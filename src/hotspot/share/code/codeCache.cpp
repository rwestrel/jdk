/*
 * Copyright (c) 1997, 2021, Oracle and/or its affiliates. All rights reserved.
 * DO NOT ALTER OR REMOVE COPYRIGHT NOTICES OR THIS FILE HEADER.
 *
 * This code is free software; you can redistribute it and/or modify it
 * under the terms of the GNU General Public License version 2 only, as
 * published by the Free Software Foundation.
 *
 * This code is distributed in the hope that it will be useful, but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
 * FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
 * version 2 for more details (a copy is included in the LICENSE file that
 * accompanied this code).
 *
 * You should have received a copy of the GNU General Public License version
 * 2 along with this work; if not, write to the Free Software Foundation,
 * Inc., 51 Franklin St, Fifth Floor, Boston, MA 02110-1301 USA.
 *
 * Please contact Oracle, 500 Oracle Parkway, Redwood Shores, CA 94065 USA
 * or visit www.oracle.com if you need additional information or have any
 * questions.
 *
 */

#include <classfile/symbolTable.hpp>
#include <classfile/systemDictionary.hpp>
#include <opto/runtime.hpp>
#include "precompiled.hpp"
#include "jvm_io.h"
#include "code/codeBlob.hpp"
#include "code/codeCache.hpp"
#include "code/codeHeapState.hpp"
#include "code/compiledIC.hpp"
#include "code/dependencies.hpp"
#include "code/dependencyContext.hpp"
#include "code/icBuffer.hpp"
#include "code/nmethod.hpp"
#include "code/pcDesc.hpp"
#include "compiler/compilationPolicy.hpp"
#include "compiler/compileBroker.hpp"
#include "compiler/oopMap.hpp"
#include "gc/shared/collectedHeap.hpp"
#include "jfr/jfrEvents.hpp"
#include "logging/log.hpp"
#include "logging/logStream.hpp"
#include "memory/allocation.inline.hpp"
#include "memory/iterator.hpp"
#include "memory/resourceArea.hpp"
#include "memory/universe.hpp"
#include "oops/method.inline.hpp"
#include "oops/objArrayOop.hpp"
#include "oops/oop.inline.hpp"
#include "oops/verifyOopClosure.hpp"
#include "runtime/arguments.hpp"
#include "runtime/atomic.hpp"
#include "runtime/deoptimization.hpp"
#include "runtime/globals_extension.hpp"
#include "runtime/handles.inline.hpp"
#include "runtime/icache.hpp"
#include "runtime/java.hpp"
#include "runtime/mutexLocker.hpp"
#include "runtime/safepointVerifiers.hpp"
#include "runtime/sweeper.hpp"
#include "runtime/vmThread.hpp"
#include "services/memoryService.hpp"
#include "utilities/align.hpp"
#include "utilities/vmError.hpp"
#include "utilities/xmlstream.hpp"
#ifdef COMPILER1
#include "c1/c1_Compilation.hpp"
#include "c1/c1_Compiler.hpp"
#endif
#ifdef COMPILER2
#include "opto/c2compiler.hpp"
#include "opto/compile.hpp"
#include "opto/node.hpp"
#include "vtableStubs.hpp"

#endif

// Helper class for printing in CodeCache
class CodeBlob_sizes {
 private:
  int count;
  int total_size;
  int header_size;
  int code_size;
  int stub_size;
  int relocation_size;
  int scopes_oop_size;
  int scopes_metadata_size;
  int scopes_data_size;
  int scopes_pcs_size;

 public:
  CodeBlob_sizes() {
    count            = 0;
    total_size       = 0;
    header_size      = 0;
    code_size        = 0;
    stub_size        = 0;
    relocation_size  = 0;
    scopes_oop_size  = 0;
    scopes_metadata_size  = 0;
    scopes_data_size = 0;
    scopes_pcs_size  = 0;
  }

  int total()                                    { return total_size; }
  bool is_empty()                                { return count == 0; }

  void print(const char* title) {
    tty->print_cr(" #%d %s = %dK (hdr %d%%,  loc %d%%, code %d%%, stub %d%%, [oops %d%%, metadata %d%%, data %d%%, pcs %d%%])",
                  count,
                  title,
                  (int)(total() / K),
                  header_size             * 100 / total_size,
                  relocation_size         * 100 / total_size,
                  code_size               * 100 / total_size,
                  stub_size               * 100 / total_size,
                  scopes_oop_size         * 100 / total_size,
                  scopes_metadata_size    * 100 / total_size,
                  scopes_data_size        * 100 / total_size,
                  scopes_pcs_size         * 100 / total_size);
  }

  void add(CodeBlob* cb) {
    count++;
    total_size       += cb->size();
    header_size      += cb->header_size();
    relocation_size  += cb->relocation_size();
    if (cb->is_nmethod()) {
      nmethod* nm = cb->as_nmethod_or_null();
      code_size        += nm->insts_size();
      stub_size        += nm->stub_size();

      scopes_oop_size  += nm->oops_size();
      scopes_metadata_size  += nm->metadata_size();
      scopes_data_size += nm->scopes_data_size();
      scopes_pcs_size  += nm->scopes_pcs_size();
    } else {
      code_size        += cb->code_size();
    }
  }
};

// Iterate over all CodeHeaps
#define FOR_ALL_HEAPS(heap) for (GrowableArrayIterator<CodeHeap*> heap = _heaps->begin(); heap != _heaps->end(); ++heap)
#define FOR_ALL_NMETHOD_HEAPS(heap) for (GrowableArrayIterator<CodeHeap*> heap = _nmethod_heaps->begin(); heap != _nmethod_heaps->end(); ++heap)
#define FOR_ALL_ALLOCABLE_HEAPS(heap) for (GrowableArrayIterator<CodeHeap*> heap = _allocable_heaps->begin(); heap != _allocable_heaps->end(); ++heap)

// Iterate over all CodeBlobs (cb) on the given CodeHeap
#define FOR_ALL_BLOBS(cb, heap) for (CodeBlob* cb = first_blob(heap); cb != NULL; cb = next_blob(heap, cb))

address CodeCache::_low_bound = 0;
address CodeCache::_high_bound = 0;
int CodeCache::_number_of_nmethods_with_dependencies = 0;
ExceptionCache* volatile CodeCache::_exception_cache_purge_list = NULL;

// Initialize arrays of CodeHeap subsets
GrowableArray<CodeHeap*>* CodeCache::_heaps = new(ResourceObj::C_HEAP, mtCode) GrowableArray<CodeHeap*> (CodeBlobType::All, mtCode);
GrowableArray<CodeHeap*>* CodeCache::_compiled_heaps = new(ResourceObj::C_HEAP, mtCode) GrowableArray<CodeHeap*> (CodeBlobType::All, mtCode);
GrowableArray<CodeHeap*>* CodeCache::_nmethod_heaps = new(ResourceObj::C_HEAP, mtCode) GrowableArray<CodeHeap*> (CodeBlobType::All, mtCode);
GrowableArray<CodeHeap*>* CodeCache::_allocable_heaps = new(ResourceObj::C_HEAP, mtCode) GrowableArray<CodeHeap*> (CodeBlobType::All, mtCode);

void CodeCache::check_heap_sizes(size_t non_nmethod_size, size_t profiled_size, size_t non_profiled_size, size_t cache_size, bool all_set) {
  size_t total_size = non_nmethod_size + profiled_size + non_profiled_size;
  // Prepare error message
  const char* error = "Invalid code heap sizes";
  err_msg message("NonNMethodCodeHeapSize (" SIZE_FORMAT "K) + ProfiledCodeHeapSize (" SIZE_FORMAT "K)"
                  " + NonProfiledCodeHeapSize (" SIZE_FORMAT "K) = " SIZE_FORMAT "K",
          non_nmethod_size/K, profiled_size/K, non_profiled_size/K, total_size/K);

  if (total_size > cache_size) {
    // Some code heap sizes were explicitly set: total_size must be <= cache_size
    message.append(" is greater than ReservedCodeCacheSize (" SIZE_FORMAT "K).", cache_size/K);
    vm_exit_during_initialization(error, message);
  } else if (all_set && total_size != cache_size) {
    // All code heap sizes were explicitly set: total_size must equal cache_size
    message.append(" is not equal to ReservedCodeCacheSize (" SIZE_FORMAT "K).", cache_size/K);
    vm_exit_during_initialization(error, message);
  }
}

void CodeCache::initialize_heaps() {
  bool non_nmethod_set      = FLAG_IS_CMDLINE(NonNMethodCodeHeapSize);
  bool profiled_set         = FLAG_IS_CMDLINE(ProfiledCodeHeapSize);
  bool non_profiled_set     = FLAG_IS_CMDLINE(NonProfiledCodeHeapSize);
  size_t min_size           = os::vm_page_size();
  size_t cache_size         = ReservedCodeCacheSize;
  size_t non_nmethod_size   = NonNMethodCodeHeapSize;
  size_t profiled_size      = ProfiledCodeHeapSize;
  size_t non_profiled_size  = NonProfiledCodeHeapSize;
  // Check if total size set via command line flags exceeds the reserved size
  check_heap_sizes((non_nmethod_set  ? non_nmethod_size  : min_size),
                   (profiled_set     ? profiled_size     : min_size),
                   (non_profiled_set ? non_profiled_size : min_size),
                   cache_size,
                   non_nmethod_set && profiled_set && non_profiled_set);

  // Determine size of compiler buffers
  size_t code_buffers_size = 0;
#ifdef COMPILER1
  // C1 temporary code buffers (see Compiler::init_buffer_blob())
  const int c1_count = CompilationPolicy::c1_count();
  code_buffers_size += c1_count * Compiler::code_buffer_size();
#endif
#ifdef COMPILER2
  // C2 scratch buffers (see Compile::init_scratch_buffer_blob())
  const int c2_count = CompilationPolicy::c2_count();
  // Initial size of constant table (this may be increased if a compiled method needs more space)
  code_buffers_size += c2_count * C2Compiler::initial_code_buffer_size();
#endif

  // Increase default non_nmethod_size to account for compiler buffers
  if (!non_nmethod_set) {
    non_nmethod_size += code_buffers_size;
  }
  // Calculate default CodeHeap sizes if not set by user
  if (!non_nmethod_set && !profiled_set && !non_profiled_set) {
    // Check if we have enough space for the non-nmethod code heap
    if (cache_size > non_nmethod_size) {
      // Use the default value for non_nmethod_size and one half of the
      // remaining size for non-profiled and one half for profiled methods
      size_t remaining_size = cache_size - non_nmethod_size;
      profiled_size = remaining_size / 2;
      non_profiled_size = remaining_size - profiled_size;
    } else {
      // Use all space for the non-nmethod heap and set other heaps to minimal size
      non_nmethod_size = cache_size - 2 * min_size;
      profiled_size = min_size;
      non_profiled_size = min_size;
    }
  } else if (!non_nmethod_set || !profiled_set || !non_profiled_set) {
    // The user explicitly set some code heap sizes. Increase or decrease the (default)
    // sizes of the other code heaps accordingly. First adapt non-profiled and profiled
    // code heap sizes and then only change non-nmethod code heap size if still necessary.
    intx diff_size = cache_size - (non_nmethod_size + profiled_size + non_profiled_size);
    if (non_profiled_set) {
      if (!profiled_set) {
        // Adapt size of profiled code heap
        if (diff_size < 0 && ((intx)profiled_size + diff_size) <= 0) {
          // Not enough space available, set to minimum size
          diff_size += profiled_size - min_size;
          profiled_size = min_size;
        } else {
          profiled_size += diff_size;
          diff_size = 0;
        }
      }
    } else if (profiled_set) {
      // Adapt size of non-profiled code heap
      if (diff_size < 0 && ((intx)non_profiled_size + diff_size) <= 0) {
        // Not enough space available, set to minimum size
        diff_size += non_profiled_size - min_size;
        non_profiled_size = min_size;
      } else {
        non_profiled_size += diff_size;
        diff_size = 0;
      }
    } else if (non_nmethod_set) {
      // Distribute remaining size between profiled and non-profiled code heaps
      diff_size = cache_size - non_nmethod_size;
      profiled_size = diff_size / 2;
      non_profiled_size = diff_size - profiled_size;
      diff_size = 0;
    }
    if (diff_size != 0) {
      // Use non-nmethod code heap for remaining space requirements
      assert(!non_nmethod_set && ((intx)non_nmethod_size + diff_size) > 0, "sanity");
      non_nmethod_size += diff_size;
    }
  }

  // We do not need the profiled CodeHeap, use all space for the non-profiled CodeHeap
  if (!heap_available(CodeBlobType::MethodProfiled)) {
    non_profiled_size += profiled_size;
    profiled_size = 0;
  }
  // We do not need the non-profiled CodeHeap, use all space for the non-nmethod CodeHeap
  if (!heap_available(CodeBlobType::MethodNonProfiled)) {
    non_nmethod_size += non_profiled_size;
    non_profiled_size = 0;
  }
  // Make sure we have enough space for VM internal code
  uint min_code_cache_size = CodeCacheMinimumUseSpace DEBUG_ONLY(* 3);
  if (non_nmethod_size < min_code_cache_size) {
    vm_exit_during_initialization(err_msg(
        "Not enough space in non-nmethod code heap to run VM: " SIZE_FORMAT "K < " SIZE_FORMAT "K",
        non_nmethod_size/K, min_code_cache_size/K));
  }

  // Verify sizes and update flag values
  assert(non_profiled_size + profiled_size + non_nmethod_size == cache_size, "Invalid code heap sizes");
  FLAG_SET_ERGO(NonNMethodCodeHeapSize, non_nmethod_size);
  FLAG_SET_ERGO(ProfiledCodeHeapSize, profiled_size);
  FLAG_SET_ERGO(NonProfiledCodeHeapSize, non_profiled_size);

  // If large page support is enabled, align code heaps according to large
  // page size to make sure that code cache is covered by large pages.
  const size_t alignment = MAX2(page_size(false, 8), (size_t) os::vm_allocation_granularity());
  non_nmethod_size = align_up(non_nmethod_size, alignment);
  profiled_size    = align_down(profiled_size, alignment);

  // Reserve one continuous chunk of memory for CodeHeaps and split it into
  // parts for the individual heaps. The memory layout looks like this:
  // ---------- high -----------
  //    Non-profiled nmethods
  //      Profiled nmethods
  //         Non-nmethods
  // ---------- low ------------
  ReservedCodeSpace rs = reserve_heap_memory(cache_size);
  ReservedSpace non_method_space    = rs.first_part(non_nmethod_size);
  ReservedSpace rest                = rs.last_part(non_nmethod_size);
  ReservedSpace profiled_space      = rest.first_part(profiled_size);
  ReservedSpace non_profiled_space  = rest.last_part(profiled_size);

  // Non-nmethods (stubs, adapters, ...)
  add_heap(non_method_space, "CodeHeap 'non-nmethods'", CodeBlobType::NonNMethod);
  // Tier 2 and tier 3 (profiled) methods
  add_heap(profiled_space, "CodeHeap 'profiled nmethods'", CodeBlobType::MethodProfiled);
  // Tier 1 and tier 4 (non-profiled) methods and native methods
  add_heap(non_profiled_space, "CodeHeap 'non-profiled nmethods'", CodeBlobType::MethodNonProfiled);
}

size_t CodeCache::page_size(bool aligned, size_t min_pages) {
  if (os::can_execute_large_page_memory()) {
    if (InitialCodeCacheSize < ReservedCodeCacheSize) {
      // Make sure that the page size allows for an incremental commit of the reserved space
      min_pages = MAX2(min_pages, (size_t)8);
    }
    return aligned ? os::page_size_for_region_aligned(ReservedCodeCacheSize, min_pages) :
                     os::page_size_for_region_unaligned(ReservedCodeCacheSize, min_pages);
  } else {
    return os::vm_page_size();
  }
}

ReservedCodeSpace CodeCache::reserve_heap_memory(size_t size) {
  // Align and reserve space for code cache
  const size_t rs_ps = page_size();
  const size_t rs_align = MAX2(rs_ps, (size_t) os::vm_allocation_granularity());
  const size_t rs_size = align_up(size, rs_align);
  ReservedCodeSpace rs(rs_size, rs_align, rs_ps);
  if (!rs.is_reserved()) {
    vm_exit_during_initialization(err_msg("Could not reserve enough space for code cache (" SIZE_FORMAT "K)",
                                          rs_size/K));
  }

  // Initialize bounds
  _low_bound = (address)rs.base();
  _high_bound = _low_bound + rs.size();
  return rs;
}

// Heaps available for allocation
bool CodeCache::heap_available(int code_blob_type) {
  if (!SegmentedCodeCache) {
    // No segmentation: use a single code heap
    return (code_blob_type == CodeBlobType::All);
  } else if (Arguments::is_interpreter_only()) {
    // Interpreter only: we don't need any method code heaps
    return (code_blob_type == CodeBlobType::NonNMethod);
  } else if (CompilerConfig::is_c1_profiling()) {
    // Tiered compilation: use all code heaps
    return (code_blob_type < CodeBlobType::All);
  } else {
    // No TieredCompilation: we only need the non-nmethod and non-profiled code heap
    return (code_blob_type == CodeBlobType::NonNMethod) ||
           (code_blob_type == CodeBlobType::MethodNonProfiled);
  }
}

const char* CodeCache::get_code_heap_flag_name(int code_blob_type) {
  switch(code_blob_type) {
  case CodeBlobType::NonNMethod:
    return "NonNMethodCodeHeapSize";
    break;
  case CodeBlobType::MethodNonProfiled:
    return "NonProfiledCodeHeapSize";
    break;
  case CodeBlobType::MethodProfiled:
    return "ProfiledCodeHeapSize";
    break;
  }
  ShouldNotReachHere();
  return NULL;
}

int CodeCache::code_heap_compare(CodeHeap* const &lhs, CodeHeap* const &rhs) {
  if (lhs->code_blob_type() == rhs->code_blob_type()) {
    return (lhs > rhs) ? 1 : ((lhs < rhs) ? -1 : 0);
  } else {
    return lhs->code_blob_type() - rhs->code_blob_type();
  }
}

void CodeCache::add_heap(CodeHeap* heap) {
  assert(!Universe::is_fully_initialized(), "late heap addition?");

  _heaps->insert_sorted<code_heap_compare>(heap);

  int type = heap->code_blob_type();
  if (code_blob_type_accepts_compiled(type)) {
    _compiled_heaps->insert_sorted<code_heap_compare>(heap);
  }
  if (code_blob_type_accepts_nmethod(type)) {
    _nmethod_heaps->insert_sorted<code_heap_compare>(heap);
  }
  if (code_blob_type_accepts_allocable(type)) {
    _allocable_heaps->insert_sorted<code_heap_compare>(heap);
  }
}

void CodeCache::add_heap(ReservedSpace rs, const char* name, int code_blob_type) {
  // Check if heap is needed
  if (!heap_available(code_blob_type)) {
    return;
  }

  // Create CodeHeap
  CodeHeap* heap = new CodeHeap(name, code_blob_type);
  add_heap(heap);

  // Reserve Space
  size_t size_initial = MIN2((size_t)InitialCodeCacheSize, rs.size());
  size_initial = align_up(size_initial, os::vm_page_size());
  if (!heap->reserve(rs, size_initial, CodeCacheSegmentSize)) {
    vm_exit_during_initialization(err_msg("Could not reserve enough space in %s (" SIZE_FORMAT "K)",
                                          heap->name(), size_initial/K));
  }

  // Register the CodeHeap
  MemoryService::add_code_heap_memory_pool(heap, name);
}

CodeHeap* CodeCache::get_code_heap_containing(void* start) {
  FOR_ALL_HEAPS(heap) {
    if ((*heap)->contains(start)) {
      return *heap;
    }
  }
  return NULL;
}

CodeHeap* CodeCache::get_code_heap(const CodeBlob* cb) {
  assert(cb != NULL, "CodeBlob is null");
  FOR_ALL_HEAPS(heap) {
    if ((*heap)->contains_blob(cb)) {
      return *heap;
    }
  }
  ShouldNotReachHere();
  return NULL;
}

CodeHeap* CodeCache::get_code_heap(int code_blob_type) {
  FOR_ALL_HEAPS(heap) {
    if ((*heap)->accepts(code_blob_type)) {
      return *heap;
    }
  }
  return NULL;
}

CodeBlob* CodeCache::first_blob(CodeHeap* heap) {
  assert_locked_or_safepoint(CodeCache_lock);
  assert(heap != NULL, "heap is null");
  return (CodeBlob*)heap->first();
}

CodeBlob* CodeCache::first_blob(int code_blob_type) {
  if (heap_available(code_blob_type)) {
    return first_blob(get_code_heap(code_blob_type));
  } else {
    return NULL;
  }
}

CodeBlob* CodeCache::next_blob(CodeHeap* heap, CodeBlob* cb) {
  assert_locked_or_safepoint(CodeCache_lock);
  assert(heap != NULL, "heap is null");
  return (CodeBlob*)heap->next(cb);
}

/**
 * Do not seize the CodeCache lock here--if the caller has not
 * already done so, we are going to lose bigtime, since the code
 * cache will contain a garbage CodeBlob until the caller can
 * run the constructor for the CodeBlob subclass he is busy
 * instantiating.
 */
CodeBlob* CodeCache::allocate(int size, int code_blob_type, bool handle_alloc_failure, int orig_code_blob_type) {
  // Possibly wakes up the sweeper thread.
  NMethodSweeper::report_allocation(code_blob_type);
  assert_locked_or_safepoint(CodeCache_lock);
  assert(size > 0, "Code cache allocation request must be > 0 but is %d", size);
  if (size <= 0) {
    return NULL;
  }
  CodeBlob* cb = NULL;

  // Get CodeHeap for the given CodeBlobType
  CodeHeap* heap = get_code_heap(code_blob_type);
  assert(heap != NULL, "heap is null");

  while (true) {
    cb = (CodeBlob*)heap->allocate(size);
    if (cb != NULL) break;
    if (!heap->expand_by(CodeCacheExpansionSize)) {
      // Save original type for error reporting
      if (orig_code_blob_type == CodeBlobType::All) {
        orig_code_blob_type = code_blob_type;
      }
      // Expansion failed
      if (SegmentedCodeCache) {
        // Fallback solution: Try to store code in another code heap.
        // NonNMethod -> MethodNonProfiled -> MethodProfiled (-> MethodNonProfiled)
        // Note that in the sweeper, we check the reverse_free_ratio of the code heap
        // and force stack scanning if less than 10% of the code heap are free.
        int type = code_blob_type;
        switch (type) {
        case CodeBlobType::NonNMethod:
          type = CodeBlobType::MethodNonProfiled;
          break;
        case CodeBlobType::MethodNonProfiled:
          type = CodeBlobType::MethodProfiled;
          break;
        case CodeBlobType::MethodProfiled:
          // Avoid loop if we already tried that code heap
          if (type == orig_code_blob_type) {
            type = CodeBlobType::MethodNonProfiled;
          }
          break;
        }
        if (type != code_blob_type && type != orig_code_blob_type && heap_available(type)) {
          if (PrintCodeCacheExtension) {
            tty->print_cr("Extension of %s failed. Trying to allocate in %s.",
                          heap->name(), get_code_heap(type)->name());
          }
          return allocate(size, type, handle_alloc_failure, orig_code_blob_type);
        }
      }
      if (handle_alloc_failure) {
        MutexUnlocker mu(CodeCache_lock, Mutex::_no_safepoint_check_flag);
        CompileBroker::handle_full_code_cache(orig_code_blob_type);
      }
      return NULL;
    }
    if (PrintCodeCacheExtension) {
      ResourceMark rm;
      if (_nmethod_heaps->length() >= 1) {
        tty->print("%s", heap->name());
      } else {
        tty->print("CodeCache");
      }
      tty->print_cr(" extended to [" INTPTR_FORMAT ", " INTPTR_FORMAT "] (" SSIZE_FORMAT " bytes)",
                    (intptr_t)heap->low_boundary(), (intptr_t)heap->high(),
                    (address)heap->high() - (address)heap->low_boundary());
    }
  }
  print_trace("allocation", cb, size);
  return cb;
}

void CodeCache::free(CodeBlob* cb) {
  assert_locked_or_safepoint(CodeCache_lock);
  CodeHeap* heap = get_code_heap(cb);
  print_trace("free", cb);
  if (cb->is_nmethod()) {
    nmethod* ptr = (nmethod *)cb;
    heap->set_nmethod_count(heap->nmethod_count() - 1);
    if (ptr->has_dependencies()) {
      _number_of_nmethods_with_dependencies--;
    }
    ptr->free_native_invokers();
  }
  if (cb->is_adapter_blob()) {
    heap->set_adapter_count(heap->adapter_count() - 1);
  }

  // Get heap for given CodeBlob and deallocate
  get_code_heap(cb)->deallocate(cb);

  assert(heap->blob_count() >= 0, "sanity check");
}

void CodeCache::free_unused_tail(CodeBlob* cb, size_t used) {
  assert_locked_or_safepoint(CodeCache_lock);
  guarantee(cb->is_buffer_blob() && strncmp("Interpreter", cb->name(), 11) == 0, "Only possible for interpreter!");
  print_trace("free_unused_tail", cb);

  // We also have to account for the extra space (i.e. header) used by the CodeBlob
  // which provides the memory (see BufferBlob::create() in codeBlob.cpp).
  used += CodeBlob::align_code_offset(cb->header_size());

  // Get heap for given CodeBlob and deallocate its unused tail
  get_code_heap(cb)->deallocate_tail(cb, used);
  // Adjust the sizes of the CodeBlob
  cb->adjust_size(used);
}

void CodeCache::commit(CodeBlob* cb) {
  // this is called by nmethod::nmethod, which must already own CodeCache_lock
  assert_locked_or_safepoint(CodeCache_lock);
  CodeHeap* heap = get_code_heap(cb);
  if (cb->is_nmethod()) {
    heap->set_nmethod_count(heap->nmethod_count() + 1);
    if (((nmethod *)cb)->has_dependencies()) {
      _number_of_nmethods_with_dependencies++;
    }
  }
  if (cb->is_adapter_blob()) {
    heap->set_adapter_count(heap->adapter_count() + 1);
  }

  // flush the hardware I-cache
  ICache::invalidate_range(cb->content_begin(), cb->content_size());
}

bool CodeCache::contains(void *p) {
  // S390 uses contains() in current_frame(), which is used before
  // code cache initialization if NativeMemoryTracking=detail is set.
  S390_ONLY(if (_heaps == NULL) return false;)
  // It should be ok to call contains without holding a lock.
  FOR_ALL_HEAPS(heap) {
    if ((*heap)->contains(p)) {
      return true;
    }
  }
  return false;
}

bool CodeCache::contains(nmethod *nm) {
  return contains((void *)nm);
}

// This method is safe to call without holding the CodeCache_lock, as long as a dead CodeBlob is not
// looked up (i.e., one that has been marked for deletion). It only depends on the _segmap to contain
// valid indices, which it will always do, as long as the CodeBlob is not in the process of being recycled.
CodeBlob* CodeCache::find_blob(void* start) {
  CodeBlob* result = find_blob_unsafe(start);
  // We could potentially look up non_entrant methods
  guarantee(result == NULL || !result->is_zombie() || result->is_locked_by_vm() || VMError::is_error_reported(), "unsafe access to zombie method");
  return result;
}

// Lookup that does not fail if you lookup a zombie method (if you call this, be sure to know
// what you are doing)
CodeBlob* CodeCache::find_blob_unsafe(void* start) {
  // NMT can walk the stack before code cache is created
  if (_heaps != NULL) {
    CodeHeap* heap = get_code_heap_containing(start);
    if (heap != NULL) {
      return heap->find_blob_unsafe(start);
    }
  }
  return NULL;
}

nmethod* CodeCache::find_nmethod(void* start) {
  CodeBlob* cb = find_blob(start);
  assert(cb->is_nmethod(), "did not find an nmethod");
  return (nmethod*)cb;
}

void CodeCache::blobs_do(void f(CodeBlob* nm)) {
  assert_locked_or_safepoint(CodeCache_lock);
  FOR_ALL_HEAPS(heap) {
    FOR_ALL_BLOBS(cb, *heap) {
      f(cb);
    }
  }
}

void CodeCache::nmethods_do(void f(nmethod* nm)) {
  assert_locked_or_safepoint(CodeCache_lock);
  NMethodIterator iter(NMethodIterator::all_blobs);
  while(iter.next()) {
    f(iter.method());
  }
}

void CodeCache::metadata_do(MetadataClosure* f) {
  assert_locked_or_safepoint(CodeCache_lock);
  NMethodIterator iter(NMethodIterator::only_alive_and_not_unloading);
  while(iter.next()) {
    iter.method()->metadata_do(f);
  }
}

int CodeCache::alignment_unit() {
  return (int)_heaps->first()->alignment_unit();
}

int CodeCache::alignment_offset() {
  return (int)_heaps->first()->alignment_offset();
}

// Mark nmethods for unloading if they contain otherwise unreachable oops.
void CodeCache::do_unloading(BoolObjectClosure* is_alive, bool unloading_occurred) {
  assert_locked_or_safepoint(CodeCache_lock);
  UnloadingScope scope(is_alive);
  CompiledMethodIterator iter(CompiledMethodIterator::only_alive);
  while(iter.next()) {
    iter.method()->do_unloading(unloading_occurred);
  }
}

void CodeCache::blobs_do(CodeBlobClosure* f) {
  assert_locked_or_safepoint(CodeCache_lock);
  FOR_ALL_ALLOCABLE_HEAPS(heap) {
    FOR_ALL_BLOBS(cb, *heap) {
      if (cb->is_alive()) {
        f->do_code_blob(cb);
#ifdef ASSERT
        if (cb->is_nmethod()) {
          Universe::heap()->verify_nmethod((nmethod*)cb);
        }
#endif //ASSERT
      }
    }
  }
}

void CodeCache::verify_clean_inline_caches() {
#ifdef ASSERT
  NMethodIterator iter(NMethodIterator::only_alive_and_not_unloading);
  while(iter.next()) {
    nmethod* nm = iter.method();
    assert(!nm->is_unloaded(), "Tautology");
    nm->verify_clean_inline_caches();
    nm->verify();
  }
#endif
}

void CodeCache::verify_icholder_relocations() {
#ifdef ASSERT
  // make sure that we aren't leaking icholders
  int count = 0;
  FOR_ALL_HEAPS(heap) {
    FOR_ALL_BLOBS(cb, *heap) {
      CompiledMethod *nm = cb->as_compiled_method_or_null();
      if (nm != NULL) {
        count += nm->verify_icholder_relocations();
      }
    }
  }
  assert(count + InlineCacheBuffer::pending_icholder_count() + CompiledICHolder::live_not_claimed_count() ==
         CompiledICHolder::live_count(), "must agree");
#endif
}

// Defer freeing of concurrently cleaned ExceptionCache entries until
// after a global handshake operation.
void CodeCache::release_exception_cache(ExceptionCache* entry) {
  if (SafepointSynchronize::is_at_safepoint()) {
    delete entry;
  } else {
    for (;;) {
      ExceptionCache* purge_list_head = Atomic::load(&_exception_cache_purge_list);
      entry->set_purge_list_next(purge_list_head);
      if (Atomic::cmpxchg(&_exception_cache_purge_list, purge_list_head, entry) == purge_list_head) {
        break;
      }
    }
  }
}

// Delete exception caches that have been concurrently unlinked,
// followed by a global handshake operation.
void CodeCache::purge_exception_caches() {
  ExceptionCache* curr = _exception_cache_purge_list;
  while (curr != NULL) {
    ExceptionCache* next = curr->purge_list_next();
    delete curr;
    curr = next;
  }
  _exception_cache_purge_list = NULL;
}

uint8_t CodeCache::_unloading_cycle = 1;

void CodeCache::increment_unloading_cycle() {
  // 2-bit value (see IsUnloadingState in nmethod.cpp for details)
  // 0 is reserved for new methods.
  _unloading_cycle = (_unloading_cycle + 1) % 4;
  if (_unloading_cycle == 0) {
    _unloading_cycle = 1;
  }
}

CodeCache::UnloadingScope::UnloadingScope(BoolObjectClosure* is_alive)
  : _is_unloading_behaviour(is_alive)
{
  _saved_behaviour = IsUnloadingBehaviour::current();
  IsUnloadingBehaviour::set_current(&_is_unloading_behaviour);
  increment_unloading_cycle();
  DependencyContext::cleaning_start();
}

CodeCache::UnloadingScope::~UnloadingScope() {
  IsUnloadingBehaviour::set_current(_saved_behaviour);
  DependencyContext::cleaning_end();
}

void CodeCache::verify_oops() {
  MutexLocker mu(CodeCache_lock, Mutex::_no_safepoint_check_flag);
  VerifyOopClosure voc;
  NMethodIterator iter(NMethodIterator::only_alive_and_not_unloading);
  while(iter.next()) {
    nmethod* nm = iter.method();
    nm->oops_do(&voc);
    nm->verify_oop_relocations();
  }
}

int CodeCache::blob_count(int code_blob_type) {
  CodeHeap* heap = get_code_heap(code_blob_type);
  return (heap != NULL) ? heap->blob_count() : 0;
}

int CodeCache::blob_count() {
  int count = 0;
  FOR_ALL_HEAPS(heap) {
    count += (*heap)->blob_count();
  }
  return count;
}

int CodeCache::nmethod_count(int code_blob_type) {
  CodeHeap* heap = get_code_heap(code_blob_type);
  return (heap != NULL) ? heap->nmethod_count() : 0;
}

int CodeCache::nmethod_count() {
  int count = 0;
  FOR_ALL_NMETHOD_HEAPS(heap) {
    count += (*heap)->nmethod_count();
  }
  return count;
}

int CodeCache::adapter_count(int code_blob_type) {
  CodeHeap* heap = get_code_heap(code_blob_type);
  return (heap != NULL) ? heap->adapter_count() : 0;
}

int CodeCache::adapter_count() {
  int count = 0;
  FOR_ALL_HEAPS(heap) {
    count += (*heap)->adapter_count();
  }
  return count;
}

address CodeCache::low_bound(int code_blob_type) {
  CodeHeap* heap = get_code_heap(code_blob_type);
  return (heap != NULL) ? (address)heap->low_boundary() : NULL;
}

address CodeCache::high_bound(int code_blob_type) {
  CodeHeap* heap = get_code_heap(code_blob_type);
  return (heap != NULL) ? (address)heap->high_boundary() : NULL;
}

size_t CodeCache::capacity() {
  size_t cap = 0;
  FOR_ALL_ALLOCABLE_HEAPS(heap) {
    cap += (*heap)->capacity();
  }
  return cap;
}

size_t CodeCache::unallocated_capacity(int code_blob_type) {
  CodeHeap* heap = get_code_heap(code_blob_type);
  return (heap != NULL) ? heap->unallocated_capacity() : 0;
}

size_t CodeCache::unallocated_capacity() {
  size_t unallocated_cap = 0;
  FOR_ALL_ALLOCABLE_HEAPS(heap) {
    unallocated_cap += (*heap)->unallocated_capacity();
  }
  return unallocated_cap;
}

size_t CodeCache::max_capacity() {
  size_t max_cap = 0;
  FOR_ALL_ALLOCABLE_HEAPS(heap) {
    max_cap += (*heap)->max_capacity();
  }
  return max_cap;
}

/**
 * Returns the reverse free ratio. E.g., if 25% (1/4) of the code heap
 * is free, reverse_free_ratio() returns 4.
 */
double CodeCache::reverse_free_ratio(int code_blob_type) {
  CodeHeap* heap = get_code_heap(code_blob_type);
  if (heap == NULL) {
    return 0;
  }

  double unallocated_capacity = MAX2((double)heap->unallocated_capacity(), 1.0); // Avoid division by 0;
  double max_capacity = (double)heap->max_capacity();
  double result = max_capacity / unallocated_capacity;
  assert (max_capacity >= unallocated_capacity, "Must be");
  assert (result >= 1.0, "reverse_free_ratio must be at least 1. It is %f", result);
  return result;
}

size_t CodeCache::bytes_allocated_in_freelists() {
  size_t allocated_bytes = 0;
  FOR_ALL_ALLOCABLE_HEAPS(heap) {
    allocated_bytes += (*heap)->allocated_in_freelist();
  }
  return allocated_bytes;
}

int CodeCache::allocated_segments() {
  int number_of_segments = 0;
  FOR_ALL_ALLOCABLE_HEAPS(heap) {
    number_of_segments += (*heap)->allocated_segments();
  }
  return number_of_segments;
}

size_t CodeCache::freelists_length() {
  size_t length = 0;
  FOR_ALL_ALLOCABLE_HEAPS(heap) {
    length += (*heap)->freelist_length();
  }
  return length;
}

void icache_init();

void CodeCache::initialize() {
  assert(CodeCacheSegmentSize >= (uintx)CodeEntryAlignment, "CodeCacheSegmentSize must be large enough to align entry points");
#ifdef COMPILER2
  assert(CodeCacheSegmentSize >= (uintx)OptoLoopAlignment,  "CodeCacheSegmentSize must be large enough to align inner loops");
#endif
  assert(CodeCacheSegmentSize >= sizeof(jdouble),    "CodeCacheSegmentSize must be large enough to align constants");
  // This was originally just a check of the alignment, causing failure, instead, round
  // the code cache to the page size.  In particular, Solaris is moving to a larger
  // default page size.
  CodeCacheExpansionSize = align_up(CodeCacheExpansionSize, os::vm_page_size());

  if (SegmentedCodeCache) {
    // Use multiple code heaps
    initialize_heaps();
  } else {
    // Use a single code heap
    FLAG_SET_ERGO(NonNMethodCodeHeapSize, 0);
    FLAG_SET_ERGO(ProfiledCodeHeapSize, 0);
    FLAG_SET_ERGO(NonProfiledCodeHeapSize, 0);
    ReservedCodeSpace rs = reserve_heap_memory(ReservedCodeCacheSize);
    add_heap(rs, "CodeCache", CodeBlobType::All);
  }

  // Initialize ICache flush mechanism
  // This service is needed for os::register_code_area
  icache_init();

  // Give OS a chance to register generated code area.
  // This is used on Windows 64 bit platforms to register
  // Structured Exception Handlers for our generated code.
  os::register_code_area((char*)low_bound(), (char*)high_bound());
}

void codeCache_init() {
  CodeCache::initialize();
}

//------------------------------------------------------------------------------------------------

int CodeCache::number_of_nmethods_with_dependencies() {
  return _number_of_nmethods_with_dependencies;
}

void CodeCache::clear_inline_caches() {
  assert_locked_or_safepoint(CodeCache_lock);
  CompiledMethodIterator iter(CompiledMethodIterator::only_alive_and_not_unloading);
  while(iter.next()) {
    iter.method()->clear_inline_caches();
  }
}

void CodeCache::cleanup_inline_caches() {
  assert_locked_or_safepoint(CodeCache_lock);
  NMethodIterator iter(NMethodIterator::only_alive_and_not_unloading);
  while(iter.next()) {
    iter.method()->cleanup_inline_caches(/*clean_all=*/true);
  }
}

// Keeps track of time spent for checking dependencies
NOT_PRODUCT(static elapsedTimer dependentCheckTime;)

int CodeCache::mark_for_deoptimization(KlassDepChange& changes) {
  MutexLocker mu(CodeCache_lock, Mutex::_no_safepoint_check_flag);
  int number_of_marked_CodeBlobs = 0;

  // search the hierarchy looking for nmethods which are affected by the loading of this class

  // then search the interfaces this class implements looking for nmethods
  // which might be dependent of the fact that an interface only had one
  // implementor.
  // nmethod::check_all_dependencies works only correctly, if no safepoint
  // can happen
  NoSafepointVerifier nsv;
  for (DepChange::ContextStream str(changes, nsv); str.next(); ) {
    Klass* d = str.klass();
    number_of_marked_CodeBlobs += InstanceKlass::cast(d)->mark_dependent_nmethods(changes);
  }

#ifndef PRODUCT
  if (VerifyDependencies) {
    // Object pointers are used as unique identifiers for dependency arguments. This
    // is only possible if no safepoint, i.e., GC occurs during the verification code.
    dependentCheckTime.start();
    nmethod::check_all_dependencies(changes);
    dependentCheckTime.stop();
  }
#endif

  return number_of_marked_CodeBlobs;
}

CompiledMethod* CodeCache::find_compiled(void* start) {
  CodeBlob *cb = find_blob(start);
  assert(cb == NULL || cb->is_compiled(), "did not find an compiled_method");
  return (CompiledMethod*)cb;
}

#if INCLUDE_JVMTI
// RedefineClasses support for unloading nmethods that are dependent on "old" methods.
// We don't really expect this table to grow very large.  If it does, it can become a hashtable.
static GrowableArray<CompiledMethod*>* old_compiled_method_table = NULL;

static void add_to_old_table(CompiledMethod* c) {
  if (old_compiled_method_table == NULL) {
    old_compiled_method_table = new (ResourceObj::C_HEAP, mtCode) GrowableArray<CompiledMethod*>(100, mtCode);
  }
  old_compiled_method_table->push(c);
}

static void reset_old_method_table() {
  if (old_compiled_method_table != NULL) {
    delete old_compiled_method_table;
    old_compiled_method_table = NULL;
  }
}

// Remove this method when zombied or unloaded.
void CodeCache::unregister_old_nmethod(CompiledMethod* c) {
  assert_lock_strong(CodeCache_lock);
  if (old_compiled_method_table != NULL) {
    int index = old_compiled_method_table->find(c);
    if (index != -1) {
      old_compiled_method_table->delete_at(index);
    }
  }
}

void CodeCache::old_nmethods_do(MetadataClosure* f) {
  // Walk old method table and mark those on stack.
  int length = 0;
  if (old_compiled_method_table != NULL) {
    length = old_compiled_method_table->length();
    for (int i = 0; i < length; i++) {
      CompiledMethod* cm = old_compiled_method_table->at(i);
      // Only walk alive nmethods, the dead ones will get removed by the sweeper or GC.
      if (cm->is_alive() && !cm->is_unloading()) {
        old_compiled_method_table->at(i)->metadata_do(f);
      }
    }
  }
  log_debug(redefine, class, nmethod)("Walked %d nmethods for mark_on_stack", length);
}

// Walk compiled methods and mark dependent methods for deoptimization.
int CodeCache::mark_dependents_for_evol_deoptimization() {
  assert(SafepointSynchronize::is_at_safepoint(), "Can only do this at a safepoint!");
  // Each redefinition creates a new set of nmethods that have references to "old" Methods
  // So delete old method table and create a new one.
  reset_old_method_table();

  int number_of_marked_CodeBlobs = 0;
  CompiledMethodIterator iter(CompiledMethodIterator::only_alive_and_not_unloading);
  while(iter.next()) {
    CompiledMethod* nm = iter.method();
    // Walk all alive nmethods to check for old Methods.
    // This includes methods whose inline caches point to old methods, so
    // inline cache clearing is unnecessary.
    if (nm->has_evol_metadata()) {
      nm->mark_for_deoptimization();
      add_to_old_table(nm);
      number_of_marked_CodeBlobs++;
    }
  }

  // return total count of nmethods marked for deoptimization, if zero the caller
  // can skip deoptimization
  return number_of_marked_CodeBlobs;
}

void CodeCache::mark_all_nmethods_for_evol_deoptimization() {
  assert(SafepointSynchronize::is_at_safepoint(), "Can only do this at a safepoint!");
  CompiledMethodIterator iter(CompiledMethodIterator::only_alive_and_not_unloading);
  while(iter.next()) {
    CompiledMethod* nm = iter.method();
    if (!nm->method()->is_method_handle_intrinsic()) {
      nm->mark_for_deoptimization();
      if (nm->has_evol_metadata()) {
        add_to_old_table(nm);
      }
    }
  }
}

// Flushes compiled methods dependent on redefined classes, that have already been
// marked for deoptimization.
void CodeCache::flush_evol_dependents() {
  assert(SafepointSynchronize::is_at_safepoint(), "Can only do this at a safepoint!");

  // CodeCache can only be updated by a thread_in_VM and they will all be
  // stopped during the safepoint so CodeCache will be safe to update without
  // holding the CodeCache_lock.

  // At least one nmethod has been marked for deoptimization

  Deoptimization::deoptimize_all_marked();
}
#endif // INCLUDE_JVMTI

// Mark methods for deopt (if safe or possible).
void CodeCache::mark_all_nmethods_for_deoptimization() {
  MutexLocker mu(CodeCache_lock, Mutex::_no_safepoint_check_flag);
  CompiledMethodIterator iter(CompiledMethodIterator::only_alive_and_not_unloading);
  while(iter.next()) {
    CompiledMethod* nm = iter.method();
    if (!nm->is_native_method()) {
      nm->mark_for_deoptimization();
    }
  }
}

int CodeCache::mark_for_deoptimization(Method* dependee) {
  MutexLocker mu(CodeCache_lock, Mutex::_no_safepoint_check_flag);
  int number_of_marked_CodeBlobs = 0;

  CompiledMethodIterator iter(CompiledMethodIterator::only_alive_and_not_unloading);
  while(iter.next()) {
    CompiledMethod* nm = iter.method();
    if (nm->is_dependent_on_method(dependee)) {
      ResourceMark rm;
      nm->mark_for_deoptimization();
      number_of_marked_CodeBlobs++;
    }
  }

  return number_of_marked_CodeBlobs;
}

void CodeCache::make_marked_nmethods_not_entrant() {
  assert_locked_or_safepoint(CodeCache_lock);
  CompiledMethodIterator iter(CompiledMethodIterator::only_alive_and_not_unloading);
  while(iter.next()) {
    CompiledMethod* nm = iter.method();
    if (nm->is_marked_for_deoptimization()) {
      nm->make_not_entrant();
    }
  }
}

// Flushes compiled methods dependent on dependee.
void CodeCache::flush_dependents_on(InstanceKlass* dependee) {
  assert_lock_strong(Compile_lock);

  if (number_of_nmethods_with_dependencies() == 0) return;

  int marked = 0;
  if (dependee->is_linked()) {
    // Class initialization state change.
    KlassInitDepChange changes(dependee);
    marked = mark_for_deoptimization(changes);
  } else {
    // New class is loaded.
    NewKlassDepChange changes(dependee);
    marked = mark_for_deoptimization(changes);
  }

  if (marked > 0) {
    // At least one nmethod has been marked for deoptimization
    Deoptimization::deoptimize_all_marked();
  }
}

// Flushes compiled methods dependent on dependee
void CodeCache::flush_dependents_on_method(const methodHandle& m_h) {
  // --- Compile_lock is not held. However we are at a safepoint.
  assert_locked_or_safepoint(Compile_lock);

  // Compute the dependent nmethods
  if (mark_for_deoptimization(m_h()) > 0) {
    Deoptimization::deoptimize_all_marked();
  }
}

void CodeCache::verify() {
  assert_locked_or_safepoint(CodeCache_lock);
  FOR_ALL_HEAPS(heap) {
    (*heap)->verify();
    FOR_ALL_BLOBS(cb, *heap) {
      if (cb->is_alive()) {
        cb->verify();
      }
    }
  }
}

// A CodeHeap is full. Print out warning and report event.
PRAGMA_DIAG_PUSH
PRAGMA_FORMAT_NONLITERAL_IGNORED
void CodeCache::report_codemem_full(int code_blob_type, bool print) {
  // Get nmethod heap for the given CodeBlobType and build CodeCacheFull event
  CodeHeap* heap = get_code_heap(code_blob_type);
  assert(heap != NULL, "heap is null");

  if ((heap->full_count() == 0) || print) {
    // Not yet reported for this heap, report
    if (SegmentedCodeCache) {
      ResourceMark rm;
      stringStream msg1_stream, msg2_stream;
      msg1_stream.print("%s is full. Compiler has been disabled.",
                        get_code_heap_name(code_blob_type));
      msg2_stream.print("Try increasing the code heap size using -XX:%s=",
                 get_code_heap_flag_name(code_blob_type));
      const char *msg1 = msg1_stream.as_string();
      const char *msg2 = msg2_stream.as_string();

      log_warning(codecache)("%s", msg1);
      log_warning(codecache)("%s", msg2);
      warning("%s", msg1);
      warning("%s", msg2);
    } else {
      const char *msg1 = "CodeCache is full. Compiler has been disabled.";
      const char *msg2 = "Try increasing the code cache size using -XX:ReservedCodeCacheSize=";

      log_warning(codecache)("%s", msg1);
      log_warning(codecache)("%s", msg2);
      warning("%s", msg1);
      warning("%s", msg2);
    }
    ResourceMark rm;
    stringStream s;
    // Dump code cache into a buffer before locking the tty.
    {
      MutexLocker mu(CodeCache_lock, Mutex::_no_safepoint_check_flag);
      print_summary(&s);
    }
    {
      ttyLocker ttyl;
      tty->print("%s", s.as_string());
    }

    if (heap->full_count() == 0) {
      if (PrintCodeHeapAnalytics) {
        CompileBroker::print_heapinfo(tty, "all", 4096); // details, may be a lot!
      }
    }
  }

  heap->report_full();

  EventCodeCacheFull event;
  if (event.should_commit()) {
    event.set_codeBlobType((u1)code_blob_type);
    event.set_startAddress((u8)heap->low_boundary());
    event.set_commitedTopAddress((u8)heap->high());
    event.set_reservedTopAddress((u8)heap->high_boundary());
    event.set_entryCount(heap->blob_count());
    event.set_methodCount(heap->nmethod_count());
    event.set_adaptorCount(heap->adapter_count());
    event.set_unallocatedCapacity(heap->unallocated_capacity());
    event.set_fullCount(heap->full_count());
    event.commit();
  }
}
PRAGMA_DIAG_POP

void CodeCache::print_memory_overhead() {
  size_t wasted_bytes = 0;
  FOR_ALL_ALLOCABLE_HEAPS(heap) {
      CodeHeap* curr_heap = *heap;
      for (CodeBlob* cb = (CodeBlob*)curr_heap->first(); cb != NULL; cb = (CodeBlob*)curr_heap->next(cb)) {
        HeapBlock* heap_block = ((HeapBlock*)cb) - 1;
        wasted_bytes += heap_block->length() * CodeCacheSegmentSize - cb->size();
      }
  }
  // Print bytes that are allocated in the freelist
  ttyLocker ttl;
  tty->print_cr("Number of elements in freelist: " SSIZE_FORMAT,       freelists_length());
  tty->print_cr("Allocated in freelist:          " SSIZE_FORMAT "kB",  bytes_allocated_in_freelists()/K);
  tty->print_cr("Unused bytes in CodeBlobs:      " SSIZE_FORMAT "kB",  (wasted_bytes/K));
  tty->print_cr("Segment map size:               " SSIZE_FORMAT "kB",  allocated_segments()/K); // 1 byte per segment
}

//------------------------------------------------------------------------------------------------
// Non-product version

#ifndef PRODUCT

void CodeCache::print_trace(const char* event, CodeBlob* cb, int size) {
  if (PrintCodeCache2) {  // Need to add a new flag
    ResourceMark rm;
    if (size == 0)  size = cb->size();
    tty->print_cr("CodeCache %s:  addr: " INTPTR_FORMAT ", size: 0x%x", event, p2i(cb), size);
  }
}

void CodeCache::print_internals() {
  int nmethodCount = 0;
  int runtimeStubCount = 0;
  int adapterCount = 0;
  int deoptimizationStubCount = 0;
  int uncommonTrapStubCount = 0;
  int bufferBlobCount = 0;
  int total = 0;
  int nmethodAlive = 0;
  int nmethodNotEntrant = 0;
  int nmethodZombie = 0;
  int nmethodUnloaded = 0;
  int nmethodJava = 0;
  int nmethodNative = 0;
  int max_nm_size = 0;
  ResourceMark rm;

  int i = 0;
  FOR_ALL_ALLOCABLE_HEAPS(heap) {
    if ((_nmethod_heaps->length() >= 1) && Verbose) {
      tty->print_cr("-- %s --", (*heap)->name());
    }
    FOR_ALL_BLOBS(cb, *heap) {
      total++;
      if (cb->is_nmethod()) {
        nmethod* nm = (nmethod*)cb;

        if (Verbose && nm->method() != NULL) {
          ResourceMark rm;
          char *method_name = nm->method()->name_and_sig_as_C_string();
          tty->print("%s", method_name);
          if(nm->is_alive()) { tty->print_cr(" alive"); }
          if(nm->is_not_entrant()) { tty->print_cr(" not-entrant"); }
          if(nm->is_zombie()) { tty->print_cr(" zombie"); }
        }

        nmethodCount++;

        if(nm->is_alive()) { nmethodAlive++; }
        if(nm->is_not_entrant()) { nmethodNotEntrant++; }
        if(nm->is_zombie()) { nmethodZombie++; }
        if(nm->is_unloaded()) { nmethodUnloaded++; }
        if(nm->method() != NULL && nm->is_native_method()) { nmethodNative++; }

        if(nm->method() != NULL && nm->is_java_method()) {
          nmethodJava++;
          max_nm_size = MAX2(max_nm_size, nm->size());
        }
      } else if (cb->is_runtime_stub()) {
        runtimeStubCount++;
      } else if (cb->is_deoptimization_stub()) {
        deoptimizationStubCount++;
      } else if (cb->is_uncommon_trap_stub()) {
        uncommonTrapStubCount++;
      } else if (cb->is_adapter_blob()) {
        adapterCount++;
      } else if (cb->is_buffer_blob()) {
        bufferBlobCount++;
      }
    }
  }

  int bucketSize = 512;
  int bucketLimit = max_nm_size / bucketSize + 1;
  int *buckets = NEW_C_HEAP_ARRAY(int, bucketLimit, mtCode);
  memset(buckets, 0, sizeof(int) * bucketLimit);

  NMethodIterator iter(NMethodIterator::all_blobs);
  while(iter.next()) {
    nmethod* nm = iter.method();
    if(nm->method() != NULL && nm->is_java_method()) {
      buckets[nm->size() / bucketSize]++;
    }
  }

  tty->print_cr("Code Cache Entries (total of %d)",total);
  tty->print_cr("-------------------------------------------------");
  tty->print_cr("nmethods: %d",nmethodCount);
  tty->print_cr("\talive: %d",nmethodAlive);
  tty->print_cr("\tnot_entrant: %d",nmethodNotEntrant);
  tty->print_cr("\tzombie: %d",nmethodZombie);
  tty->print_cr("\tunloaded: %d",nmethodUnloaded);
  tty->print_cr("\tjava: %d",nmethodJava);
  tty->print_cr("\tnative: %d",nmethodNative);
  tty->print_cr("runtime_stubs: %d",runtimeStubCount);
  tty->print_cr("adapters: %d",adapterCount);
  tty->print_cr("buffer blobs: %d",bufferBlobCount);
  tty->print_cr("deoptimization_stubs: %d",deoptimizationStubCount);
  tty->print_cr("uncommon_traps: %d",uncommonTrapStubCount);
  tty->print_cr("\nnmethod size distribution (non-zombie java)");
  tty->print_cr("-------------------------------------------------");

  for(int i=0; i<bucketLimit; i++) {
    if(buckets[i] != 0) {
      tty->print("%d - %d bytes",i*bucketSize,(i+1)*bucketSize);
      tty->fill_to(40);
      tty->print_cr("%d",buckets[i]);
    }
  }

  FREE_C_HEAP_ARRAY(int, buckets);
  print_memory_overhead();
}

#endif // !PRODUCT

void CodeCache::print() {
  print_summary(tty);

#ifndef PRODUCT
  if (!Verbose) return;

  CodeBlob_sizes live;
  CodeBlob_sizes dead;

  FOR_ALL_ALLOCABLE_HEAPS(heap) {
    FOR_ALL_BLOBS(cb, *heap) {
      if (!cb->is_alive()) {
        dead.add(cb);
      } else {
        live.add(cb);
      }
    }
  }

  tty->print_cr("CodeCache:");
  tty->print_cr("nmethod dependency checking time %fs", dependentCheckTime.seconds());

  if (!live.is_empty()) {
    live.print("live");
  }
  if (!dead.is_empty()) {
    dead.print("dead");
  }

  if (WizardMode) {
     // print the oop_map usage
    int code_size = 0;
    int number_of_blobs = 0;
    int number_of_oop_maps = 0;
    int map_size = 0;
    FOR_ALL_ALLOCABLE_HEAPS(heap) {
      FOR_ALL_BLOBS(cb, *heap) {
        if (cb->is_alive()) {
          number_of_blobs++;
          code_size += cb->code_size();
          ImmutableOopMapSet* set = cb->oop_maps();
          if (set != NULL) {
            number_of_oop_maps += set->count();
            map_size           += set->nr_of_bytes();
          }
        }
      }
    }
    tty->print_cr("OopMaps");
    tty->print_cr("  #blobs    = %d", number_of_blobs);
    tty->print_cr("  code size = %d", code_size);
    tty->print_cr("  #oop_maps = %d", number_of_oop_maps);
    tty->print_cr("  map size  = %d", map_size);
  }

#endif // !PRODUCT
}

void CodeCache::print_summary(outputStream* st, bool detailed) {
  int full_count = 0;
  FOR_ALL_HEAPS(heap_iterator) {
    CodeHeap* heap = (*heap_iterator);
    size_t total = (heap->high_boundary() - heap->low_boundary());
    if (_heaps->length() >= 1) {
      st->print("%s:", heap->name());
    } else {
      st->print("CodeCache:");
    }
    st->print_cr(" size=" SIZE_FORMAT "Kb used=" SIZE_FORMAT
                 "Kb max_used=" SIZE_FORMAT "Kb free=" SIZE_FORMAT "Kb",
                 total/K, (total - heap->unallocated_capacity())/K,
                 heap->max_allocated_capacity()/K, heap->unallocated_capacity()/K);

    if (detailed) {
      st->print_cr(" bounds [" INTPTR_FORMAT ", " INTPTR_FORMAT ", " INTPTR_FORMAT "]",
                   p2i(heap->low_boundary()),
                   p2i(heap->high()),
                   p2i(heap->high_boundary()));

      full_count += get_codemem_full_count(heap->code_blob_type());
    }
  }

  if (detailed) {
    st->print_cr(" total_blobs=" UINT32_FORMAT " nmethods=" UINT32_FORMAT
                       " adapters=" UINT32_FORMAT,
                       blob_count(), nmethod_count(), adapter_count());
    st->print_cr(" compilation: %s", CompileBroker::should_compile_new_jobs() ?
                 "enabled" : Arguments::mode() == Arguments::_int ?
                 "disabled (interpreter mode)" :
                 "disabled (not enough contiguous free space left)");
    st->print_cr("              stopped_count=%d, restarted_count=%d",
                 CompileBroker::get_total_compiler_stopped_count(),
                 CompileBroker::get_total_compiler_restarted_count());
    st->print_cr(" full_count=%d", full_count);
  }
}

void CodeCache::print_codelist(outputStream* st) {
  MutexLocker mu(CodeCache_lock, Mutex::_no_safepoint_check_flag);

  CompiledMethodIterator iter(CompiledMethodIterator::only_alive_and_not_unloading);
  while (iter.next()) {
    CompiledMethod* cm = iter.method();
    ResourceMark rm;
    char* method_name = cm->method()->name_and_sig_as_C_string();
    st->print_cr("%d %d %d %s [" INTPTR_FORMAT ", " INTPTR_FORMAT " - " INTPTR_FORMAT "]",
                 cm->compile_id(), cm->comp_level(), cm->get_state(),
                 method_name,
                 (intptr_t)cm->header_begin(), (intptr_t)cm->code_begin(), (intptr_t)cm->code_end());
  }
}

void CodeCache::print_layout(outputStream* st) {
  MutexLocker mu(CodeCache_lock, Mutex::_no_safepoint_check_flag);
  ResourceMark rm;
  print_summary(st, true);
}

void CodeCache::log_state(outputStream* st) {
  st->print(" total_blobs='" UINT32_FORMAT "' nmethods='" UINT32_FORMAT "'"
            " adapters='" UINT32_FORMAT "' free_code_cache='" SIZE_FORMAT "'",
            blob_count(), nmethod_count(), adapter_count(),
            unallocated_capacity());
}

#ifdef LINUX
void CodeCache::write_perf_map() {
  MutexLocker mu(CodeCache_lock, Mutex::_no_safepoint_check_flag);

  // Perf expects to find the map file at /tmp/perf-<pid>.map.
  char fname[32];
  jio_snprintf(fname, sizeof(fname), "/tmp/perf-%d.map", os::current_process_id());

  fileStream fs(fname, "w");
  if (!fs.is_open()) {
    log_warning(codecache)("Failed to create %s for perf map", fname);
    return;
  }

  AllCodeBlobsIterator iter(AllCodeBlobsIterator::only_alive_and_not_unloading);
  while (iter.next()) {
    CodeBlob *cb = iter.method();
    ResourceMark rm;
    const char* method_name =
      cb->is_compiled() ? cb->as_compiled_method()->method()->external_name()
                        : cb->name();
    fs.print_cr(INTPTR_FORMAT " " INTPTR_FORMAT " %s",
                (intptr_t)cb->code_begin(), (intptr_t)cb->code_size(),
                method_name);
  }
}
#endif // LINUX

//---<  BEGIN  >--- CodeHeap State Analytics.

void CodeCache::aggregate(outputStream *out, size_t granularity) {
  FOR_ALL_ALLOCABLE_HEAPS(heap) {
    CodeHeapState::aggregate(out, (*heap), granularity);
  }
}

void CodeCache::discard(outputStream *out) {
  FOR_ALL_ALLOCABLE_HEAPS(heap) {
    CodeHeapState::discard(out, (*heap));
  }
}

void CodeCache::print_usedSpace(outputStream *out) {
  FOR_ALL_ALLOCABLE_HEAPS(heap) {
    CodeHeapState::print_usedSpace(out, (*heap));
  }
}

void CodeCache::print_freeSpace(outputStream *out) {
  FOR_ALL_ALLOCABLE_HEAPS(heap) {
    CodeHeapState::print_freeSpace(out, (*heap));
  }
}

void CodeCache::print_count(outputStream *out) {
  FOR_ALL_ALLOCABLE_HEAPS(heap) {
    CodeHeapState::print_count(out, (*heap));
  }
}

void CodeCache::print_space(outputStream *out) {
  FOR_ALL_ALLOCABLE_HEAPS(heap) {
    CodeHeapState::print_space(out, (*heap));
  }
}

void CodeCache::print_age(outputStream *out) {
  FOR_ALL_ALLOCABLE_HEAPS(heap) {
    CodeHeapState::print_age(out, (*heap));
  }
}

void CodeCache::print_names(outputStream *out) {
  FOR_ALL_ALLOCABLE_HEAPS(heap) {
    CodeHeapState::print_names(out, (*heap));
  }
}

struct Vtables {
  intptr_t nmethod;
  intptr_t bufferblob;
  intptr_t runtimestub;
  intptr_t adapterblob;
  intptr_t exceptionblob;
  intptr_t methodhandlesadapterblob;
  intptr_t safepointblob;
  intptr_t uncommontrapblob;
  intptr_t deoptimizationblob;
};

struct PerMethod {
  intptr_t _from_interpreted_entry;
};

enum MetadataRecord {
  METHOD_RECORD,
  KLASS_RECORD
};

enum RuntimeCall {
  OPTORUNTIME__INITIALIZE_KLASS_C,
  OPTORUNTIME__NEW_ARRAY_C,
  MACROASSEMBLER__DEBUG64,
  OPTORUNTIME__RETHROW_C,
  SAFEPOINTSYNCHRONIZE__HANDLE_POLLING_PAGE_EXCEPTION,
  OPTORUNTIME__HANDLE_EXCEPTION_C,
  DEOPTIMIZATION__FETCH_UNROLL_INFO,
  DEOPTIMIZATION__UNPACK_FRAMES,
  DEOPTIMIZATION__UNCOMMON_TRAP,
  OPTORUNTIME__NEW_INSTANCE_C,
  SHAREDRUNTIME_HANDLE_WRONG_METHOD_IC_MISS,
  LAST_RUNTIMECALL
};

void CodeCache::dump_to_disk(FILE* file, JavaThread* thread) {
  Vtables vts;
  {
    nmethod nm;
    vts.nmethod = *(intptr_t*)&nm;
    BufferBlob bb;
    vts.bufferblob = *(intptr_t*)&bb;
    RuntimeStub rs;
    vts.runtimestub = *(intptr_t*)&rs;
    AdapterBlob ab;
    vts.adapterblob = *(intptr_t*)&ab;
    ExceptionBlob eb;
    vts.exceptionblob = *(intptr_t*)&eb;
    MethodHandlesAdapterBlob mhab;
    vts.methodhandlesadapterblob = *(intptr_t*)&mhab;
    SafepointBlob sb;
    vts.safepointblob = *(intptr_t*)&sb;
    UncommonTrapBlob utb;
    vts.uncommontrapblob = *(intptr_t*)&utb;
    DeoptimizationBlob db;
    vts.deoptimizationblob = *(intptr_t*)&db;
  }
  int w = fwrite(&vts, sizeof(vts), 1, file);
  assert(w == 1, "fwrite failed");
  ResourceMark rm;
  MutexLocker ml(CodeCache_lock, Mutex::_no_safepoint_check_flag);
  CodeHeap* heap = get_code_heap(CodeBlobType::MethodNonProfiled);
  FOR_ALL_BLOBS(cb, heap) {
    intptr_t vtbl = *(intptr_t*)cb;
    if (vtbl != vts.nmethod &&
        vtbl != vts.bufferblob &&
        vtbl != vts.runtimestub &&
        vtbl != vts.adapterblob &&
        vtbl != vts.exceptionblob &&
        vtbl != vts.methodhandlesadapterblob &&
        vtbl != vts.safepointblob &&
        vtbl != vts.uncommontrapblob &&
        vtbl != vts.deoptimizationblob &&
        true
    ) {
      ShouldNotReachHere();
    }
    int cb_size = cb->size();
//    tty->print_cr(">>> %d", cb_size);
    w = fwrite(&cb_size, sizeof(cb_size), 1, file);
    assert(w == 1, "fwrite failed");

    CodeBlob* next = next_blob(heap, cb);
    int offset = next != NULL ? (address)next - (address)cb : 0;
    tty->print_cr("XXX %s:%ld - %d %d - %p %p", cb->name(), (uintptr_t)cb - (uintptr_t)heap->low(), cb_size, offset, cb , next);
    w = fwrite(&offset, sizeof(offset), 1, file);
    assert(w == 1, "fwrite failed");

    if (cb->is_nmethod()) {
      RelocIterator iter(cb);
      nmethod* nm = cb->as_nmethod();
      while (iter.next()) {
        if (iter.type() == relocInfo::static_call_type) {
          static_call_Relocation* call = iter.static_call_reloc();
          Method* method = call->method_value();
          assert(method != NULL, "can't resolve the call");
          assert(method->has_compiled_code(), "should be compiled");
          call->set_destination(method->from_compiled_entry());
        } else if (iter.type() == relocInfo::opt_virtual_call_type) {
          opt_virtual_call_Relocation* call = iter.opt_virtual_call_reloc();
          Method* method = call->method_value();
          assert(method != NULL, "can't resolve the call");
          assert(method->has_compiled_code(), "should be compiled");
          call->set_destination(method->from_compiled_entry());
        } else if (iter.type() == relocInfo::virtual_call_type) {
          MutexUnlocker mul(CodeCache_lock, Mutex::_no_safepoint_check_flag);
          virtual_call_Relocation* call = iter.virtual_call_reloc();
          Method* method = call->method_value();
          Klass* defc = method->method_holder();
          Symbol* name = method->name();
          Symbol* type = method->signature();
          LinkInfo link_info(defc, name, type);
          Method* resolved_method = LinkResolver::linktime_resolve_virtual_method(link_info, thread);
          int vtable_index = Method::invalid_vtable_index;
          if (resolved_method->method_holder()->is_interface()) {
            vtable_index = LinkResolver::vtable_index_of_interface_method(link_info.resolved_klass(), methodHandle(thread, resolved_method));
          } else {
            vtable_index = resolved_method->vtable_index();
          }
          CompiledICLocker ml(nm);
          CompiledIC* inline_cache = CompiledIC_at(nm, iter.addr());
          address entry = VtableStubs::find_vtable_stub(vtable_index);
          inline_cache->set_ic_destination_and_value(entry, (void*)NULL);
        }
      }
    }

    CodeBlob* cb_copy = (CodeBlob*)NEW_RESOURCE_ARRAY(char, cb_size);;
    memcpy((void*)cb_copy, cb, cb_size);

    cb_copy->_code_begin = (address)cb_copy + (cb->_code_begin - (address)cb);
    cb_copy->_code_end = (address)cb_copy + (cb->_code_end - (address) cb);
    cb_copy->_content_begin = (address)cb_copy + (cb->_content_begin - (address)cb);
    cb_copy->_data_end = (address)cb_copy + (cb->_data_end - (address) cb);
    cb_copy->_relocation_begin = (address)cb_copy + (cb->_relocation_begin - (address) cb);
    cb_copy->_relocation_end = (address)cb_copy + (cb->_relocation_end - (address) cb);

    {
      RelocIterator iter(cb_copy);
      while (iter.next()) {
        if (iter.type() == relocInfo::runtime_call_type) {
          runtime_call_Relocation* rt = iter.runtime_call_reloc();
          if (rt->destination() == (address) OptoRuntime::initialize_klass_C) {
            rt->set_destination((address) OPTORUNTIME__INITIALIZE_KLASS_C);
          } else if (rt->destination() == (address) OptoRuntime::new_array_C) {
            rt->set_destination((address) OPTORUNTIME__NEW_ARRAY_C);
          } else if (rt->destination() == (address) MacroAssembler::debug64) {
            rt->set_destination((address) MACROASSEMBLER__DEBUG64);
          } else if (rt->destination() == (address) OptoRuntime::rethrow_C) {
            rt->set_destination((address) OPTORUNTIME__RETHROW_C);
          } else if (rt->destination() == (address) SafepointSynchronize::handle_polling_page_exception) {
            rt->set_destination((address) SAFEPOINTSYNCHRONIZE__HANDLE_POLLING_PAGE_EXCEPTION);
          } else if (rt->destination() == (address) OptoRuntime::handle_exception_C) {
            rt->set_destination((address) OPTORUNTIME__HANDLE_EXCEPTION_C);
          } else if (rt->destination() == (address) Deoptimization::fetch_unroll_info) {
            rt->set_destination((address) DEOPTIMIZATION__FETCH_UNROLL_INFO);
          } else if (rt->destination() == (address) Deoptimization::unpack_frames) {
            rt->set_destination((address) DEOPTIMIZATION__UNPACK_FRAMES);
          } else if (rt->destination() == (address)Deoptimization::uncommon_trap) {
            rt->set_destination((address) DEOPTIMIZATION__UNCOMMON_TRAP);
          } else if (rt->destination() == (address) OptoRuntime::new_instance_C) {
            rt->set_destination((address) OPTORUNTIME__NEW_INSTANCE_C);
          } else if (rt->destination() == (address) SharedRuntime::handle_wrong_method_ic_miss) {
            rt->set_destination((address) SHAREDRUNTIME_HANDLE_WRONG_METHOD_IC_MISS);
          }
        } else if (iter.type() == relocInfo::card_mark_word_type) {
          card_mark_word_Relocation* cm = iter.card_mark_word_reloc();
          BarrierSet* bs = BarrierSet::barrier_set();
          CardTableBarrierSet* ctbs = barrier_set_cast<CardTableBarrierSet>(bs);
          CardTable* ct = ctbs->card_table();
          assert(cm->value() == ct->byte_map_base(), "");
        }
      }
    }

    cb_copy->_code_begin = (address)(cb->_code_begin - (address)cb);
    cb_copy->_code_end = (address)(cb->_code_end - (address) cb);
    cb_copy->_content_begin = (address)(cb->_content_begin - (address)cb);
    cb_copy->_data_end = (address) (cb->_data_end - (address) cb);
    cb_copy->_relocation_begin = (address) (cb->_relocation_begin - (address) cb);
    cb_copy->_relocation_end = (address) (cb->_relocation_end - (address) cb);

    if (cb->is_nmethod()) {
      nmethod* nm = cb->as_nmethod();
      assert(nm->oops_end() - nm->oops_begin() == 1, "");
      assert((*nm->oops_begin()) == SystemDictionary::java_system_loader(), "");
      nmethod* nm_copy = (nmethod*)cb_copy;

      nm_copy->_scopes_data_begin = (address)(nm->_scopes_data_begin - (address)nm);
      nm_copy->_deopt_handler_begin = (address)(nm->_deopt_handler_begin - (address)nm);
      nm_copy->_deopt_mh_handler_begin = (address)(nm->_deopt_mh_handler_begin - (address)nm);
      nm_copy->_entry_point = (address) (nm->_entry_point - (address) nm);
      nm_copy->_verified_entry_point = (address) (nm->_verified_entry_point - (address) nm);
      nm_copy->_osr_entry_point = (address) (nm->_osr_entry_point - (address) nm);

      w = fwrite(nm_copy, cb_size, 1, file);
      assert(w == 1, "fwrite failed");

      Method* m = nm->method();
      write_method(file, m);
      int metadata_cnt = 0;
      {
        RelocIterator iter(nm, nm->oops_reloc_begin());
        while (iter.next()) {
          if (iter.type() == relocInfo::metadata_type) {
            metadata_Relocation* r = iter.metadata_reloc();
            if (r->metadata_value() != NULL) {
              metadata_cnt++;
            }
          }
        }
      }
      for (Metadata** p = nm->metadata_begin(); p < nm->metadata_end(); p++) {
        if (*p == Universe::non_oop_word() || *p == NULL) continue;  // skip non-oops
        metadata_cnt++;
      }
      w = fwrite(&metadata_cnt, sizeof(metadata_cnt), 1, file);
      assert(w == 1, "fwrite failed");
      {
        RelocIterator iter(nm, nm->oops_reloc_begin());
        while (iter.next()) {
          switch (iter.type()) {
            case relocInfo::metadata_type: {
              metadata_Relocation* r = iter.metadata_reloc();
              Metadata* md = r->metadata_value();
              if (md != NULL) {
                if (md->is_klass()) {
                  MetadataRecord rec = KLASS_RECORD;
                  w = fwrite(&rec, sizeof(rec), 1, file);
                  assert(w == 1, "fwrite failed");
                  write_klass(file, (Klass*) md);
                } else {
                  ShouldNotReachHere();
                }
              }
              break;
            }
            case relocInfo::oop_type:
            case relocInfo::runtime_call_w_cp_type:
              ShouldNotReachHere();
            default:
              break;
          }
        }
      }
      {
        GrowableArray<CodeBlob*> cbs;
        cbs.push(nm);
        for (int i = 0; i < cbs.length(); i++) {
          CodeBlob* cb = cbs.at(i);
          RelocIterator iter(cb);
          while (iter.next()) {
            switch (iter.type()) {
              case relocInfo::opt_virtual_call_type:
              case relocInfo::virtual_call_type:
              case relocInfo::static_call_type:
              case relocInfo::runtime_call_type: {
                address dest;
                if (iter.type() == relocInfo::opt_virtual_call_type) {
                  opt_virtual_call_Relocation* call = iter.opt_virtual_call_reloc();
                  dest = call->destination();
                } else if (iter.type() == relocInfo::virtual_call_type) {
                  virtual_call_Relocation* call = iter.virtual_call_reloc();
                  dest = call->destination();
                } else if (iter.type() == relocInfo::static_call_type) {
                  static_call_Relocation* call = iter.static_call_reloc();
                  dest = call->destination();
                } else if (iter.type() == relocInfo::runtime_call_type) {
                  runtime_call_Relocation* call = iter.runtime_call_reloc();
                  dest = call->destination();
                }
                if (heap->contains(dest)) {
                  CodeBlob* callee = CodeCache::find_blob(dest);
                  if (!cbs.contains(callee)) {
                    cbs.push(callee);
                  }
                } else if (dest != (address)OptoRuntime::initialize_klass_C &&
                           dest != (address)OptoRuntime::new_array_C &&
                           dest != (address)MacroAssembler::debug64 &&
                           dest != (address)OptoRuntime::rethrow_C &&
                           dest != (address)SafepointSynchronize::handle_polling_page_exception &&
                           dest != (address)OptoRuntime::handle_exception_C &&
                           dest != (address)Deoptimization::fetch_unroll_info &&
                           dest != (address)Deoptimization::unpack_frames &&
                           dest != (address)Deoptimization::uncommon_trap &&
                           dest != (address)OptoRuntime::new_instance_C &&
                           dest != (address)SharedRuntime::handle_wrong_method_ic_miss &&
                           dest != (address)-1) {
                  ShouldNotReachHere();
                }
              }
              default:
                break;
            }
          }
        }
      }
      for (Metadata** p = nm->metadata_begin(); p < nm->metadata_end(); p++) {
        if (*p == Universe::non_oop_word() || *p == NULL) continue;  // skip non-oops
        Metadata* md = *p;
        if (md->is_method()) {
          MetadataRecord rec = METHOD_RECORD;
          w = fwrite(&rec, sizeof(rec), 1, file);
          assert(w == 1, "fwrite failed");
          write_method(file, (Method*) md);
        } else if (md->is_klass()) {
          MetadataRecord rec = KLASS_RECORD;
          w = fwrite(&rec, sizeof(rec), 1, file);
          assert(w == 1, "fwrite failed");
          write_klass(file, (Klass*) md);
        } else {
          ShouldNotReachHere();
        }
      }
      PerMethod pm;
      assert(heap->contains(m->from_interpreted_entry()), "");
      pm._from_interpreted_entry = (address)cb - m->from_interpreted_entry();
      w = fwrite(&pm, sizeof(pm), 1, file);
      assert(w == 1, "fwrite failed");
      nm->print();
//      RelocIterator iter(nm, nm->oops_reloc_begin());
//      while(iter.next()) {
//        Relocation* r = iter.reloc();
//        if (r->is_call()) {
//          CallRelocation* cr = (CallRelocation*)r;
//          assert(heap->contains(cr->destination()) || (intptr_t)cr->destination() < LAST_RUNTIMECALL, "");
//        }
//      }

    } else {
      w = fwrite(cb_copy, cb_size, 1, file);
      assert(w == 1, "fwrite failed");
    }

    const char* name = cb->name();
    int name_len = strlen(name);
    w = fwrite(&name_len, sizeof(name_len), 1, file);
    assert(w == 1, "fwrite failed");
    w = fwrite(name, 1, name_len, file);
    assert(w == name_len, "fwrite failed");

    ImmutableOopMapSet* oopmaps = cb->oop_maps();
    int oopmaps_len = oopmaps == NULL ? 0 : oopmaps->nr_of_bytes();
    w = fwrite(&oopmaps_len, sizeof(oopmaps_len), 1, file);
    assert(w == 1, "fwrite failed");
    if (oopmaps_len > 0) {
      w = fwrite(oopmaps, oopmaps_len, 1, file);
      assert(w == 1, "fwrite failed");
    }

  }
//  tty->print_cr("XXX %d %d %d", nb, heap->high() - heap->low(), heap->high_boundary() - heap->low_boundary());
//  w = fwrite(heap->low(), 1, heap->high() - heap->low(), file);
//  assert(w == heap->high() - heap->low(), "fwrite failed");
  fclose(file);
}

void CodeCache::write_method(FILE* file, const Method* m) {
  write_symbol(file, m->klass_name());
  write_symbol(file, m->name());
  write_symbol(file, m->signature());
}

void CodeCache::write_symbol(FILE* file, const Symbol* sym) {
  int l = sym->utf8_length();
  int w = fwrite(&l, sizeof(l), 1, file);
  assert(w == 1, "fwrite failed");
  w = fwrite(sym->as_utf8(), 1, l, file);
  assert(w == l, "fwrite failed");
}

void CodeCache::restore_from_disk(FILE* file, JavaThread* thread) {
  Vtables vts;
  int r = fread(&vts, sizeof(vts), 1, file);
  assert(r == 1, "fwrite failed");
  MutexLocker ml(CodeCache_lock, Mutex::_no_safepoint_check_flag);
  ResourceMark rm;

  long cur = ftell(file);
  fseek(file, 0, SEEK_END);
  long end = ftell(file);
  fseek(file, cur, SEEK_SET);

//  tty->print_cr("XXX %ld %ld", cur, end);
  CodeHeap* heap = get_code_heap(CodeBlobType::All);
  tty->print_cr("XXX %p", heap->_freelist);
  heap->_freelist = NULL;

  address prev = NULL;
  int prev_offset = -1;
  while(ftell(file) != end) {
    int cb_size;
    r = fread(&cb_size, sizeof(cb_size), 1, file);
    assert(r == 1, "fread failed");
    int offset;
    r = fread(&offset, sizeof(offset), 1, file);
    assert(r == 1, "fwrite failed");

    tty->print_cr("XXX %d %d", cb_size, offset);

//    tty->print_cr("<<< %d", cb_size);
    CodeBlob* cb = (CodeBlob*) allocate(offset > 0 ? offset - CodeHeap::header_size() : cb_size, CodeBlobType::All);
    assert(prev == NULL || prev_offset == (address)cb - prev, "offset = %d differs from %d", prev_offset, (int)((address)cb - prev));

    r = fread(cb, cb_size, 1, file);
    assert(r == 1, "fread failed");
    intptr_t vtbl = *(intptr_t*)cb;

    if (vtbl == vts.nmethod) {
      nmethod nm;
      vtbl = *(intptr_t*)&nm;
    } else if (vtbl == vts.bufferblob) {
      BufferBlob bb;
      vtbl = *(intptr_t*)&bb;
    } else if (vtbl == vts.runtimestub) {
      RuntimeStub rs;
      vtbl = *(intptr_t*)&rs;
    } else if (vtbl == vts.adapterblob) {
      AdapterBlob ab;
      vtbl = *(intptr_t*)&ab;
    } else if (vtbl == vts.exceptionblob) {
      ExceptionBlob eb;
      vtbl = *(intptr_t*)&eb;
    } else if (vtbl == vts.methodhandlesadapterblob) {
      MethodHandlesAdapterBlob mhab;
      vtbl = *(intptr_t*)&mhab;
    } else if (vtbl == vts.safepointblob) {
      SafepointBlob sb;
      vtbl = *(intptr_t*)&sb;
    } else if (vtbl == vts.uncommontrapblob) {
      UncommonTrapBlob utb;
      vtbl = *(intptr_t*)&utb;
    } else if (vtbl == vts.deoptimizationblob) {
      DeoptimizationBlob db;
      vtbl = *(intptr_t*)&db;
    } else {
      ShouldNotReachHere();
    }
    *(intptr_t*)cb = vtbl;
    cb->_code_begin = (address)cb + (intptr_t)cb->_code_begin;
    cb->_code_end = (address)cb + (intptr_t)cb->_code_end;
    cb->_content_begin = (address)cb + (intptr_t)cb->_content_begin;
    cb->_data_end = (address)cb + (intptr_t)cb->_data_end;
    cb->_relocation_begin = (address)cb + (intptr_t)cb->_relocation_begin;
    cb->_relocation_end = (address)cb + (intptr_t)cb->_relocation_end;

    RelocIterator iter(cb);
    while(iter.next()) {
      if (iter.type() == relocInfo::runtime_call_type) {
        runtime_call_Relocation* rt = iter.runtime_call_reloc();
        if (rt->destination() == (address)OPTORUNTIME__INITIALIZE_KLASS_C) {
          rt->set_destination((address) OptoRuntime::initialize_klass_C);
        } else if (rt->destination() == (address) OPTORUNTIME__NEW_ARRAY_C) {
          rt->set_destination((address)OptoRuntime::new_array_C);
        } else if (rt->destination() == (address)MACROASSEMBLER__DEBUG64) {
          rt->set_destination((address)MacroAssembler::debug64);
        } else if (rt->destination() == (address)OPTORUNTIME__RETHROW_C) {
          rt->set_destination((address) OptoRuntime::rethrow_C);
        } else if (rt->destination() == (address)SAFEPOINTSYNCHRONIZE__HANDLE_POLLING_PAGE_EXCEPTION) {
          rt->set_destination((address) SafepointSynchronize::handle_polling_page_exception);
        } else if (rt->destination() == (address)OPTORUNTIME__HANDLE_EXCEPTION_C) {
          rt->set_destination((address)OptoRuntime::handle_exception_C);
        } else if (rt->destination() == (address) DEOPTIMIZATION__FETCH_UNROLL_INFO) {
          rt->set_destination((address)Deoptimization::fetch_unroll_info);
        } else if (rt->destination() == (address)DEOPTIMIZATION__UNPACK_FRAMES) {
          rt->set_destination((address)Deoptimization::unpack_frames);
        } else if (rt->destination() == (address)DEOPTIMIZATION__UNCOMMON_TRAP) {
          rt->set_destination((address) Deoptimization::uncommon_trap);
        } else if (rt->destination() == (address)OPTORUNTIME__NEW_INSTANCE_C) {
          rt->set_destination((address) OptoRuntime::new_instance_C);
        } else if (rt->destination() == (address) SHAREDRUNTIME_HANDLE_WRONG_METHOD_IC_MISS) {
          rt->set_destination((address) SharedRuntime::handle_wrong_method_ic_miss);
        } else {
          assert(!cb->is_nmethod() || rt->destination() == (address)-1 || heap->contains(rt->destination()), "");
        }
      } else if (iter.type() == relocInfo::card_mark_word_type) {
        card_mark_word_Relocation* cm = iter.card_mark_word_reloc();
        BarrierSet* bs = BarrierSet::barrier_set();
        CardTableBarrierSet* ctbs = barrier_set_cast<CardTableBarrierSet>(bs);
        CardTable* ct = ctbs->card_table();
        cm->set_value(ct->byte_map_base());
      }
    }

    if (cb->is_nmethod()) {
      nmethod* nm = cb->as_nmethod();

      (*nm->oops_begin()) = SystemDictionary::java_system_loader();
      nm->_pc_desc_container.reset_to(nm->scopes_pcs_begin());

      nm->_scopes_data_begin = (address)nm + (intptr_t)nm->_scopes_data_begin;
      nm->_deopt_handler_begin = (address)nm + (intptr_t)nm->_deopt_handler_begin;
      nm->_deopt_mh_handler_begin = (address)nm + (intptr_t)nm->_deopt_mh_handler_begin;
      nm->_entry_point = (address)nm + (intptr_t)nm->_entry_point;
      nm->_verified_entry_point = (address)nm + (intptr_t)nm->_verified_entry_point;
      nm->_osr_entry_point = (address)nm + (intptr_t)nm->_osr_entry_point;

      Method* m = read_method(file, thread);
      methodHandle mh(thread, m);

      int metadata_cnt;
      r = fread(&metadata_cnt, sizeof(metadata_cnt), 1, file);
      assert(r == 1, "fwrite failed");
      RelocIterator iter(nm, nm->oops_reloc_begin());
      while (iter.next()) {
        if (iter.type() == relocInfo::metadata_type) {
          metadata_Relocation* r = iter.metadata_reloc();
          Metadata* md = r->metadata_value();
          if (md != NULL) {
            assert(metadata_cnt > 0, "");
            metadata_cnt--;
            MetadataRecord rec;
            int read = fread(&rec, sizeof(rec), 1, file);
            assert(read == 1, "fwrite failed");
            if (rec == KLASS_RECORD) {
              Klass* k = read_klass(file, thread);
              *r->metadata_addr() = k;
            } else {
              ShouldNotReachHere();
            }
          }
        }
      }
      for (Metadata** p = nm->metadata_begin(); p < nm->metadata_end(); p++) {
        if (*p == Universe::non_oop_word() || *p == NULL) continue;  // skip non-oops
        assert(metadata_cnt > 0, "");
        metadata_cnt--;
        MetadataRecord rec;
        r = fread(&rec, sizeof(rec), 1, file);
        assert(r == 1, "fwrite failed");
        if (rec == METHOD_RECORD) {
          *p = read_method(file, thread);
        } else if (rec == KLASS_RECORD) {
          *p = read_klass(file, thread);
        } else {
          ShouldNotReachHere();
        }
      }

      nm->set_method(m);

      PerMethod pm;
      r = fread(&pm, sizeof(pm), 1, file);
      assert(r == 1, "fread failed");

      {
        MutexLocker ml(CompiledMethod_lock, Mutex::_no_safepoint_check_flag);
        mh->_code = nm;
        mh->set_highest_comp_level(nm->comp_level());
        OrderAccess::storestore();
        mh->_from_compiled_entry = nm->verified_entry_point();
        OrderAccess::storestore();
        // Instantly compiled code can execute.
        if (!mh->is_method_handle_intrinsic())
          mh->_from_interpreted_entry = (address)cb - pm._from_interpreted_entry;
        mh->_i2i_entry = (address)-1;
      }
      nm->_gc_data = NULL;

      Universe::heap()->register_nmethod(nm);
      CodeCache::commit(nm);

      nm->print();
    }
    int name_len;
    r = fread(&name_len, sizeof(name_len), 1, file);
    assert(r == 1, "fread failed");
    char* name = NEW_C_HEAP_ARRAY(char, name_len+1, mtCode);
    r = fread(name, 1, name_len, file);
    assert(r == name_len, "fread failed");
    name[name_len] = '\0';
    cb->_name = name;

    int oopmaps_len;
    r = fread(&oopmaps_len, sizeof(oopmaps_len), 1, file);
    assert(r == 1, "fread failed");
    if (oopmaps_len > 0) {
      ImmutableOopMapSet* oopmaps = (ImmutableOopMapSet*)NEW_C_HEAP_ARRAY(char, oopmaps_len, mtCode);
      r = fread(oopmaps, oopmaps_len, 1, file);
      assert(r == 1, "fread failed");
      cb->_oop_maps = oopmaps;
    } else {
      cb->_oop_maps = NULL;
    }

    tty->print_cr("XXX %s:%ld", cb->name(), (uintptr_t)cb - (uintptr_t)heap->low());
    prev = (address)cb;
    prev_offset = offset;
  }
//  FOR_ALL_BLOBS(cb, heap) {
//    if (cb->is_nmethod()) {
//      nmethod* nm = cb->as_nmethod();
//      RelocIterator iter(nm, nm->oops_reloc_begin());
//      while(iter.next()) {
//        Relocation* r = iter.reloc();
//        if (r->is_call()) {
//          CallRelocation* cr = (CallRelocation*)r;
//          assert(heap->contains(cr->destination()), "");
//        }
//      }
//    }
//  }

  fclose(file);

#if 0
  CodeHeap* heap = get_code_heap(CodeBlobType::MethodNonProfiled);
  FOR_ALL_BLOBS(cb, heap) {
    intptr_t vtbl = *(intptr_t*) cb;
    if (vtbl == vts.nmethod) {
      nmethod nm;
      vtbl = *(intptr_t*)&nm;
    } else if (vtbl == vts.bufferblob) {
      BufferBlob bb;
      vtbl = *(intptr_t*)&bb;
    } else if (vtbl == vts.runtimestub) {
      RuntimeStub rs;
      vtbl = *(intptr_t*)&rs;
    } else if (vtbl == vts.adapterblob) {
      AdapterBlob ab;
      vtbl = *(intptr_t*)&ab;
    } else if (vtbl == vts.exceptionblob) {
      ExceptionBlob eb;
      vtbl = *(intptr_t*)&eb;
    } else if (vtbl == vts.methodhandlesadapterblob) {
      MethodHandlesAdapterBlob mhab;
      vtbl = *(intptr_t*)&mhab;
    } else if (vtbl == vts.safepointblob) {
      SafepointBlob sb;
      vtbl = *(intptr_t*)&sb;
    } else if (vtbl == vts.uncommontrapblob) {
      UncommonTrapBlob utb;
      vtbl = *(intptr_t*)&utb;
    } else if (vtbl == vts.deoptimizationblob) {
      DeoptimizationBlob db;
      vtbl = *(intptr_t*)&db;
    } else {
      ShouldNotReachHere();
    }
    *(intptr_t*) cb = vtbl;
  }
#endif
}

Method* CodeCache::read_method(FILE* file, JavaThread* thread) {
  Klass* k = read_klass(file, thread);
  Symbol* method_sym = read_symbol(file);
  Symbol* signature_sym = read_symbol(file);
  Method* m = InstanceKlass::cast(k)->find_method(method_sym, signature_sym);
  assert(m != NULL, "method not found");
  return m;
}

Klass* CodeCache::read_klass(FILE* file, JavaThread* thread) {
  Symbol* klass_sym = read_symbol(file);
  Klass* k = SystemDictionary::resolve_or_fail(klass_sym, Handle(thread, SystemDictionary::java_system_loader()),
                                               Handle(), true, thread);
  assert(k != NULL && !thread->has_pending_exception(), "resolution failure");
  return k;
}

Symbol* CodeCache::read_symbol(FILE* file) {
  int l;
  int r = fread(&l, sizeof(l), 1, file);
  assert(r == 1, "fread failed");
  char* name = NEW_RESOURCE_ARRAY(char, l + 1);
  r = fread(name, 1, l, file);
  assert(r == l, "fread failed");
  name[l] = '\0';
  return SymbolTable::new_symbol(name, l);
}

void CodeCache::write_klass(FILE* file, Klass* klass) {
  write_symbol(file, klass->name());
}
//---<  END  >--- CodeHeap State Analytics.
