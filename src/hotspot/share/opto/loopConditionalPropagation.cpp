/*
 * Copyright (c) 2021, Red Hat, Inc. All rights reserved.
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

#include "precompiled.hpp"
#include "opto/loopnode.hpp"
#include "opto/rootnode.hpp"
#include "opto/callnode.hpp"

class PhaseConditionalPropagation : public PhaseIterGVN {
private:
  class TreeNode : public ResourceObj {
  private:
    Node* _node;
    const Type* _type;
    TreeNode* _left;
    TreeNode* _right;
    int _rpo;

  public:
    TreeNode(Node* n, const Type* type)
            : _node(n), _type(type), _left(NULL), _right(NULL), _rpo(0) {
    }

    TreeNode(Node* n, const Type* type, int rpo, TreeNode* left, TreeNode* right)
            : _node(n), _type(type), _left(left), _right(right), _rpo(rpo) {
    }

    TreeNode()
            : _node(NULL), _type(NULL), _left(NULL), _right(NULL), _rpo(0) {
    }

    const Node* node() const { return _node; };

    const node_idx_t idx() const { return _node->_idx; }

    void set_left(TreeNode* left) {
      _left = left;
    }

    void set_right(TreeNode* right) {
      _right = right;
    }

    const TreeNode* left() const {
      return _left;
    }

    const TreeNode* right() const {
      return _right;
    }

    const Type* type() const {
      return _type;
    }

    const TreeNode* find(const Node* node) const {
      const TreeNode* tn = this;
      node_idx_t idx = node->_idx;
      do {
        if (tn->_node == node) {
          return tn;
        } else {
          if (idx < tn->idx()) {
            tn = tn->_left;
          } else if (idx > tn->idx()) {
            tn = tn->_right;
          }
        }
      } while (tn != NULL);
      return NULL;
    }

    TreeNode* set_type(Node* n, const Type* t, int rpo) {
      assert(_rpo <= rpo, "");
      if (_node == n) {
        if (_rpo < rpo) {
          return new TreeNode(_node, t, rpo, _left, _right);
        } else {
          _type = t;
          return this;
        }
      } else if (n->_idx < idx()) {
        assert(_left != NULL, "");
        TreeNode* tn = _left->set_type(n, t, rpo);
        if (_rpo == rpo) {
          _left = tn;
          return this;
        } else {
          assert(tn != _left, "");
          return new TreeNode(_node, _type, rpo, tn, _right);
        }
      } else if (n->_idx > idx()) {
        assert(_right != NULL, "");
        TreeNode* tn = _right->set_type(n, t, rpo);
        if (_rpo == rpo) {
          _right = tn;
          return this;
        } else {
          assert(tn != _right, "");
          return new TreeNode(_node, _type, rpo, _left, tn);
        }
      }
      ShouldNotReachHere();
      return NULL;
    }

    class Iterator : public StackObj {
    private:
      TreeNode* _current1;
      TreeNode* _current2;
      GrowableArray<TreeNode*> _stack1;
      GrowableArray<TreeNode*> _stack2;
    public:
      Iterator(TreeNode* root1, TreeNode* root2) :
              _current1(NULL), _current2(NULL) {
        _stack1.push(root1);
        _stack2.push(root2);
      }

      bool next() {
        _current1 = _current2 = NULL;
        assert(_stack1.length() == _stack2.length(), "");
        while (_stack1.is_nonempty()) {
          TreeNode* tn1 = _stack1.pop();
          TreeNode* tn2 = _stack2.pop();
          assert(tn1->_node = tn2->_node, "");
          assert((tn1->_left != NULL) == (tn2->_left != NULL), "");
          assert((tn1->_right != NULL) == (tn2->_right != NULL), "");
          if (tn1 == tn2) {
            continue;
          }

          if (tn1->_left != NULL) {
            _stack1.push(tn1->_left);
            _stack2.push(tn2->_left);
          }
          if (tn1->_right != NULL) {
            _stack1.push(tn1->_right);
            _stack2.push(tn2->_right);
          }

          if (tn1->_type != tn2->_type) {
            _current1 = tn1;
            _current2 = tn2;
            return true;
          }
        }
        return false;
      }

      const Type* type1() const {
        return _current1->_type;
      }

      const Type* type2() const {
        return _current2->_type;
      }

      Node* node() const {
        return _current1->_node;
      }
    };

    const Type* get_type(const Node* n) {
      const TreeNode* tn = find(n);
      assert(tn != NULL, "");
      return tn->_type;
    }
  };

  struct interval {
    int beg;
    int end;
  };

  void build_types_tree(VectorSet &visited) {
    GrowableArray<TreeNode> nodes;
    Compile* C = _phase->C;
    nodes.push(TreeNode(C->root(), PhaseTransform::type(C->root())));
    visited.set(C->root()->_idx);
    for (int i = 0; i < nodes.length(); i++) {
      TreeNode tn = nodes.at(i);
      for (uint j = 0; j < tn.node()->req(); j++) {
        Node* in = tn.node()->in(j);
        if (in != NULL && !visited.test_set(in->_idx)) {
          nodes.push(TreeNode(in, PhaseTransform::type(in)));
        }
      }
    }
    nodes.sort([](TreeNode* tn1, TreeNode* tn2) { return tn1->idx() < tn2->idx() ? -1 : (tn1->idx() > tn2->idx() ? 1 : 0); });
    int length = nodes.length();
#ifdef ASSERT
    for (int i = 1; i < length; i++) {
      assert(nodes.at(i).idx() > nodes.at(i-1).idx(), "");
    }
#endif
    GrowableArray<interval> stack;
    stack.push({0, length - 1});
    int root = (length - 1) / 2;
    do {
      interval i = stack.pop();
      int current = (i.end - i.beg) / 2 + i.beg;
      TreeNode& current_node = nodes.at(current);
      int left = (current - 1 - i.beg) / 2 + i.beg;
      if (left != current) {
        current_node.set_left(nodes.adr_at(left));
      }
      if (current - i.beg > 1) {
        stack.push({i.beg, current - 1});
      }
      int right = (i.end - (current + 1)) / 2 + current + 1;
      if (right != current) {
        current_node.set_right(nodes.adr_at(right));
      }
      if (i.end - current > 1) {
        stack.push({current + 1, i.end});
      }
    } while (stack.is_nonempty());
    TreeNode* tree_root = nodes.adr_at(root);
    _types_at_ctrl.Insert(C->root(), tree_root);
  }

  bool valid_use(Node* u, Node* c) const {
    if (u->is_Phi() || !_visited.test(u->_idx)) {
      return false;
    }
    Node* u_c = _phase->ctrl_or_self(u);
    if (!_phase->is_dominator(c, u_c) && (u->is_CFG() || !_phase->is_dominator(u_c, c))) {
      return false;
    }
    if (!u->is_CFG() && u->in(0) != NULL && u->in(0)->is_CFG() && !_phase->is_dominator(u->in(0), c)) {
      return false;
    }
    return true;
  }

  void enqueue_uses(const Node* n, Node* c) {
    assert(_visited.test(n->_idx), "");
    for (DUIterator_Fast imax, i = n->fast_outs(imax); i < imax; i++) {
      Node* u = n->fast_out(i);
      if (valid_use(u, c)) {
        _wq.push(u);
        if (u->Opcode() == Op_AddI || u->Opcode() == Op_SubI) {
          for (DUIterator_Fast i2max, i2 = u->fast_outs(i2max); i2 < i2max; i2++) {
            Node* uu = u->fast_out(i2);
            if (uu->Opcode() == Op_CmpU && valid_use(uu, c)) {
              _wq.push(uu);
            }
          }
        }
        if (u->is_AllocateArray()) {
          for (DUIterator_Fast i2max, i2 = u->fast_outs(i2max); i2 < i2max; i2++) {
            Node* uu = u->fast_out(i2);
            if (uu->is_Proj() && uu->as_Proj()->_con == TypeFunc::Control) {
              Node* catch_node = uu->find_out_with(Op_Catch);
              if (catch_node != NULL) {
                _wq.push(catch_node);
              }
            }
          }
        }
      }

    }
  }

  void set_type(Node* n, const Type* t, int rpo) {
    PhaseTransform::set_type(n, t);
    _current_types = _current_types->set_type(n, t, rpo);
  }

  void sync_from_tree(Node* c) {
    _current_types = (TreeNode*) _types_at_ctrl[c];
    assert(_current_types != NULL, "");
    TreeNode::Iterator iter((TreeNode*)_types_at_ctrl[_current_ctrl], (TreeNode*) _current_types);
    while (iter.next()) {
      Node* node = iter.node();
      const Type* t = iter.type2();
      PhaseTransform::set_type(node, t);
    }
    _current_ctrl = c;
  }

  PhaseIdealLoop* _phase;
  VectorSet _visited;
  Dict _types_at_ctrl;
  Node_List _rpo_list;
  TreeNode* _current_types;
  Node* _current_ctrl;
#ifdef ASSERT
  VectorSet _conditions;
#endif
  Unique_Node_List _wq;


public:
  PhaseConditionalPropagation(PhaseIdealLoop* phase, VectorSet &visited, Node_Stack &nstack, Node_List &rpo_list)
  : PhaseIterGVN(&phase->igvn()),
    _phase(phase),
    _visited(visited),
    _types_at_ctrl(cmpkey, hashptr),
    _rpo_list(rpo_list),
    _current_types(NULL),
    _current_ctrl(phase->C->root()) {
    assert(nstack.is_empty(), "");
    assert(_rpo_list.size() == 0, "");
    phase->rpo(C->root(), nstack, _visited, _rpo_list);
    Node* root = _rpo_list.pop();
    assert(root == C->root(), "");

    _visited.clear();
    build_types_tree(_visited);
  }

  void analyze() {
    bool progress = true;
    int iterations = 0;
    int extra_rounds = 0;
    while (progress) {
      iterations++;
      assert(iterations <= 2 || _phase->ltree_root()->_child != NULL, "");
      assert(iterations - extra_rounds >= 0, "");
      assert(iterations - extra_rounds <= 3 || _phase->_has_irreducible_loops, "");

      progress = false;
      bool extra = false;
      for (int i = _rpo_list.size() - 1; i >= 0; i--) {
        int rpo = _rpo_list.size() - 1 - i;
        Node* c = _rpo_list.at(i);
        Node* dom = _phase->idom(c);

        TreeNode* types_at_dom = (TreeNode*) (_types_at_ctrl[dom]);
        TreeNode* prev_types_at_c = (TreeNode*) (_types_at_ctrl[c]);
        TreeNode* types_at_c = types_at_dom;
        if (c->is_Region()) {
          Node* in = c->in(1);
          TreeNode* types_at_in1 = (TreeNode*) (_types_at_ctrl[in]);
          if (types_at_in1 != NULL) {
            TreeNode::Iterator iter(types_at_dom, types_at_in1);
            while (iter.next()) {
              Node* node = iter.node();
              uint j = 2;
              const Type* t = iter.type2();
              const Type* current_type = types_at_dom->get_type(node);
              for (; j < c->req(); j++) {
                in = c->in(j);
                TreeNode* types_at_in = (TreeNode*) (_types_at_ctrl[in]);
                if (types_at_in == NULL) {
                  assert(_phase->get_loop(c)->_irreducible, "");
                  break;
                }
                const Type* type_at_in = types_at_in->get_type(node);
                if (type_at_in == current_type) {
                  break;
                }
                t = t->meet_speculative(type_at_in);
              }
              if (j == c->req()) {
                if (prev_types_at_c != NULL) {
                  const Type* prev_t = t;
                  t = t->filter(prev_types_at_c->get_type(node));
                  assert(t == prev_t, "");
                  t = saturate(t, prev_types_at_c->get_type(node), NULL);
                  if (c->is_Loop() && t != prev_types_at_c->get_type(node)) {
                    extra = true;
                  }
                  t = t->filter(current_type);
                }

                if (t != current_type) {
                  if (types_at_c->get_type(node) != t) {
#ifdef ASSERT
                    assert(narrows_type(types_at_c->get_type(node), t), "");
#endif
                    types_at_c = types_at_c->set_type(node, t, rpo);
                    enqueue_uses(node, c);
                  }
                }
              }
            }
          } else {
            assert(_phase->get_loop(c)->_irreducible || c->unique_ctrl_out()->Opcode() == Op_NeverBranch, "");
          }
        } else if (c->is_IfProj()) {
          Node* iff = c->in(0);
          assert(iff->is_If(), "");
          if (iff->as_If()->safe_for_optimizations() &&
              !(iff->is_CountedLoopEnd() && iff->as_CountedLoopEnd()->loopnode() != NULL && iff->as_CountedLoopEnd()->loopnode()->is_strip_mined())) {
            Node* bol = iff->in(1);
            if (iff->is_OuterStripMinedLoopEnd()) {
              assert(iff->in(0)->in(0)->in(0)->is_CountedLoopEnd(), "");
              bol = iff->in(0)->in(0)->in(0)->in(1);
            }
            if (bol->Opcode() == Op_Opaque4) {
              bol = bol->in(1);
            }
            if (bol->is_Bool()) {
              Node* cmp = bol->in(1);
              if (cmp->Opcode() == Op_CmpI || cmp->Opcode() == Op_CmpU ||
                  cmp->Opcode() == Op_CmpL || cmp->Opcode() == Op_CmpUL) {
                Node* cmp1 = cmp->in(1);
                Node* cmp2 = cmp->in(2);
                sync_from_tree(iff);
                types_at_c = analyze_if(rpo, c, types_at_c, cmp, cmp1);
                types_at_c = analyze_if(rpo, c, types_at_c, cmp, cmp2);
              }
            }
          }
        } else if (c->is_CatchProj() && c->in(0)->in(0)->in(0)->is_AllocateArray() && c->as_CatchProj()->_con == CatchProjNode::fall_through_index) {
          AllocateArrayNode* alloc = c->in(0)->in(0)->in(0)->as_AllocateArray();
          Node* length = alloc->in(AllocateArrayNode::ALength);
          Node* klass = alloc->in(AllocateNode::KlassNode);
          const Type* klass_t = types_at_c->get_type(klass);
          if (klass_t != Type::TOP) {
            const TypeOopPtr* ary_type = types_at_c->get_type(klass)->is_klassptr()->as_instance_type();
            const TypeInt* length_type = types_at_c->get_type(length)->isa_int();
            if (ary_type->isa_aryptr() && length_type != NULL) {
              const Type* narrow_length_type = ary_type->is_aryptr()->narrow_size_type(length_type);
              narrow_length_type = narrow_length_type->filter(length_type);
              assert(narrows_type(length_type, narrow_length_type), "");
              if (narrow_length_type != length_type) {
                types_at_c = types_at_c->set_type(length, narrow_length_type, rpo);
                enqueue_uses(length, c);
              }
            }
          }
        }
        for (DUIterator_Fast imax, i = c->fast_outs(imax); i < imax; i++) {
          Node* u = c->fast_out(i);
          if (!u->is_CFG() && u->in(0) == c && _visited.test(u->_idx)) {
            _wq.push(u);
          }
        }

        _types_at_ctrl.Insert(c, types_at_c);

        sync_from_tree(c);
        while (_wq.size() > 0) {
          Node* n = _wq.pop();
          const Type* t = n->Value(this);
          if (n->is_Phi() && prev_types_at_c != NULL) {
            const Type* prev_t = t;
            t = t->filter(prev_types_at_c->get_type(n));
            assert(t == prev_t, "");
            if (!(n->in(0)->is_CountedLoop() && n->in(0)->as_CountedLoop()->phi() == n)) {
              t = saturate(t, prev_types_at_c->get_type(n), NULL);
            }
            if (c->is_Loop() && t != prev_types_at_c->get_type(n)) {
              extra = true;
            }
          }
          t = t->filter(PhaseTransform::type(n));
          if (t != PhaseTransform::type(n)) {
#ifdef ASSERT
            assert(narrows_type(PhaseTransform::type(n), t), "");
#endif
            set_type(n, t, rpo);
            enqueue_uses(n, c);
          }
        }
        if (types_at_c != _current_types) {
          _types_at_ctrl.Insert(c, _current_types);
          types_at_c = _current_types;
        }
        progress = progress || (prev_types_at_c == NULL && types_at_c != types_at_dom) || (prev_types_at_c != NULL && TreeNode::Iterator(prev_types_at_c, types_at_c).next());
#ifdef ASSERT
        if (prev_types_at_c != NULL || (types_at_c != types_at_dom)) {
          if (PrintLoopConditionalPropagation) {
            TreeNode::Iterator iter(types_at_dom, types_at_c);
            bool failure = false;
            while (iter.next()) {
              const Type* t1 = iter.type1();
              const Type* t2 = iter.type2();
              tty->print("@ iteration %d for node %d at control %d: ", iterations, iter.node()->_idx, c->_idx);
              tty->print(" ");
              t1->dump();
              tty->print(" - ");
              t2->dump();
              tty->cr();
            }
          }
          {
            TreeNode::Iterator iter(prev_types_at_c != NULL ? prev_types_at_c : types_at_dom, types_at_c);
            bool failure = false;
            while (iter.next()) {
              const Type* t1 = iter.type1();
              const Type* t2 = iter.type2();
              if (!narrows_type(t1, t2)) {
                failure = true;
                if (PrintLoopConditionalPropagation) {
                  tty->print("XXX ");
                  tty->print("@ iteration %d for node %d at control %d: ", iterations, iter.node()->_idx, c->_idx);
                  tty->print(" ");
                  t1->dump();
                  tty->print(" - ");
                  t2->dump();
                  tty->cr();
                }
              }
            }
            assert(!failure, "");
          }
        }
#endif
      }
      if (extra) {
        extra_rounds++;
      }
    }

    sync_from_tree(C->root());
  }

  TreeNode* analyze_if(int rpo, Node* c, TreeNode* types_at_c, const Node* cmp, Node* in) {
    const Type* t = IfNode::filtered_int_type(this, in, c, (cmp->Opcode() == Op_CmpI || cmp->Opcode() == Op_CmpU) ? T_INT : T_LONG);
    if (t != NULL) {
      t = types_at_c->get_type(in)->filter(t);
      assert(narrows_type(types_at_c->get_type(in), t), "");
      if (types_at_c->get_type(in) != t) {
#ifdef ASSERT
        _conditions.set(c->_idx);
#endif
        types_at_c = types_at_c->set_type(in, t, rpo);
        enqueue_uses(in, c);
      }
    }
    return types_at_c;
  }

  bool narrows_type(const Type* old_t, const Type* new_t) {
    if (new_t == Type::TOP) {
      return true;
    }

    if (old_t == Type::TOP) {
      return false;
    }

    if (!new_t->isa_int() && !new_t->isa_long()) {
      return true;
    }

    assert(old_t->isa_int() || old_t->isa_long(), "");
    assert((old_t->isa_int() != NULL) == (new_t->isa_int() != NULL), "");

    BasicType bt = new_t->isa_int() ? T_INT : T_LONG;

    const TypeInteger* new_int = new_t->is_integer(bt);
    const TypeInteger* old_int = old_t->is_integer(bt);

    if (new_int->lo_as_long() < old_int->lo_as_long()) {
      return false;
    }

    if (new_int->hi_as_long() > old_int->hi_as_long()) {
      return false;
    }

    return true;
  }

  void do_transform() {
    _wq.push(_phase->C->root());
    bool progress = false;
    for (uint i = 0; i < _wq.size(); i++) {
      Node* c = _wq.at(i);

      TreeNode* types = (TreeNode*) _types_at_ctrl[c];
      if (types->get_type(c) == Type::TOP) {
        assert(c->is_CatchProj() && c->in(0)->in(0)->in(0)->is_AllocateArray(), "");
        replace_node(c, _phase->C->top());
        _phase->C->set_major_progress();
        continue;
      }


      for (DUIterator_Fast imax, i = c->fast_outs(imax); i < imax; i++) {
        Node* u = c->fast_out(i);
        if (u->is_CFG() && !_wq.member(u)) {
          if (transform_helper(u)) {
            progress = true;
          }
        }
      }

    }
  }

  bool validate_control(Node* n, Node* c) {
    ResourceMark rm;
    Unique_Node_List wq;
    wq.push(n);
    for (uint i = 0; i < wq.size(); i++) {
      Node* node = wq.at(i);
      assert(!node->is_CFG(), "");
      for (DUIterator_Fast jmax, j = node->fast_outs(jmax); j < jmax; j++) {
        Node* u = node->fast_out(j);
        if (!_visited.test(u->_idx)) {
          continue;
        }
        if (u->is_CFG()) {
          if (_phase->is_dominator(u, c)) {
            return true;
          }
        } else if (u->is_Phi()) {
          for (uint k = 1; k < u->req(); k++) {
            if (u->in(k) == node && _phase->is_dominator(u->in(0)->in(k), c)) {
              return true;
            }
          }
        } else {
          wq.push(u);
        }
      }
    }
    return false;
  }

  bool transform_helper(Node* c) {
    bool progress = false;
    TreeNode* types = (TreeNode*) _types_at_ctrl[c];
    {
      TreeNode::Iterator iter((TreeNode*) _types_at_ctrl[_phase->idom(c)], types);
      while (iter.next()) {
        Node* node = iter.node();
        const Type* t = iter.type2();
        if (t->singleton()) {
          if (node->is_CFG()) {
            continue;
          }
          {
            Node* con = NULL;
            for (DUIterator_Fast imax, i = node->fast_outs(imax); i < imax; i++) {
              Node* use = node->fast_out(i);
              if (_phase->is_dominator(c, _phase->ctrl_or_self(use))) {
                progress = true;
                if (con == NULL) {
                  con = makecon(t);
                  _phase->set_ctrl(con, C->root());
                }
                rehash_node_delayed(use);
                int nb = use->replace_edge(node, con, this);
                --i, imax -= nb;
#ifdef ASSERT
                if (PrintLoopConditionalPropagation) {
                  tty->print_cr("constant folding");
                  iter.node()->dump();
                  use->dump();
                  iter.type1()->dump();
                  tty->cr();
                  iter.type2()->dump();
                  tty->cr();
                }
#endif
                if (use->is_If()) {
                  _phase->C->set_major_progress();
                }
              }
            }
            if (!node->is_CFG() && node->outcnt() > 0) {
              Node* node_c = _phase->get_ctrl(node);
              IdealLoopTree* node_loop = _phase->get_loop(node_c);
              Node* node_loop_head = node_loop->head();
              if (node_loop_head->is_OuterStripMinedLoop()) {
                Node* late_ctrl = _phase->get_late_ctrl(node, node_c);
                if (!node_loop->is_member(_phase->get_loop(late_ctrl))) {
                  _phase->set_ctrl(node, node_loop_head->as_OuterStripMinedLoop()->outer_loop_exit());
                }
              }
            }
          }
        } else if (node->is_Type() && c == node->in(0)) {
          progress = true;
#ifdef ASSERT
          assert(narrows_type(node->bottom_type(), t), "");
          if (PrintLoopConditionalPropagation) {
            tty->print_cr("improved type for");
            node->dump();
            iter.type1()->dump();
            tty->cr();
            iter.type2()->dump();
            tty->cr();
          }
#endif
          rehash_node_delayed(node);
          node->as_Type()->set_type(t);
          PhaseTransform::set_type(node, t);
        }
      }
    }
    {
      TreeNode::Iterator iter((TreeNode*) _types_at_ctrl[_phase->idom(c)], types);
      while (iter.next()) {
        Node* node = iter.node();
        const Type* t = iter.type2();
        if (t->singleton()) {
          if (node->is_CFG()) {
            continue;
          }
          if (t == Type::TOP) {
#ifdef ASSERT
            if (PrintLoopConditionalPropagation) {
              tty->print("top at %d", c->_idx);
              iter.node()->dump();
            }
#endif
            if (c->is_IfProj()) {
              if (!validate_control(node, c)) {
                continue;
              }
              Node* iff = c->in(0);
              Node* bol = iff->in(1);
              const Type* bol_t = bol->bottom_type();
              const Type* new_bol_t = TypeInt::make(1 - c->as_IfProj()->_con);
              if (bol_t != new_bol_t) {
                progress = true;
                assert((c->is_IfProj() && _conditions.test(c->_idx)), "");
                Node* con = makecon(new_bol_t);
                _phase->set_ctrl(con, C->root());
                rehash_node_delayed(iff);
                iff->set_req_X(1, con, this);
                _phase->C->set_major_progress();
#ifdef ASSERT
                if (PrintLoopConditionalPropagation) {
                  tty->print_cr("killing path");
                  iter.node()->dump();
                  bol_t->dump();
                  tty->cr();
                  new_bol_t->dump();
                  tty->cr();
                  c->dump();
                }
#endif
              }
            }
          }
        }
      }
    }

    if (c->is_IfProj()) {
      IfNode* iff = c->in(0)->as_If();
      const TypeInt* bol_t = iff->in(1)->bottom_type()->is_int();
      if (bol_t->is_con()) {
        if (iff->proj_out(bol_t->get_con()) == c) {
          _wq.push(c);
          assert(((TreeNode*) _types_at_ctrl[iff])->get_type(c) != Type::TOP, "");
        }
      } else {
        _wq.push(c);
      }
    } else {
      _wq.push(c);
    }

    return progress;
  }

  const Type* type(const Node* n, const Node* c) const {
    assert(c->is_CFG(), "");
    TreeNode* types = (TreeNode*) _types_at_ctrl[c];
    if (types == NULL) {
      return PhaseTransform::type(n);
    }
    return types->get_type(n);
  }

  virtual PhaseConditionalPropagation* is_ConditionalPropagation() { return this; }

};

void PhaseIdealLoop::conditional_elimination(VectorSet &visited, Node_Stack &nstack, Node_List &rpo_list) {
  PhaseConditionalPropagation pcp(this, visited, nstack, rpo_list);
  pcp.analyze();
  pcp.do_transform();
  _igvn = pcp;
  C->print_method(PHASE_DEBUG, 2);
}

