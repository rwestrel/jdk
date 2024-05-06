/*
 * Copyright (c) 2024, Red Hat, Inc. All rights reserved.
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
 */

package compiler.c2.irTests;

import compiler.lib.ir_framework.*;
import jdk.internal.misc.Unsafe;

/*
 * @test
 * @bug 8329077
 * @summary C2: MemorySegment double accesses don't vectorize
 * @modules java.base/jdk.internal.misc
 * @library /test/lib /
 * @run driver compiler.c2.irTests.TestVectorizedUnsafeLoadStore
 */

public class TestVectorizedUnsafeLoadStore {
    private static final Unsafe UNSAFE = Unsafe.getUnsafe();

    public static void main(String[] args) {
        TestFramework.runWithFlags("--add-modules", "java.base", "--add-exports", "java.base/jdk.internal.misc=ALL-UNNAMED");
    }

    @Test
    @IR(counts = {IRNode.LOAD_VECTOR_D,  " >0 ", IRNode.STORE_VECTOR,  " >0 "})
    public static void test1(double[] src, double[] dst) {
        for (int i = 0; i < src.length; i++) {
            dst[i] = src[i];
        }
    }

    @Run(test = "test1")
    public static void test1_runner() {
        double[] src = new double[1024];
        double[] dst = new double[1024];
        test1(src, dst);
    }

    @Test
    @IR(counts = {IRNode.LOAD_VECTOR_D,  " >0 ", IRNode.STORE_VECTOR,  " >0 "})
    public static void test2(double[] src, double[] dst) {
        for (int i = 0; i < src.length; i++) {
            double v = UNSAFE.getDouble(src, UNSAFE.ARRAY_DOUBLE_BASE_OFFSET + i * UNSAFE.ARRAY_DOUBLE_INDEX_SCALE);
            UNSAFE.putDouble(dst, UNSAFE.ARRAY_DOUBLE_BASE_OFFSET + i * UNSAFE.ARRAY_DOUBLE_INDEX_SCALE, v);
        }
    }

    @Run(test = "test2")
    public static void test2_runner() {
        double[] src = new double[1024];
        double[] dst = new double[1024];
        test2(src, dst);
    }

    @Test
    @IR(counts = {IRNode.LOAD_VECTOR_D,  " >0 ", IRNode.STORE_VECTOR,  " >0 "})
    public static void test3(double[] src, double[] dst) {
        for (int i = 0; i < src.length; i++) {
            long v = UNSAFE.getLong(src, UNSAFE.ARRAY_DOUBLE_BASE_OFFSET + i * UNSAFE.ARRAY_DOUBLE_INDEX_SCALE);
            UNSAFE.putDouble(dst, UNSAFE.ARRAY_DOUBLE_BASE_OFFSET + i * UNSAFE.ARRAY_DOUBLE_INDEX_SCALE, Double.longBitsToDouble(v));
        }
    }

    @Run(test = "test3")
    public static void test3_runner() {
        double[] src = new double[1024];
        double[] dst = new double[1024];
        test3(src, dst);
    }
}
