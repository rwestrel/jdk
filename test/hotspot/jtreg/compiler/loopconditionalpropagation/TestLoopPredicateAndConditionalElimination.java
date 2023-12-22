/*
 * Copyright (c) 2023, Red Hat, Inc. All rights reserved.
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

/*
 * @test
 * @bug 8275202
 * @summary C2: optimize out more redundant conditions
 * @run main/othervm -XX:-BackgroundCompilation -XX:-TieredCompilation -XX:-UseOnStackReplacement
 *                   -XX:CompileCommand=dontinline,TestLoopPredicateAndConditionalElimination::notInlined1
 *                   -XX:+IgnoreUnrecognizedVMOptions -XX:+LoopConditionalPropagationALot TestLoopPredicateAndConditionalElimination
 */

public class TestLoopPredicateAndConditionalElimination {
    private static volatile int volatileBarrier;
    private static float floatField;

    public static void main(String[] args) {
        float[] array = new float[1000];
        for (int i = 0; i < 20_000; i++) {
            test(false, 0);
            inlined1(0, array, 42, true, 0);
            inlined1(0, array, 2, true, 0);
        }
    }

    private static float test(boolean flag, int other) {
        float[] array = new float[1000];
        notInlined1(array);
        int j = 1;
        for (; j < 2; j *= 2) {
        }
        int k = 1;
        for (; k < 2; k *= 2) {
        }
        final float v = inlined1(k - 3, array, j, flag, other);
        return v;
    }

    private static float inlined1(int start, float[] array, int j, boolean flag, int other) {
        float v = 0;
        if (flag) {
            if (other < 0) {
            }
            volatileBarrier = 42;
            if (start < other) {
            }
            for (int i = start; i < 1000; i++) {
                v = array[i];
                if (j == 2) {
                    break;
                }
            }
        } else {
            volatileBarrier = 42;
            v = floatField;
        }
        return v;
    }

    private static void notInlined1(float[] array) {
    }
}
