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
 */

package compiler.c2.irTests;

import compiler.lib.ir_framework.*;
import java.util.Objects;

/*
 * @test
 * @library /test/lib /
 * @run driver compiler.c2.irTests.TestLoopConditionalPropagation
 */

public class TestLoopConditionalPropagation {
    public static void main(String[] args) {
        TestFramework.runWithFlags("-XX:-UseLoopPredicate");
    }
    
    @Test
    @IR(counts = {IRNode.IF,"1"})
    @Arguments({Argument.NUMBER_42})
    @Warmup(10_000)
    private void test1(int i) {
        if (i < 42) {
            throw new RuntimeException("never taken");
        }
        if (i < 10) { 
            throw new RuntimeException("never taken");
        }
    }

    @Test
    @IR(counts = {IRNode.IF,"3"})
    @Arguments({Argument.NUMBER_42,Argument.BOOLEAN_TOGGLE_FIRST_TRUE})
    @Warmup(10_000)
    private static void test2(int i, boolean flag) {
        if (flag) {
            if (i < 42) {
                throw new RuntimeException("never taken");
            }
        } else {
            if (i < 42) {
                throw new RuntimeException("never taken");
            }
        }
        if (i < 10) {
            throw new RuntimeException("never taken");
        }
    }


    @DontInline
    private static void notInlined() {

    }
    
    @Test
    @IR(counts = {IRNode.IF,"2"})
    @Arguments({Argument.NUMBER_42,Argument.BOOLEAN_TOGGLE_FIRST_TRUE})
    @Warmup(10_000)
    private static void test3(int i, boolean flag) {
        if (flag) {
            if (i < 42) {
                throw new RuntimeException("never taken");
            }
        } else {
            i = 100;
        }
        notInlined();
        if (i < 10) {
            throw new RuntimeException("never taken");
        }
    }


    static volatile int volatileField;
    
    @Test
    @IR(counts = {IRNode.IF,"3"})
    @Arguments({Argument.NUMBER_42,Argument.NUMBER_42})
    @Warmup(10_000)
    private static void test4(int i, int k) {
        if (i < 42) {
            throw new RuntimeException("never taken");
        }
        for (int j = 1; j < 4; j *= 2) {
            volatileField = 42;
            volatileField = 42;
            volatileField = 42;
            volatileField = 42;
            volatileField = 42;
            volatileField = 42;
            volatileField = 42;
            volatileField = 42;
            volatileField = 42;
            volatileField = 42;
            volatileField = 42;
            volatileField = 42;
            volatileField = 42;
            volatileField = 42;
            volatileField = 42;
            volatileField = 42;
            volatileField = 42;
            volatileField = 42;
            volatileField = 42;
            volatileField = 42;
            volatileField = 42;
            volatileField = 42;
            volatileField = 42;
            volatileField = 42;
            volatileField = 42;
            volatileField = 42;
            volatileField = 42;
            volatileField = 42;
            volatileField = 42;
            volatileField = 42;
            volatileField = 42;
            volatileField = 42;
            volatileField = 42;
            volatileField = 42;
            volatileField = 42;
            volatileField = 42;
            volatileField = 42;
            volatileField = 42;
            volatileField = 42;
            volatileField = 42;
            volatileField = 42;
            volatileField = 42;
            volatileField = 42;
            volatileField = 42;
            volatileField = 42;
            volatileField = 42;
            volatileField = 42;
            volatileField = 42;
            volatileField = 42;
            volatileField = 42;
            volatileField = 42;
            volatileField = 42;
            volatileField = 42;
            volatileField = 42;
            volatileField = 42;
            volatileField = 42;
            volatileField = 42;
            volatileField = 42;
            volatileField = 42;
            volatileField = 42;
            volatileField = 42;
            volatileField = 42;
            volatileField = 42;
            volatileField = 42;
            volatileField = 42;
            volatileField = 42;
            volatileField = 42;
            volatileField = 42;
            volatileField = 42;
            volatileField = 42;
            volatileField = 42;
            volatileField = 42;
            volatileField = 42;
            volatileField = 42;
            volatileField = 42;
            volatileField = 42;
            volatileField = 42;
            volatileField = 42;
            volatileField = 42;
            volatileField = 42;
            volatileField = 42;
            volatileField = 42;
            volatileField = 42;
            volatileField = 42;
            volatileField = 42;
            volatileField = 42;
            volatileField = 42;
            volatileField = 42;
            volatileField = 42;
            volatileField = 42;
            volatileField = 42;
            volatileField = 42;
            volatileField = 42;
            volatileField = 42;
            volatileField = 42;
            volatileField = 42;
            volatileField = 42;
            volatileField = 42;
            volatileField = 42;
            volatileField = 42;
            if (i < 10) {
                throw new RuntimeException("never taken");
            }
            if (k < 42) {
                throw new RuntimeException("never taken");
            }
            i = k;
        }
    }
    

    @Test
    @IR(counts = {IRNode.IF,"2"})
    @IR(failOn = {IRNode.ADDI,IRNode.MULI})
    @Arguments({Argument.NUMBER_42})
    @Warmup(10_000)
    private static int test5(int i) {
        if (i < 42) {
            throw new RuntimeException("never taken");
        }
        notInlined();
        if (i > 42) {
            throw new RuntimeException("never taken");
        }
        return (i + 5) * 100;
    }


    @Test
    @IR(counts = {IRNode.IF,"3"})
    @Arguments({Argument.NUMBER_42,Argument.NUMBER_42,Argument.NUMBER_42})
    @Warmup(10_000)
    private static void test6(int i, int j, int k) {
        if (i < 42) {
            throw new RuntimeException("never taken");
        }
        if (j < i) {
            throw new RuntimeException("never taken");
        }
        if (k < j) {
            throw new RuntimeException("never taken");
        }
        if (k < 10) {
            throw new RuntimeException("never taken");
        }
    }

    @Test
    @IR(counts = {IRNode.IF,"1"})
    @Arguments({Argument.NUMBER_42})
    @Warmup(10_000)
    private static void test7(int i) {
        if (i < 0 || i >= 43) {
            throw new RuntimeException("never taken");
        }
        if (i < -1) {
            throw new RuntimeException("never taken");
        }
    }

    @Test
    @IR(counts = {IRNode.IF,"1"})
    @Arguments({Argument.NUMBER_42})
    @Warmup(10_000)
    private static void test8(int i) {
        if (i < 0 || i >= 43) {
            throw new RuntimeException("never taken");
        }
        if (i > 42) {
            throw new RuntimeException("never taken");
        }
    }


    @Test
    @IR(counts = {IRNode.IF,"1"})
    @Arguments({Argument.NUMBER_42})
    @Warmup(10_000)
    private static void test9(long i) {
        if (i < 42) {
            throw new RuntimeException("never taken");
        }
        if (i < 10) {
            throw new RuntimeException("never taken");
        }
    }


    @Test
    @IR(counts = {IRNode.IF,"1"})
    @Arguments({Argument.NUMBER_42})
    @Warmup(10_000)
    private static void test10(int i) {
        if (i - 1 <= 0) {
            throw new RuntimeException("never taken");
        }
        if (i == 0) {
            throw new RuntimeException("never taken");
        }
    }

    @Test
    @IR(counts = {IRNode.IF,"1"})
    @Arguments({Argument.BOOLEAN_TOGGLE_FIRST_TRUE, Argument.NUMBER_42})
    @Warmup(10_000)
    private static void test11(boolean flag, int i) {
        if (i - 1 <= 0) {
            throw new RuntimeException("never taken");
        }
        if (flag) {
            if (i == 0) {
                throw new RuntimeException("never taken");
            }
        } else {
            if (i == 0) {
                throw new RuntimeException("never taken");
            }
        }
    }

    @Test
    @IR(counts = {IRNode.IF,"2"})
    @Arguments({Argument.NUMBER_42, Argument.NUMBER_42})
    @Warmup(10_000)
    private static void test12(int i, int j) {
        if (i < 42) {
            throw new RuntimeException("never taken");
        }
        // i >= 42
        if (i > j) {
            throw new RuntimeException("never taken");
        }
        // i <= j => j >= 42
        if (j < 10) {
            throw new RuntimeException("never taken");
        }
    }

}
