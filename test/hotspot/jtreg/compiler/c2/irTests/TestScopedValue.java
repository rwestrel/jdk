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

package compiler.c2.irTests;

import compiler.lib.ir_framework.*;
import jdk.test.whitebox.WhiteBox;
import java.lang.reflect.Method;
import compiler.whitebox.CompilerWhiteBoxTest;
import java.net.MalformedURLException;
import java.net.URL;
import java.net.URLClassLoader;
import java.nio.file.Paths;
import java.util.Arrays;
import java.util.List;

/*
 * @test
 * @library /test/lib /
 * @build jdk.test.whitebox.WhiteBox
  * @run driver jdk.test.lib.helpers.ClassFileInstaller jdk.test.whitebox.WhiteBox
 * @compile --enable-preview -source ${jdk.version} TestScopedValue.java
 * @run main/othervm --enable-preview -Xbootclasspath/a:. -XX:+UnlockDiagnosticVMOptions -XX:+WhiteBoxAPI compiler.c2.irTests.TestScopedValue
 */

public class TestScopedValue {

    protected static final WhiteBox WHITE_BOX = WhiteBox.getWhiteBox();

    static ScopedValue<MyLong> sv = ScopedValue.newInstance();
    static ScopedValue<MyLong> sv2 = ScopedValue.newInstance();
    static final ScopedValue<MyLong> svFinal = ScopedValue.newInstance();
    static final ScopedValue<MyLong> svFinal2 = ScopedValue.newInstance();
    static ScopedValue<Object> sv3 = ScopedValue.newInstance();
    
    public static void main(String[] args) {
        List<String> tests = List.of("testFastPath1", "testFastPath2", "testFastPath3", "testFastPath5", "testFastPath6", "testFastPath7", "testFastPath8", "testFastPath9",
                                     "testSlowPath1,testSlowPath2,testSlowPath3,testSlowPath4,testSlowPath5");
        for (String test : tests) {
            TestFramework.runWithFlags("--enable-preview", "-XX:CompileCommand=dontinline,java.lang.ScopedValue::slowGet", "-DTest=" + test);
        }
    }
    
    @Test
    @IR(failOn = {IRNode.CALL_OF_METHOD, "slowGet"})
    @IR(counts = {IRNode.LOAD_L, "1" })
    public static long testFastPath1() {
        MyLong sv1 = (MyLong)sv.get();
        MyLong sv2 = (MyLong)sv.get();
        return sv1.getValue() + sv2.getValue();
    }

    @Run(test = "testFastPath1", mode = RunMode.STANDALONE)
    private void testFastPath1Runner() throws Exception {
        ScopedValue.where(sv, new MyLong(42)).run(
                () -> {
                    MyLong unused = (MyLong)sv.get();
                    for (int i = 0; i < 20_000; i++) {
                        if (testFastPath1() != 42 + 42) {
                            throw new RuntimeException();
                        }
                    }
                });
        Method m = TestScopedValue.class.getDeclaredMethod("testFastPath1");
        WHITE_BOX.enqueueMethodForCompilation(m, CompilerWhiteBoxTest.COMP_LEVEL_FULL_OPTIMIZATION);
        if (!WHITE_BOX.isMethodCompiled(m) || WHITE_BOX.getMethodCompilationLevel(m) != CompilerWhiteBoxTest.COMP_LEVEL_FULL_OPTIMIZATION) {
            throw new RuntimeException("should be compiled");
        }
    }

    @DontInline
    static void notInlined() {
    }
    
    @Test
    @IR(failOn = {IRNode.CALL_OF_METHOD, "slowGet"})
    @IR(counts = {IRNode.LOAD_L, "1" })
    public static long testFastPath2() {
        ScopedValue<MyLong> scopedValue = sv;
        MyLong sv1 = (MyLong)scopedValue.get();
        notInlined();
        MyLong sv2 = (MyLong)scopedValue.get();
        return sv1.getValue() + sv2.getValue();
    }

    @Run(test = "testFastPath2", mode = RunMode.STANDALONE)
    private void testFastPath2Runner() throws Exception {
        ScopedValue.where(sv, new MyLong(42)).run(
                () -> {
                    MyLong unused = (MyLong)sv.get();
                    for (int i = 0; i < 20_000; i++) {
                        if (testFastPath2() != 42 + 42) {
                            throw new RuntimeException();
                        }
                    }
                });
        Method m = TestScopedValue.class.getDeclaredMethod("testFastPath2");
        WHITE_BOX.enqueueMethodForCompilation(m, CompilerWhiteBoxTest.COMP_LEVEL_FULL_OPTIMIZATION);
        if (!WHITE_BOX.isMethodCompiled(m) || WHITE_BOX.getMethodCompilationLevel(m) != CompilerWhiteBoxTest.COMP_LEVEL_FULL_OPTIMIZATION) {
            throw new RuntimeException("should be compiled");
        }
    }

    @Test
    @IR(failOn = {IRNode.CALL_OF_METHOD, "slowGet"})
    @IR(counts = {IRNode.LOAD_L, "2" })
    public static long testFastPath3() {
        MyLong sv1 = (MyLong)sv.get();
        notInlined();
        MyLong sv2 = (MyLong)sv.get();
        return sv1.getValue() + sv2.getValue();
    }

    @Run(test = "testFastPath3", mode = RunMode.STANDALONE)
    private void testFastPath3Runner() throws Exception {
        ScopedValue.where(sv, new MyLong(42)).run(
                () -> {
                    MyLong unused = (MyLong)sv.get();
                    for (int i = 0; i < 20_000; i++) {
                        if (testFastPath3() != 42 + 42) {
                            throw new RuntimeException();
                        }
                    }
                });
        Method m = TestScopedValue.class.getDeclaredMethod("testFastPath3");
        WHITE_BOX.enqueueMethodForCompilation(m, CompilerWhiteBoxTest.COMP_LEVEL_FULL_OPTIMIZATION);
        if (!WHITE_BOX.isMethodCompiled(m) || WHITE_BOX.getMethodCompilationLevel(m) != CompilerWhiteBoxTest.COMP_LEVEL_FULL_OPTIMIZATION) {
            throw new RuntimeException("should be compiled");
        }
    }

    // @Test
    // @IR(failOn = {IRNode.CALL_OF_METHOD, "slowGet"})
    // @IR(counts = {IRNode.LOAD_L, "2" })
    // public static long test4(boolean flag) throws Exception {
    //     ScopedValue<MyLong> scopedValue;
    //     MyLong long1;
    //     if (flag) {
    //         scopedValue = svFinal;
    //         long1 = (MyLong)svFinal.get();
    //     } else {
    //         scopedValue = svFinal2;
    //         long1 = (MyLong)svFinal2.get();
    //     }
    //     MyLong long2 = (MyLong)scopedValue.get();
    //     return long1.getValue() + long2.getValue();
    // }

    // @Run(test = "test4", mode = RunMode.STANDALONE)
    // private void test4Runner() throws Exception {
    //     ScopedValue.where(svFinal, new MyLong(42)).where(svFinal2, new MyLong(42)).run(
    //             () -> {
    //                 try {
    //                     MyLong unused = (MyLong)svFinal.get();
    //                     unused = (MyLong)svFinal2.get();
    //                     for (int i = 0; i < 20_000; i++) {
    //                         if (test4(true) != 42 + 42) {
    //                             throw new RuntimeException();
    //                         }
    //                         if (test4(false) != 42 + 42) {
    //                             throw new RuntimeException();
    //                         }
    //                     }
    //                 } catch(Exception ex) {}
    //             });
    //     Method m = TestScopedValue.class.getDeclaredMethod("test4", boolean.class);
    //     WHITE_BOX.enqueueMethodForCompilation(m, CompilerWhiteBoxTest.COMP_LEVEL_FULL_OPTIMIZATION);
    //     if (!WHITE_BOX.isMethodCompiled(m) || WHITE_BOX.getMethodCompilationLevel(m) != CompilerWhiteBoxTest.COMP_LEVEL_FULL_OPTIMIZATION) {
    //         throw new RuntimeException("should be compiled");
    //     }
    // }

    @Test
    @IR(failOn = {IRNode.CALL_OF_METHOD, "slowGet", IRNode.LOOP})
    @IR(counts = {IRNode.LOAD_L, "1" })
    public static long testFastPath5() {
        long res = 0;
        for (int i = 0; i < 10_000; i++) {
            res = sv.get().getValue();
        }
        return res;
    }

    @Run(test = "testFastPath5", mode = RunMode.STANDALONE)
    private void testFastPath5Runner() throws Exception {
        ScopedValue.where(sv, new MyLong(42)).run(
                () -> {
                    MyLong unused = (MyLong)sv.get();
                    for (int i = 0; i < 20_000; i++) {
                        if (testFastPath5() != 42) {
                            throw new RuntimeException();
                        }
                    }
                });
        Method m = TestScopedValue.class.getDeclaredMethod("testFastPath5");
        WHITE_BOX.enqueueMethodForCompilation(m, CompilerWhiteBoxTest.COMP_LEVEL_FULL_OPTIMIZATION);
        if (!WHITE_BOX.isMethodCompiled(m) || WHITE_BOX.getMethodCompilationLevel(m) != CompilerWhiteBoxTest.COMP_LEVEL_FULL_OPTIMIZATION) {
            throw new RuntimeException("should be compiled");
        }
    }

    @Test
    @IR(failOn = {IRNode.CALL_OF_METHOD, "slowGet"})
    @IR(counts = {IRNode.IF, "1", IRNode.LOAD_P_OR_N, "1" })
    public static void testFastPath6() {
        Object unused = sv3.get();
    }

    @Run(test = "testFastPath6", mode = RunMode.STANDALONE)
    private void testFastPath6Runner() throws Exception {
        ScopedValue.where(sv3, new Object()).run(
                () -> {
                    Object unused = sv3.get();
                    for (int i = 0; i < 20_000; i++) {
                        testFastPath6();
                    }
                });
        Method m = TestScopedValue.class.getDeclaredMethod("testFastPath6");
        WHITE_BOX.enqueueMethodForCompilation(m, CompilerWhiteBoxTest.COMP_LEVEL_FULL_OPTIMIZATION);
        if (!WHITE_BOX.isMethodCompiled(m) || WHITE_BOX.getMethodCompilationLevel(m) != CompilerWhiteBoxTest.COMP_LEVEL_FULL_OPTIMIZATION) {
            throw new RuntimeException("should be compiled");
        }
    }

    static Object testFastPath7Field;
    @ForceInline
    static void testFastPath7Helper(int i, Object o) {
        if (i != 10) {
            testFastPath7Field = o;
        }
    }
    
    @Test
    @IR(failOn = {IRNode.CALL_OF_METHOD, "slowGet"})
    @IR(counts = {IRNode.IF, "1", IRNode.LOAD_P_OR_N, "1" })
    public static void testFastPath7() {
        Object unused = sv3.get();
        int i;
        for (i = 0; i < 10; i++);
        testFastPath7Helper(i, unused);
    }

    @Run(test = "testFastPath7", mode = RunMode.STANDALONE)
    private void testFastPath7Runner() throws Exception {
        ScopedValue.where(sv3, new Object()).run(
                () -> {
                    Object unused = sv3.get();
                    for (int i = 0; i < 20_000; i++) {
                        testFastPath7();
                        testFastPath7Helper(9, null);
                    }
                });
        Method m = TestScopedValue.class.getDeclaredMethod("testFastPath7");
        WHITE_BOX.enqueueMethodForCompilation(m, CompilerWhiteBoxTest.COMP_LEVEL_FULL_OPTIMIZATION);
        if (!WHITE_BOX.isMethodCompiled(m) || WHITE_BOX.getMethodCompilationLevel(m) != CompilerWhiteBoxTest.COMP_LEVEL_FULL_OPTIMIZATION) {
            throw new RuntimeException("should be compiled");
        }
    }

    @Test
    @IR(failOn = {IRNode.CALL_OF_METHOD, "slowGet", IRNode.LOOP, IRNode.COUNTED_LOOP})
    @IR(counts = {IRNode.LOAD_L, "1" })
    public static long testFastPath8(boolean[] flags) {
        long res = 0;
        for (int i = 0; i < 10_000; i++) {
            if (flags[i]) {
                res = sv.get().getValue();
            } else {
                res = sv.get().getValue();
            }
        }
        return res;
    }

    @Run(test = "testFastPath8", mode = RunMode.STANDALONE)
    private void testFastPath8Runner() throws Exception {
        boolean[] allTrue = new boolean[10_000];
        Arrays.fill(allTrue, true);
        boolean[] allFalse = new boolean[10_000];
        ScopedValue.where(sv, new MyLong(42)).run(
                () -> {
                    MyLong unused = (MyLong)sv.get();
                    for (int i = 0; i < 20_000; i++) {
                        if (testFastPath8(allTrue) != 42) {
                            throw new RuntimeException();
                        }
                        if (testFastPath8(allFalse) != 42) {
                            throw new RuntimeException();
                        }
                    }
                });
        Method m = TestScopedValue.class.getDeclaredMethod("testFastPath8", boolean[].class);
        WHITE_BOX.enqueueMethodForCompilation(m, CompilerWhiteBoxTest.COMP_LEVEL_FULL_OPTIMIZATION);
        if (!WHITE_BOX.isMethodCompiled(m) || WHITE_BOX.getMethodCompilationLevel(m) != CompilerWhiteBoxTest.COMP_LEVEL_FULL_OPTIMIZATION) {
            throw new RuntimeException("should be compiled");
        }
    }

    @Test
    @IR(failOn = {IRNode.CALL_OF_METHOD, "slowGet"})
    @IR(counts = {IRNode.LOAD_L, "1" })
    public static long testFastPath9(boolean[] flags) {
        long res = 0;
        for (int i = 0; i < 10_000; i++) {
            notInlined();
            if (flags[i]) {
                res = svFinal.get().getValue();
            } else {
                res = svFinal.get().getValue();
            }
        }
        return res;
    }

    @Run(test = "testFastPath9", mode = RunMode.STANDALONE)
    private void testFastPath9Runner() throws Exception {
        boolean[] allTrue = new boolean[10_000];
        Arrays.fill(allTrue, true);
        boolean[] allFalse = new boolean[10_000];
        ScopedValue.where(svFinal, new MyLong(42)).run(
                () -> {
                    MyLong unused = (MyLong)svFinal.get();
                    for (int i = 0; i < 20_000; i++) {
                        if (testFastPath9(allTrue) != 42) {
                            throw new RuntimeException();
                        }
                        if (testFastPath9(allFalse) != 42) {
                            throw new RuntimeException();
                        }
                    }
                });
        Method m = TestScopedValue.class.getDeclaredMethod("testFastPath9", boolean[].class);
        WHITE_BOX.enqueueMethodForCompilation(m, CompilerWhiteBoxTest.COMP_LEVEL_FULL_OPTIMIZATION);
        if (!WHITE_BOX.isMethodCompiled(m) || WHITE_BOX.getMethodCompilationLevel(m) != CompilerWhiteBoxTest.COMP_LEVEL_FULL_OPTIMIZATION) {
            throw new RuntimeException("should be compiled");
        }
    }

    @Test
    @IR(counts = {IRNode.LOAD_L, "1", IRNode.CALL_OF_METHOD, "slowGet", "1" })
    public static long testSlowPath1() {
        ScopedValue<MyLong> localSV = sv;
        MyLong sv1 = (MyLong)localSV.get();
        MyLong sv2 = (MyLong)localSV.get();
        return sv1.getValue() + sv2.getValue();
    }

    @Run(test = "testSlowPath1")
    private void testSlowPath1Runner() throws Exception {
        ScopedValue.where(sv, new MyLong(42)).run(
                () -> {
                    if (testSlowPath1() != 42 + 42) {
                        throw new RuntimeException();
                    }
                });
    }

    @Test
    @IR(counts = {IRNode.LOAD_L, "1", IRNode.CALL_OF_METHOD, "slowGet", "1" })
    public static long testSlowPath2() {
        ScopedValue<MyLong> localSV = sv;
        MyLong sv1 = (MyLong)localSV.get();
        notInlined();
        MyLong sv2 = (MyLong)localSV.get();
        return sv1.getValue() + sv2.getValue();
    }

    @Run(test = "testSlowPath2")
    private void testSlowPath2Runner() throws Exception {
        ScopedValue.where(sv, new MyLong(42)).run(
                () -> {
                    if (testSlowPath2() != 42 + 42) {
                        throw new RuntimeException();
                    }
                });
    }

    @Test
    @IR(failOn = {IRNode.CALL_OF_METHOD, "slowGet"})
    @IR(counts = {IRNode.IF, "1", IRNode.LOAD_P_OR_N, "1" })
    public static void testSlowPath3() {
        Object unused = sv3.get();
    }

    @Run(test = "testSlowPath3")
    private void testSlowPath3Runner() throws Exception {
        ScopedValue.where(sv3, new Object()).run(
                () -> {
                    testSlowPath3();
                });
    }

    static Object testSlowPath4Field;
    @ForceInline
    static void testSlowPath4Helper(int i, Object o) {
        if (i != 10) {
            testSlowPath4Field = o;
        }
    }

    @Test
    @IR(failOn = {IRNode.CALL_OF_METHOD, "slowGet"})
    @IR(counts = {IRNode.IF, "1", IRNode.LOAD_P_OR_N, "1" })
    public static void testSlowPath4() {
        Object unused = sv3.get();
        int i;
        for (i = 0; i < 10; i++);
        testSlowPath4Helper(i, unused);
    }

    @Run(test = "testSlowPath4")
    private void testSlowPath4Runner() throws Exception {
        testSlowPath4Helper(9, null);
        ScopedValue.where(sv3, new Object()).run(
                () -> {
                    testSlowPath4();
                });
    }

    @Test
    @IR(failOn = {IRNode.LOOP, IRNode.COUNTED_LOOP})
    @IR(counts = {IRNode.LOAD_L, "1", IRNode.CALL_OF_METHOD, "slowGet", "1" })
    public static long testSlowPath5() {
        ScopedValue<MyLong> localSV = sv;
        long res = 0;
        for (int i = 0; i < 10_000; i++) {
            res = localSV.get().getValue();
        }
        return res;
    }

    @Run(test = "testSlowPath5")
    private void testSlowPath5Runner() throws Exception {
        ScopedValue.where(sv, new MyLong(42)).run(
                () -> {
                    if (testSlowPath5() != 42) {
                        throw new RuntimeException();
                    }
                });
    }

    static class MyLong {
        final private long value;
        
        public MyLong(long value) {
            this.value = value;
        }

        @ForceInline
        public long getValue() {
            return value;
        }
    }

}
