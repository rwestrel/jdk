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

/*
 * @test
 * @library /test/lib /
 * @run driver jdk.test.lib.helpers.ClassFileInstaller jdk.test.whitebox.WhiteBox
 * @compile --enable-preview -source ${jdk.version} TestScopedValue.java
 * @run main/othervm --enable-preview -Xbootclasspath/a:. -XX:+UnlockDiagnosticVMOptions -XX:+WhiteBoxAPI compiler.c2.irTests.TestScopedValue
 */

public class TestScopedValue {

    protected static final WhiteBox WHITE_BOX = WhiteBox.getWhiteBox();

    static ScopedValue<MyLong> sv = ScopedValue.newInstance();
    static ScopedValue<MyLong> sv2 = ScopedValue.newInstance();
    static final ScopedValue<MyLong> svFinal = ScopedValue.newInstance();
    
    public static void main(String[] args) {
        TestFramework.runWithFlags("--enable-preview", "-XX:CompileCommand=dontinline,java.lang.ScopedValue::slowGet");
    }
    
    // @Test
    // @IR(failOn = {IRNode.CALL_OF_METHOD, "slowGet"})
    // @IR(counts = {IRNode.LOAD_L, "1" })
    // public static long test1() throws Exception {
    //     MyLong sv1 = (MyLong)sv.get();
    //     MyLong sv2 = (MyLong)sv.get();
    //     return sv1.getValue() + sv2.getValue();
    // }

    // @Run(test = "test1", mode = RunMode.STANDALONE)
    // private void test1Runner() throws Exception {
    //     ScopedValue.where(sv, new MyLong(42)).run(
    //             () -> {
    //                 try {
    //                     MyLong unused = (MyLong)sv.get();
    //                     for (int i = 0; i < 20_000; i++) {
    //                         if (test1() != 42 + 42) {
    //                             throw new RuntimeException();
    //                         }
    //                     }
    //                 } catch(Exception ex) {}
    //             });
    //     Method m = TestScopedValue.class.getDeclaredMethod("test1");
    //     WHITE_BOX.enqueueMethodForCompilation(m, CompilerWhiteBoxTest.COMP_LEVEL_FULL_OPTIMIZATION);
    //     if (!WHITE_BOX.isMethodCompiled(m) || WHITE_BOX.getMethodCompilationLevel(m) != CompilerWhiteBoxTest.COMP_LEVEL_FULL_OPTIMIZATION) {
    //         throw new RuntimeException("should be compiled");
    //     }
    // }

    @DontInline
    static void notInlined() {
    }
    
    // @Test
    // @IR(failOn = {IRNode.CALL_OF_METHOD, "slowGet"})
    // @IR(counts = {IRNode.LOAD_L, "1" })
    // public static long test2() throws Exception {
    //     ScopedValue<MyLong> scopedValue = sv;
    //     MyLong sv1 = (MyLong)scopedValue.get();
    //     notInlined();
    //     MyLong sv2 = (MyLong)scopedValue.get();
    //     return sv1.getValue() + sv2.getValue();
    // }

    // @Run(test = "test2", mode = RunMode.STANDALONE)
    // private void test2Runner() throws Exception {
    //     ScopedValue.where(sv, new MyLong(42)).run(
    //             () -> {
    //                 try {
    //                     MyLong unused = (MyLong)sv.get();
    //                     for (int i = 0; i < 20_000; i++) {
    //                         if (test2() != 42 + 42) {
    //                             throw new RuntimeException();
    //                         }
    //                     }
    //                 } catch(Exception ex) {}
    //             });
    //     Method m = TestScopedValue.class.getDeclaredMethod("test2");
    //     WHITE_BOX.enqueueMethodForCompilation(m, CompilerWhiteBoxTest.COMP_LEVEL_FULL_OPTIMIZATION);
    //     if (!WHITE_BOX.isMethodCompiled(m) || WHITE_BOX.getMethodCompilationLevel(m) != CompilerWhiteBoxTest.COMP_LEVEL_FULL_OPTIMIZATION) {
    //         throw new RuntimeException("should be compiled");
    //     }
    // }

    // @Test
    // @IR(failOn = {IRNode.CALL_OF_METHOD, "slowGet"})
    // @IR(counts = {IRNode.LOAD_L, "2" })
    // public static long test3() throws Exception {
    //     MyLong sv1 = (MyLong)sv.get();
    //     notInlined();
    //     MyLong sv2 = (MyLong)sv.get();
    //     return sv1.getValue() + sv2.getValue();
    // }

    // @Run(test = "test3", mode = RunMode.STANDALONE)
    // private void test3Runner() throws Exception {
    //     ScopedValue.where(sv, new MyLong(42)).run(
    //             () -> {
    //                 try {
    //                     MyLong unused = (MyLong)sv.get();
    //                     for (int i = 0; i < 20_000; i++) {
    //                         if (test3() != 42 + 42) {
    //                             throw new RuntimeException();
    //                         }
    //                     }
    //                 } catch(Exception ex) {}
    //             });
    //     Method m = TestScopedValue.class.getDeclaredMethod("test3");
    //     WHITE_BOX.enqueueMethodForCompilation(m, CompilerWhiteBoxTest.COMP_LEVEL_FULL_OPTIMIZATION);
    //     if (!WHITE_BOX.isMethodCompiled(m) || WHITE_BOX.getMethodCompilationLevel(m) != CompilerWhiteBoxTest.COMP_LEVEL_FULL_OPTIMIZATION) {
    //         throw new RuntimeException("should be compiled");
    //     }
    // }

    // @Test
    // @IR(failOn = {IRNode.CALL_OF_METHOD, "slowGet"})
    // @IR(counts = {IRNode.LOAD_L, "1" })
    // public static long test4(boolean flag) throws Exception {
    //     ScopedValue<MyLong> scopedValue;
    //     MyLong long1;
    //     if (flag) {
    //         scopedValue = sv;
    //         long1 = (MyLong)sv.get();
    //     } else {
    //         scopedValue = sv2;
    //         long1 = (MyLong)sv2.get();
    //     }
    //     MyLong long2 = (MyLong)scopedValue.get();
    //     return long1.getValue() + long2.getValue();
    // }

    // @Run(test = "test4", mode = RunMode.STANDALONE)
    // private void test4Runner() throws Exception {
    //     ScopedValue.where(sv, new MyLong(42)).where(sv2, new MyLong(42)).run(
    //             () -> {
    //                 try {
    //                     MyLong unused = (MyLong)sv.get();
    //                     unused = (MyLong)sv2.get();
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
    @IR(failOn = {IRNode.CALL_OF_METHOD, "slowGet"})
    @IR(counts = {IRNode.LOAD_L, "1" })
    public static long test5() throws Exception {
        int res = 0;
        for (int i = 0; i < 10_000; i++) {
            res += sv.get().getValue();
        }
        return res;
    }

    @Run(test = "test5", mode = RunMode.STANDALONE)
    private void test5Runner() throws Exception {
        ScopedValue.where(sv, new MyLong(42)).where(sv2, new MyLong(42)).run(
                () -> {
                    try {
                        MyLong unused = (MyLong)sv.get();
                        for (int i = 0; i < 20_000; i++) {
                            if (test5() != 42 * 10_000) {
                                throw new RuntimeException();
                            }
                        }
                    } catch(Exception ex) {}
                });
        Method m = TestScopedValue.class.getDeclaredMethod("test5");
        WHITE_BOX.enqueueMethodForCompilation(m, CompilerWhiteBoxTest.COMP_LEVEL_FULL_OPTIMIZATION);
        if (!WHITE_BOX.isMethodCompiled(m) || WHITE_BOX.getMethodCompilationLevel(m) != CompilerWhiteBoxTest.COMP_LEVEL_FULL_OPTIMIZATION) {
            throw new RuntimeException("should be compiled");
        }
    }

    // @Test
    // @IR(counts = {IRNode.CALL_OF_METHOD, "slowGet", "2"})
    // public static long test2() {
    //     MyLong sv1 = sv.get();
    //     MyLong sv2 = sv.get();
    //     return sv1.getValue() + sv2.getValue();
    // }

    // @Run(test = "test2")
    // private void test2Runner() throws Exception {
    //     ScopedValue.where(sv, new MyLong(42)).run(
    //             () -> {
    //                 if (test2() != 42 + 42) {
    //                     throw new RuntimeException();
    //                 }
    //             });
    // }


    static class MyLong {
        private long value;
        
        public MyLong(long value) {
            this.value = value;
        }

        @ForceInline
        public long getValue() {
            return value;
        }
    }

    public static ClassLoader newClassLoader() {
        try {
            return new URLClassLoader(new URL[] {
                    Paths.get(System.getProperty("test.classes",".")).toUri().toURL(),
            }, null);
        } catch (MalformedURLException e){
            throw new RuntimeException("Unexpected URL conversion failure", e);
        }
    }

    static final Method get1 = getMethod();

    static Method getMethod() {
        Method res = null;
        try {
            res = newClassLoader().loadClass("java.lang.ScopedValue").getDeclaredMethod("get");
        } catch (Throwable t) {
            System.out.println("XXX exception! " + t);
        }
        return res;
    }

}
