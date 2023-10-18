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
import jdk.test.whitebox.gc.GC;
import java.util.ArrayList;
import java.lang.reflect.Method;
import java.net.URLClassLoader;
import java.net.URL;
import java.nio.file.Paths;
import java.net.MalformedURLException;

/*
 * @test
 * @library /test/lib /
 * @compile --enable-preview -source ${jdk.version} TestScopedValue.java
 * @run main/othervm --enable-preview compiler.c2.irTests.TestScopedValue
 */

public class TestScopedValue {

    static ScopedValue<MyLong> sv = ScopedValue.newInstance();
    static final ScopedValue<MyLong> svFinal = ScopedValue.newInstance();
    
    public static void main(String[] args) {
        TestFramework.runWithFlags("--enable-preview");
    }
    
    // @IR(counts = {IRNode.LOAD_L, "1" })
    // hits in the cache
    @Test
    @IR(failOn = {IRNode.CALL_OF_METHOD, "slowGet", IRNode.INTRINSIC_TRAP})
    public static long test1() throws Exception {
        MyLong sv1 = (MyLong)get1.invoke(sv);
        MyLong sv2 = (MyLong)get1.invoke(sv);
        return sv1.getValue() + sv2.getValue();
    }

    @Run(test = "test1")
    @Warmup(1)
    private void test1Runner() {
        ScopedValue.where(sv, new MyLong(42)).run(
                () -> {
                    try {
                        MyLong unused = (MyLong)get1.invoke(sv);
                        for (int i = 0; i < 20_000; i++) {
                            if (test1() != 42 + 42) {
                                throw new RuntimeException();
                            }
                        }
                    } catch (Exception e) {}
                });
    }


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
