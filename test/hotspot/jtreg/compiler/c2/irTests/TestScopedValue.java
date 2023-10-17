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

/*
 * @test
 * @library /test/lib /
 * @compile --enable-preview -source ${jdk.version} TestScopedValue.java
 * @run main/othervm --enable-preview compiler.c2.irTests.TestScopedValue
 */

public class TestScopedValue {

    static ScopedValue<Long> sv = ScopedValue.newInstance();
    static final ScopedValue<Long> svFinal = ScopedValue.newInstance();
    
    public static void main(String[] args) {
        TestFramework.runWithFlags("--enable-preview");
    }
    
    // hits in the cache
    @Test
    public static long test1() {
        Long sv1 = sv.get();
        Long sv2 = sv.get();
        return sv1 + sv2;
    }

    @Run(test = "test1")
    @Warmup(1)
    private void test1Runner() {
        ScopedValue.where(sv, 42L).run(
                () -> {
                    Long unused = sv.get();
                    for (int i = 0; i < 20_000; i++) {
                        if (test1() != 42 + 42) {
                            throw new RuntimeException();
                        }
                    }
                });
    }
}
