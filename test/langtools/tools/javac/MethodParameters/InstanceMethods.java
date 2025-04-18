/*
 * Copyright (c) 2013, 2024, Oracle and/or its affiliates. All rights reserved.
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
 * @bug 8006582
 * @summary javac should generate method parameters correctly.
 * @build MethodParametersTester ClassFileVisitor ReflectionVisitor
 * @compile -parameters InstanceMethods.java
 * @run main MethodParametersTester InstanceMethods InstanceMethods.out
 */

public class InstanceMethods {
    public void empty() {}
    final void def(Object a, final Object ba, final String... cba) { }
    final public void pub(Object d, final Object ed, final String... fed) { }
    protected boolean prot(Object g, final Object hg, final String... ihg) { return true; }
    private boolean priv(Object j, final Object kj, final String... lkj) { return true; }
    void def(int A, Object BA, final Object CBA, final String... DCBA) { }
    public void pub(int B, Object CB, final Object DCB, final String... EDCB) { }
    final protected boolean prot(int C, Object DC, final Object EDC, final String... FEDC) { return true; }
    final private boolean priv(int D, Object ED, final Object FED, final String... GFED) { return true; }
}



