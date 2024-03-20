/*
 * @test
 * @modules java.base/jdk.internal.misc:+open
 * @run main/othervm  -XX:-BackgroundCompilation -XX:-TieredCompilation TestProfileContext
 *
 */

import jdk.internal.misc.ProfileContext;

public class TestProfileContext {
    static public void main(String[] args) {
        ProfileContext pc1 = ProfileContext.acquire();
        ProfileContext pc2 = ProfileContext.acquire();
        A a = new A();
        B b = new B();
        C c = new C();
        D d = new D();
        for (int i = 0; i < 20_000; i++) {
            test1(b);
            test1(a);
            pc1.run(() -> test1(c));
            pc2.run(() -> test1(d));
        }
    }

    static void test1(A a) {
        for (int i = 0; i < 100; i++) {
            a.m();
        }
    }

    static class A {
        void m() {
        }
    }

    static class B extends A {
        void m() {
        }
    }

    static class C extends A {
        void m() {
        }
    }

    static class D extends A {
        void m() {
        }
    }
}
