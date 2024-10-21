/*
 * @test
 * @modules java.base/jdk.internal.misc:+open
 * @run main/othervm -XX:-BackgroundCompilation -XX:-UseOnStackReplacement -XX:-TieredCompilation TestRedundantSetMemory
 */

import jdk.internal.misc.Unsafe;

public class TestRedundantSetMemory {
    private static final Unsafe UNSAFE = Unsafe.getUnsafe();
    private static long offHeapLength = 1024;
    private static long offHeapMemory = UNSAFE.allocateMemory(offHeapLength);

    public static void main(String[] args) {
        for (int i = 0; i < 20_000; i++) {
            UNSAFE.setMemory(null, offHeapMemory, offHeapLength, (byte)0);
            test1(offHeapMemory+1, offHeapLength-1);
        }
        UNSAFE.setMemory(null, offHeapMemory, offHeapLength, (byte)0);
        test1(offHeapMemory, offHeapLength);
        for (long i = 0; i < offHeapLength; i++) {
            if (UNSAFE.getByte(null, offHeapMemory + i) != -1) {
                throw new RuntimeException("failure");
            }
        }
    }

    static private void test1(long addr, long length) {
        UNSAFE.setMemory(null, addr, length, (byte)-1);
    }
}
