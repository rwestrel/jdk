package jdk.internal.misc;

public final class ProfileContext {
    static long uniqueContext;
    long context;

    ProfileContext(long context) {
        this.context = context;
    }

    // public void run(Runnable op) {
    //     long currentContext = getProfileContext();
    //     setProfileContext(context);
    //     try {
    //         op.run();
    //     } finally {
    //         setProfileContext(currentContext);
    //     }
    // }

    public void switchAndRun(Runnable op) {
        switchAndRun(context, op);
    }
    
    static native private void switchAndRun(long context, Runnable op);

    static private void run(Runnable op) {
        op.run();
    }

    // private native void setProfileContext(long context);

    // private native long getProfileContext();

    static synchronized public ProfileContext acquire() {
        uniqueContext++;
        return new ProfileContext(uniqueContext);
    }

    static {
        initialize();
    }
    private static native void initialize();
}
