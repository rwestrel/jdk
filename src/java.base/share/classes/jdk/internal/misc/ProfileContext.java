package jdk.internal.misc;

public final class ProfileContext {
    static long uniqueContext;
    long context;

    ProfileContext(long context) {
        this.context = context;
    }

    public void run(Runnable op) {
        long currentContext = getProfileContext();
        setProfileContext(context);
        try {
            op.run();
        } finally {
            setProfileContext(currentContext);
        }
    }

    private native void setProfileContext(long context);

    private native long getProfileContext();

    static synchronized public ProfileContext acquire() {
        uniqueContext++;
        return new ProfileContext(uniqueContext);
    }

    static {
        initialize();
    }
    private static native void initialize();
}
