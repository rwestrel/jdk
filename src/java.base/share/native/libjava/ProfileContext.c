#include "jni.h"
#include "jvm.h"

#include "jdk_internal_misc_ProfileContext.h"

static JNINativeMethod methods[] = {
    /* {"setProfileContext",           "(J)V",        (void *)&JVM_SetProfileContext}, */
    /* {"getProfileContext",           "()J",         (void *)&JVM_GetProfileContext}, */
  {"run",           "(JLjava/lang/Runnable;)V",         (void *)&JVM_ProfileContextRun}, 
};

JNIEXPORT void JNICALL
Java_jdk_internal_misc_ProfileContext_initialize(JNIEnv *env, jclass cls) {
    (*env)->RegisterNatives(env, cls,
                            methods, sizeof(methods)/sizeof(methods[0]));
}
