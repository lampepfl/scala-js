#! /bin/sh

if [ $# -eq 1 -a "$1" = "-x" ]; then
    CMD="sbt"
else
    echo "Showing commands that would be executed. Use -x to run."
    CMD="echo sbt"
fi

FULL_VERSIONS="2.11.0 2.11.1 2.11.2 2.11.4 2.11.5 2.11.6 2.11.7 2.11.8 2.11.11 2.11.12 2.12.1 2.12.2 2.12.3 2.12.4 2.13.0-M2"
BIN_VERSIONS="2.11.12 2.12.4 2.13.0-M2"
JVM_BIN_VERSIONS="2.10.7 2.11.12 2.12.4 2.13.0-M2"
SBT_VERSION="2.12.4"
SBT013_VERSION="2.10.7"
SBT013_SBTVERSION="0.13.17-RC2"

COMPILER="compiler jUnitPlugin"
LIBS="library irJS ioJS loggingJS linkerJS testInterface jUnitRuntime"
JVM_LIBS="ir io logging linker jsEnvs jsEnvsTestKit nodeJSEnv testAdapter stubs"

# Publish compiler
for v in $FULL_VERSIONS; do
    ARGS="++$v!"
    for p in $COMPILER; do
        ARGS="$ARGS $p/publishSigned"
    done
    $CMD $ARGS
done

# Publish libraries
for v in $BIN_VERSIONS; do
    ARGS="++$v!"
    for p in $LIBS; do
        ARGS="$ARGS $p/publishSigned"
    done
    $CMD $ARGS
done

# Publish JVM libraries
for v in $JVM_BIN_VERSIONS; do
    ARGS="++$v!"
    for p in $JVM_LIBS; do
        ARGS="$ARGS $p/publishSigned"
    done
    $CMD $ARGS
done

# Publish sbt-plugin
$CMD "++$SBT_VERSION!" "sbtPlugin/publishSigned"
$CMD "++$SBT013_VERSION!" "^^$SBT013_SBTVERSION" "sbtPlugin/publishSigned"
