#!/usr/bin/env bash

# usage: . make_examples.sh -b/--build -dz/--debugz3
# where if build we call mvn package, and OW do not
# where if debugz3 we set LOG_Z3 to true, otherwise false
# Must be using java8

BUILD=false;
DEBUG_Z3="";

# parse arguments following
# https://stackoverflow.com/questions/192249/how-do-i-parse-command-line-arguments-in-bash
while [[ $# -gt 0 ]]; do
    key="$1"
    case $key in
        -b|--build)
            BUILD=true;
            shift # past arg
            ;;
        -dz|--debugz3)
           DEBUG_Z3=" -debugZ3";
           shift
           ;;
   esac
done


if [[ $BUILD = true ]] ; then
    echo "** clean installing package ";
    cd ..;
    mvn clean install -Dmaven.test.skip=true ;
    cd examples;
    echo "** Package built";
fi

# one of "trace" "debug" "info" "warn" "error" "off"
LOG_LEVEL="debug";
# build holds .class files of examplaes
BUILD_DIR=`realpath "build/"`;
# holds source of examples
SOURCE_DIR=`realpath "."`;
# where to leave jimple files
OUT_DIR=`realpath "./modifiedClasses"`;
PATH_TO_Z3=`realpath "/usr/lib/"`;
JAR=`realpath "../target/lockPlacementBenchmarks-0.0.1-SNAPSHOT.jar"`;

# build jimple classpath
JIMPLE_CP="${BUILD_DIR}:`realpath "../target/classes"`";

# Build source 
if [ ! -d "${BUILD_DIR}" ]; then
    mkdir "${BUILD_DIR}";
fi

echo "** Building examples and common.aux from ${SOURCE_DIR} into ${BUILD_DIR}";
find ${SOURCE_DIR} -type f -name "*.java" | xargs javac -d ${BUILD_DIR};
echo "** Done building"; echo;

# Run Ranjit's algorithm on test dirs
for targetFile in `find ${SOURCE_DIR} -type f -name "targets.txt" -not -wholename "${SOURCE_DIR}/common/*"`; do 
    CLASS_NAME=`cat ${targetFile}`;
    echo "** Running Ranjit's algorithm on ${CLASS_NAME}";
    # Assume ${JAVA_HOME} is set up correctly for this to work
    LD_LIBRARY_PATH="${PATH_TO_Z3}" \
        java -Dorg.slf4j.simpleLogger.defaultLogLevel=${LOG_LEVEL} \
             -Djava.library.path="${PATH_TO_Z3}" \
             -jar "${JAR}" ${targetFile} ${DEBUG_Z3} \
                           -- -d ${OUT_DIR} -f jimple -cp ${JIMPLE_CP} -pp;
    echo "** Jimple file in directory ${OUT_DIR}"; echo
done
