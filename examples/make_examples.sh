#!/usr/bin/env bash

# usage: . make_examples.sh <build?>
# where if build? is y/yes we call mvn package, and OW do not
# Must be using java8

if [[ "$#" -ge 1 ]] ; then
    build_arg=`echo $1 | tr '[:upper:]' '[:lower:]'`;  # convert to lowercase
    if [[ $build_arg == "y" ]] || [[ $build_arg == "yes" ]] ; then
        echo "** Building package";
        cd ..;
        mvn package -Dmaven.test.skip=true ;
        cd examples;
        echo "** Package built";
    fi
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

echo "** Building examples from ${SOURCE_DIR} into ${BUILD_DIR}";
find ${SOURCE_DIR} -type f -name "*.java" | xargs javac -d ${BUILD_DIR};
echo "** Done building"; echo;

# Run Ranjit's algorithm on test dirs
for targetFile in `find ${SOURCE_DIR} -type f -name "targets.txt"`; do 
    CLASS_NAME=`cat ${targetFile}`;
    echo "** Running Ranjit's algorithm on ${CLASS_NAME}";
    # Assume ${JAVA_HOME} is set up correctly for this to work
    LD_LIBRARY_PATH="${PATH_TO_Z3}" \
        java -Dorg.slf4j.simpleLogger.defaultLogLevel=${LOG_LEVEL} \
             -Djava.library.path="${PATH_TO_Z3}" \
             -jar "${JAR}" ${targetFile} -- -d ${OUT_DIR} -f jimple -cp ${JIMPLE_CP} -pp;
    echo "** Jimple file in directory ${OUT_DIR}"; echo
done
