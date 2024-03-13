cmake_minimum_required(VERSION 3.9)

# For setting up agda2hs.
set(CMAKE_MODULE_PATH CMakeModulePath)
configure_file(CMakeModulePath/CMakeAgdaCompiler.cmake.in
               CMakeAgdaCompiler.cmake)
set(CMAKE_Agda_COMPILER /home/csimma/.cabal/bin/agda2hs)
set(CMAKE_Agda_COMPILER_ENV_VAR "")
set(CMAKE_Agda_SOURCE_FILE_EXTENSIONS agda)

# the language is given so that GNUInstallDirs knows where to install
project(Acorn LANGUAGES C)

#add_custom_command(OUTPUT hs/All.hs
#  COMMAND agda2hs -o hs src/All.agda
#)

#add_custom_command(OUTPUT obj/All.o
#  COMMAND ghc --make -ihs/ -odir obj -hidir hi -stubdir stub hs/All.hs
#  MAIN_DEPENDENCY hs/All.hs
#)

#add_library(Acorn obj/All.o)

#set_target_properties(Acorn PROPERTIES
#  LINKER_LANGUAGE C
#)

#add_subdirectory(obj)



#add_library(Acorn)
#add_subdirectory(${CMAKE_CURRENT_SOURCE_DIR}/src)

set (CABAL_BUILD_PATH ${CMAKE_CURRENT_SOURCE_DIR}/cabalbuild/build/x86_64-linux/ghc-9.2.8/acorn-0.1/build)

add_custom_command(OUTPUT hs
  COMMAND agda2hs -o ${CMAKE_CURRENT_SOURCE_DIR}/hs ${CMAKE_CURRENT_SOURCE_DIR}/src/All.agda
  COMMAND ${CMAKE_COMMAND} -E copy
      ${CMAKE_CURRENT_SOURCE_DIR}/src/Main.hs
      ${CMAKE_CURRENT_SOURCE_DIR}/hs/Main.hs
)

add_library(Acorn hs)
add_executable(AcornShell hs)

# "Linking" will consist of compiling things with ghc.
# This way, we ensure that there are no additional files and need to copy
# as it was when doing Haskell compilation in `add_custom_command` directives.
# And when running `sudo make install` after building,
# root won't need access to ghc.
set_target_properties(Acorn PROPERTIES
  LINKER_LANGUAGE Agda
)
set_target_properties(AcornShell PROPERTIES
  LINKER_LANGUAGE Agda
)
set(CMAKE_Agda_CREATE_STATIC_LIBRARY "ghc --make -ihs -odir obj -hidir hi -stubdir stub -staticlib -fPIC -o libAcorn.a hs/All.hs")
set(CMAKE_Agda_LINK_EXECUTABLE "ghc --make -ihs -odir obj -hidir hi -stubdir stub -o AcornShell hs/Main.hs")

# preparing the library to be used by other projects
# make cache variables for install destinations
include(GNUInstallDirs)
# now, we put our headers in the include/ folder
# adding project root as an include directory
target_include_directories(Acorn
                           PUBLIC
                           "$<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}/include>"
                           "$<INSTALL_INTERFACE:${CMAKE_INSTALL_INCLUDEDIR}>"
)
install(FILES include/TinyHsFFI.h include/Acorn.h DESTINATION ${CMAKE_INSTALL_INCLUDEDIR})
install(TARGETS Acorn
        EXPORT AcornTargets
        LIBRARY DESTINATION ${CMAKE_INSTALL_LIBDIR}
        ARCHIVE DESTINATION ${CMAKE_INSTALL_LIBDIR}
        RUNTIME DESTINATION ${CMAKE_INSTALL_BINDIR}
        INCLUDES DESTINATION ${CMAKE_INSTALL_INCLUDEDIR}
)
install(EXPORT AcornTargets
        FILE AcornTargets.cmake
        DESTINATION ${CMAKE_INSTALL_LIBDIR}/cmake/Acorn
)
