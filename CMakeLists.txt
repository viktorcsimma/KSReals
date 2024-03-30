cmake_minimum_required(VERSION 3.9)

# the language is given so that GNUInstallDirs knows where to install
project(Acorn LANGUAGES C)

add_library(Acorn src/All.agda)
add_executable(AcornShell src/All.agda src/Main.hs)

# "Linking" will be the actual compilation (both with agda2hs and ghc).
# This way, we ensure that there are no additional files and need to copy
# as it was when doing Haskell compilation in `add_custom_command` directives;
# still the Haskell files get updated if the Agda sources are modified.
# (agda2hs will manage what to update.)
# And when running `sudo make install` after building,
# root won't need access to ghc.
set_target_properties(Acorn PROPERTIES
  LINKER_LANGUAGE Agda
)
set_target_properties(AcornShell PROPERTIES
  LINKER_LANGUAGE Agda
)
# The library needs a -threaded option so as to be able to interrupt a thread from another by a foreign call.
set(CMAKE_Agda_CREATE_STATIC_LIBRARY
      "agda2hs src/All.agda"
      "ghc -threaded --make -isrc -staticlib -fPIC -o libAcorn.a src/All.hs"
)
set(CMAKE_Agda_LINK_EXECUTABLE
      "agda2hs src/All.agda"
      "ghc --make -isrc -o AcornShell src/Main.hs"
)

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
