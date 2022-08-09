@PACKAGE_INIT@


# Avoid repeatedly including the targets
if(NOT TARGET Catch2::Catch2)
    # Provide path for scripts
    list(APPEND CMAKE_MODULE_PATH "${CMAKE_CURRENT_LIST_DIR}")

    include(${CMAKE_CURRENT_LIST_DIR}/Catch2Targets.cmake)
endif()