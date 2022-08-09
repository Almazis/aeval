Include(FetchContent)

FetchContent_Declare(
  Catch2
  GIT_REPOSITORY https://github.com/catchorg/Catch2.git
  GIT_TAG        v2.13.9 # or a later release
)

FetchContent_MakeAvailable(Catch2)

add_executable(unitTests
  test.cpp
)
target_link_libraries(unitTests Catch2::Catch2)

include(CTest)
include(Catch)
catch_discover_tests(unitTests)
