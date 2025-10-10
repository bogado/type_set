cmake_minimum_required(VERSION 3.25)
project (typeset LANGUAGES CXX C VERSION 1.0)

enable_testing()

find_package(basic_prj REQUIRED GLOBAL)

add_library(typeset INTERFACE include/typesets.hpp)

target_include_directories(typeset INTERFACE include)

setup_target(typeset INTERFACE)
add_executable(typeset-test src/main.cpp)
setup_target(typeset-test INTERFACE)

target_link_libraries(typeset-test PRIVATE typeset)

