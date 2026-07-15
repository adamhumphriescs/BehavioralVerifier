#===------------------------------------------------------------------------===#
#
#                     The KLEE Symbolic Virtual Machine
#
# This file is distributed under the University of Illinois Open Source
# License. See LICENSE.TXT for details.
#
#===------------------------------------------------------------------------===#
klee_add_component(kleeTase
  CVAssignment.cpp
  #  API.cpp
  API_Alt.cpp
  TASESysModels.cpp
  TASEFloatModels.cpp
  TASESSLVerModels.cpp
  TASETetriNETVerModels.cpp
  TASEMAVLinkVerModels.cpp
  TASEConstraintBOWEncoding.cpp
  EditDistanceOracle.cpp
  )


klee_add_component(kleeTaseScout
  CVAssignment.cpp
  API_Scout.cpp
  TASESysModels.cpp
  TASEFloatModels.cpp
  TASESSLVerModels.cpp
  TASETetriNETVerModels.cpp
  TASEMAVLinkVerModels.cpp
  TASEConstraintBOWEncoding.cpp
  EditDistanceOracle.cpp  
  )


target_include_directories(kleeTase PUBLIC ${PROJECT_SOURCE_DIR}/../microbenchmarks/mavlink/c_library_v2/common/ ${PROJECT_SOURCE_DIR}/../microbenchmarks/mavlink/packets/)
target_include_directories(kleeTaseScout PUBLIC ${PROJECT_SOURCE_DIR}/../microbenchmarks/mavlink/c_library_v2/common/ ${PROJECT_SOURCE_DIR}/../microbenchmarks/mavlink/packets/)

target_link_libraries(kleeTase PRIVATE ${ZLIB_LIBRARIES})
target_link_libraries(kleeTaseScout PRIVATE ${ZLIB_LIBRARIES})

klee_get_llvm_libs(LLVM_LIBS ${LLVM_COMPONENTS})
target_link_libraries(kleeTase PUBLIC ${LLVM_LIBS})
target_link_libraries(kleeTaseScout PUBLIC ${LLVM_LIBS})

target_link_libraries(kleeTase PRIVATE
  kleeBasic
  kleeCore
  kleeModule
  kleaverSolver
  kleaverExpr
  kleeSupport
  ${CMAKE_BINARY_DIR}/lib/libtase.a
  )

target_link_libraries(kleeTaseScout PRIVATE
  kleeBasic
  kleeCore
  kleeModule
  kleaverSolver
  kleaverExpr
  kleeSupport
  ${CMAKE_BINARY_DIR}/lib/libtase.a
  )

target_link_options(kleeTase PUBLIC "-lc -lgcc_s")
target_link_options(kleeTaseScout PUBLIC "-lc -lgcc_s")
