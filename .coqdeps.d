language.vo language.glob language.v.beautified: language.v
language.vio: language.v
blockchain.vo blockchain.glob blockchain.v.beautified: blockchain.v language.vo
blockchain.vio: blockchain.v language.vio
semantics.vo semantics.glob semantics.v.beautified: semantics.v language.vo blockchain.vo
semantics.vio: semantics.v language.vio blockchain.vio
tests.vo tests.glob tests.v.beautified: tests.v language.vo semantics.vo
tests.vio: tests.v language.vio semantics.vio
factorial.vo factorial.glob factorial.v.beautified: factorial.v language.vo semantics.vo
factorial.vio: factorial.v language.vio semantics.vio
multisig.vo multisig.glob multisig.v.beautified: multisig.v language.vo blockchain.vo semantics.vo
multisig.vio: multisig.v language.vio blockchain.vio semantics.vio
