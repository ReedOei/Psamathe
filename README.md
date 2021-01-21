# Psamathe

Psamathe is a programming language targeted at the blockchain, intended to make smart contracts safer and more concise.
It uses a new *flow* abstraction, which represents an atomic transfer.
This operation is very convenient for implementing common kinds of smart contracts, such as token contracts, auctions, etc. and works well with Psamathe's other features to provide safety and conciseness.

For an introduction to Psamathe, see [this short paper](http://reedoei.com/files/padl-21.pdf) or [this talk](https://youtu.be/2A_gIlZsAEU).

## Installation

To install and use Psamathe, clone the repository and navigate to it.
You will need [Stack](https://docs.haskellstack.org/en/stable/README/).
Then run:
```
cd Compiler/
stack install
```
Then you can compile Psamathe programs by:
```
psamathe file.flow
```
Psamathe compiles to Solidity, and by default, the Solidity code is printed to the screen.
Note that Psamathe is still very much under development.

## Examples

Here is an example implementation of the `transfer` function from [ERC-20](https://eips.ethereum.org/EIPS/eip-20).
```
type Token is fungible asset uint256
transformer transfer(balances : map address => Token,
                     dst : address,
                     amount : uint256) {
    balances[msg.sender] --[ amount ]-> balances[dst]
}
```

Additional examples can be found in the `examples/` folder in this directory, or in the `Compiler/test/resources/` directory.

## IDE Support

Currently, the only "IDE Support" for Psamathe is via a Vim syntax highlighting file, `flow.vim` in this repository's root.

