contract ERC20 {
  mapping (address => uint) balances;
  function transfer(address dst, uint amount) public {
    require(amount <= balances[msg.sender]);
    balances[msg.sender] =
      balances[msg.sender].sub(amount);
    balances[dst] = balances[dst].add(amount);
  }
}

