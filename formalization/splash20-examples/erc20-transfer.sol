contract ERC20 {
  mapping (address => uint256) balances;
  function transfer(address dst, uint256 amt)
    public returns (bool) {
    require(amt <= balances[msg.sender]);
    balances[msg.sender] = balances[msg.sender].sub(amt);
    balances[dst] = balances[dst].add(amt);
    return true;
  }
}

