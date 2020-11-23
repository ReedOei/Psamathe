mapping (address => uint256) balances;
function transfer(address dst, uint256 amount) public {
  require(amount <= balances[msg.sender]);
  balances[msg.sender] = balances[msg.sender].sub(amount);
  balances[dst] = balances[dst].add(amount);
}

