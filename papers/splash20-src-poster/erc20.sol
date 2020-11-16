contract EIP20 {
    mapping (address => uint256) balances;
    mapping (address => mapping (address => uint256)) allowed;
    function transferFrom(address from, address to, uint256 value)
        public returns (bool success) {
        require(balances[from] >= value &&
                allowed[from][msg.sender] >= value);
        balances[to] += value;
        balances[from] -= value;
        allowed[from][msg.sender] -= value;
        return true;
    }
    function approve(address spender, uint256 value)
        public returns (bool success) {
        allowed[msg.sender][spender] = value;
        return true;
    }
}
