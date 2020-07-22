contract EIP20 {
    mapping (address => uint256) private _balances;
    function transfer(address to, uint256 value)
        public returns (bool) {
        require(value <= _balances[msg.sender]);
        require(to != address(0));
        _balances[msg.sender] = _balances[msg.sender].sub(value);
        _balances[to] = _balances[to].add(value);
        return true;
    }
}

