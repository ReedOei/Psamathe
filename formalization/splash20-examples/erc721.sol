contract NFToken {
  mapping (uint256 => address) idToOwner;
  mapping (uint256 => address) idToApproval;
  mapping (address => uint256) ownerToNFTokenCount;
  mapping (address => mapping (address => bool)) ownerToOperators;
  modifier canTransfer(uint256 tokId) {
    address tokenOwner = idToOwner[tokId];
    require(tokenOwner == msg.sender ||
            idToApproval[tokId] == msg.sender ||
            ownerToOperators[tokenOwner][msg.sender]);
    _;
  }
  function transferFrom(address _from, address _to, uint256 tokId)
    external canTransfer(tokId) {
    require(idToOwner[tokId] != address(0));
    require(idToOwner[tokId] == _from);
    require(_to != address(0));
    if (idToApproval[tokId] != address(0)) {
      delete idToApproval[tokId];
    }
    require(idToOwner[tokId] == _from);
    ownerToNFTokenCount[_from] = ownerToNFTokenCount[_from] - 1;
    delete idToOwner[tokId];
    require(idToOwner[tokId] == address(0));
    idToOwner[tokId] = _to;
    ownerToNFTokenCount[_to] = ownerToNFTokenCount[_to].add(1);
  }
}
