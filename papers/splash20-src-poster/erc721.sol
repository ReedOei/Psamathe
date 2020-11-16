contract NFToken {
  mapping (uint256 => address) idToOwner;
  mapping (uint256 => address) idToApproval;
  mapping (address => uint256) ownerToNFTokenCount;
  mapping (address => mapping (address => bool)) ownerToOperators;

  function transferFrom(address src, address dst, uint256 tokId) external {
    require(idToOwner[tokId] == msg.sender ||
            idToApproval[tokId] == msg.sender ||
            ownerToOperators[idToOwner[tokId]][msg.sender]);
    require(idToOwner[tokId] != address(0));
    require(idToOwner[tokId] == src && dst != address(0));
    if (idToApproval[tokId] != address(0)) {
      delete idToApproval[tokId];
    }
    ownerToNFTokenCount[src] = ownerToNFTokenCount[src] - 1;
    idToOwner[tokId] = dst;
    ownerToNFTokenCount[dst] = ownerToNFTokenCount[dst].add(1);
  }
}
