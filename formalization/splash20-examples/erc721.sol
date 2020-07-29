contract NFToken {
  mapping (uint256 => address) idToOwner;
  mapping (uint256 => address) idToApproval;
  mapping (address => uint256) ownerToNFTokenCount;
  mapping (address => mapping (address => bool)) ownerToOperators;


  modifier canTransfer(uint256 tokId) {
    require(idToOwner[tokId] == msg.sender ||
            idToApproval[tokId] == msg.sender ||
            ownerToOperators[idToOwner[tokId]][msg.sender]);
    _;
  }
  function transferFrom(address src, address dst, uint256 tokId)
    external canTransfer(tokId) {
    require(idToOwner[tokId] != address(0));
    require(idToOwner[tokId] == src);
    require(dst != address(0));
    if (idToApproval[tokId] != address(0)) {
      delete idToApproval[tokId];
    }
    ownerToNFTokenCount[src] = ownerToNFTokenCount[src] - 1;
    delete idToOwner[tokId];
    idToOwner[tokId] = dst;
    ownerToNFTokenCount[dst] = ownerToNFTokenCount[dst].add(1);
  }
}
