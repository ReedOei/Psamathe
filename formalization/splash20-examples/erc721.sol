contract NFToken {
  mapping (uint256 => address) idToOwner;
  mapping (uint256 => address) idToApproval;
  mapping (address => uint256) ownerToNFTokenCount;
  mapping (address => mapping (address => bool)) ownerToOperators;
  modifier canTransfer(uint256 _tokenId) {
    address tokenOwner = idToOwner[_tokenId];
    require(tokenOwner == msg.sender ||
            idToApproval[_tokenId] == msg.sender ||
            ownerToOperators[tokenOwner][msg.sender],
            NOT_OWNER_APPROWED_OR_OPERATOR);
    _;
  }
  modifier validNFToken(uint256 _tokenId) {
    require(idToOwner[_tokenId] != address(0), NOT_VALID_NFT);
    _;
  }
  function transferFrom(address _from, address _to, uint256 _tokenId)
    external override canTransfer(_tokenId) validNFToken(_tokenId) {
    require(idToOwner[_tokenId] == _from, NOT_OWNER);
    require(_to != address(0), ZERO_ADDRESS);
    address from = idToOwner[_tokenId];
    if (idToApproval[_tokenId] != address(0)) {
      delete idToApproval[_tokenId];
    }
    _removeNFToken(from, _tokenId);
    require(idToOwner[_tokenId] == _from, NOT_OWNER);
    ownerToNFTokenCount[_from] = ownerToNFTokenCount[_from] - 1;
    delete idToOwner[_tokenId];
    _addNFToken(_to, _tokenId);
    require(idToOwner[_tokenId] == address(0), NFT_ALREADY_EXISTS);
    idToOwner[_tokenId] = _to;
    ownerToNFTokenCount[_to] = ownerToNFTokenCount[_to].add(1);
}
