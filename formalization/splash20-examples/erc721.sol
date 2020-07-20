contract NFToken {
  mapping (uint256 => address) idToOwner;
  mapping (uint256 => address) idToApproval;
  mapping (address => uint256) ownerToNFTokenCount;
  mapping (address => mapping (address => bool)) ownerToOperators;
  modifier canOperate(uint256 _tokenId) {
    address tokenOwner = idToOwner[_tokenId];
    require(tokenOwner == msg.sender ||
            ownerToOperators[tokenOwner][msg.sender],
            NOT_OWNER_OR_OPERATOR);
    _;
  }
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
    address tokenOwner = idToOwner[_tokenId];
    require(tokenOwner == _from, NOT_OWNER);
    require(_to != address(0), ZERO_ADDRESS);
    _transfer(_to, _tokenId);
  }
  function approve(address _approved, uint256 _tokenId)
    external override canOperate(_tokenId) validNFToken(_tokenId) {
    address tokenOwner = idToOwner[_tokenId];
    require(_approved != tokenOwner, IS_OWNER);
    idToApproval[_tokenId] = _approved;
  }
  function setApprovalForAll(address _operator, bool _approved)
    external override {
    ownerToOperators[msg.sender][_operator] = _approved;
  }
  function balanceOf(address _owner)
    external override view returns (uint256) {
    require(_owner != address(0), ZERO_ADDRESS);
    return _getOwnerNFTCount(_owner);
  }
  function ownerOf(uint256 _tokenId)
    external override view returns (address _owner) {
    _owner = idToOwner[_tokenId];
    require(_owner != address(0), NOT_VALID_NFT);
  }
  function getApproved(uint256 _tokenId)
    external override view validNFToken(_tokenId) returns (address) {
    return idToApproval[_tokenId];
  }

  /**
   * @dev Checks if `_operator` is an approved operator for `_owner`.
   * @param _owner The address that owns the NFTs.
   * @param _operator The address that acts on behalf of the owner.
   * @return True if approved for all, false otherwise.
   */
  function isApprovedForAll(
    address _owner,
    address _operator
  )
    external
    override
    view
    returns (bool)
  {
    return ownerToOperators[_owner][_operator];
  }

  /**
   * @dev Actually preforms the transfer.
   * @notice Does NO checks.
   * @param _to Address of a new owner.
   * @param _tokenId The NFT that is being transferred.
   */
  function _transfer(
    address _to,
    uint256 _tokenId
  )
    internal
  {
    address from = idToOwner[_tokenId];
    _clearApproval(_tokenId);

    _removeNFToken(from, _tokenId);
    _addNFToken(_to, _tokenId);

    emit Transfer(from, _to, _tokenId);
  }

  /**
   * @dev Mints a new NFT.
   * @notice This is an internal function which should be called from user-implemented external
   * mint function. Its purpose is to show and properly initialize data structures when using this
   * implementation.
   * @param _to The address that will own the minted NFT.
   * @param _tokenId of the NFT to be minted by the msg.sender.
   */
  function _mint(
    address _to,
    uint256 _tokenId
  )
    internal
    virtual
  {
    require(_to != address(0), ZERO_ADDRESS);
    require(idToOwner[_tokenId] == address(0), NFT_ALREADY_EXISTS);

    _addNFToken(_to, _tokenId);

    emit Transfer(address(0), _to, _tokenId);
  }

  /**
   * @dev Burns a NFT.
   * @notice This is an internal function which should be called from user-implemented external burn
   * function. Its purpose is to show and properly initialize data structures when using this
   * implementation. Also, note that this burn implementation allows the minter to re-mint a burned
   * NFT.
   * @param _tokenId ID of the NFT to be burned.
   */
  function _burn(
    uint256 _tokenId
  )
    internal
    virtual
    validNFToken(_tokenId)
  {
    address tokenOwner = idToOwner[_tokenId];
    _clearApproval(_tokenId);
    _removeNFToken(tokenOwner, _tokenId);
    emit Transfer(tokenOwner, address(0), _tokenId);
  }

  /**
   * @dev Removes a NFT from owner.
   * @notice Use and override this function with caution. Wrong usage can have serious consequences.
   * @param _from Address from wich we want to remove the NFT.
   * @param _tokenId Which NFT we want to remove.
   */
  function _removeNFToken(
    address _from,
    uint256 _tokenId
  )
    internal
    virtual
  {
    require(idToOwner[_tokenId] == _from, NOT_OWNER);
    ownerToNFTokenCount[_from] = ownerToNFTokenCount[_from] - 1;
    delete idToOwner[_tokenId];
  }

  /**
   * @dev Assignes a new NFT to owner.
   * @notice Use and override this function with caution. Wrong usage can have serious consequences.
   * @param _to Address to wich we want to add the NFT.
   * @param _tokenId Which NFT we want to add.
   */
  function _addNFToken(
    address _to,
    uint256 _tokenId
  )
    internal
    virtual
  {
    require(idToOwner[_tokenId] == address(0), NFT_ALREADY_EXISTS);

    idToOwner[_tokenId] = _to;
    ownerToNFTokenCount[_to] = ownerToNFTokenCount[_to].add(1);
  }

  /**
   * @dev Helper function that gets NFT count of owner. This is needed for overriding in enumerable
   * extension to remove double storage (gas optimization) of owner nft count.
   * @param _owner Address for whom to query the count.
   * @return Number of _owner NFTs.
   */
  function _getOwnerNFTCount(
    address _owner
  )
    internal
    virtual
    view
    returns (uint256)
  {
    return ownerToNFTokenCount[_owner];
  }

  /**
   * @dev Actually perform the safeTransferFrom.
   * @param _from The current owner of the NFT.
   * @param _to The new owner.
   * @param _tokenId The NFT to transfer.
   * @param _data Additional data with no specified format, sent in call to `_to`.
   */
  function _safeTransferFrom(
    address _from,
    address _to,
    uint256 _tokenId,
    bytes memory _data
  )
    private
    canTransfer(_tokenId)
    validNFToken(_tokenId)
  {
    address tokenOwner = idToOwner[_tokenId];
    require(tokenOwner == _from, NOT_OWNER);
    require(_to != address(0), ZERO_ADDRESS);

    _transfer(_to, _tokenId);

    if (_to.isContract())
    {
      bytes4 retval = ERC721TokenReceiver(_to).onERC721Received(msg.sender, _from, _tokenId, _data);
      require(retval == MAGIC_ON_ERC721_RECEIVED, NOT_ABLE_TO_RECEIVE_NFT);
    }
  }

  /**
   * @dev Clears the current approval of a given NFT ID.
   * @param _tokenId ID of the NFT to be transferred.
   */
  function _clearApproval(
    uint256 _tokenId
  )
    private
  {
    if (idToApproval[_tokenId] != address(0))
    {
      delete idToApproval[_tokenId];
    }
  }
}
