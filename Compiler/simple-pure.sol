// SPDX-License-Identifier: MIT
pragma solidity ^0.7.5;
contract C {
    record____key_One_ProposalName_value_Any_table____One__Voter[] v3;
    table__key__One__record__key__key_Any_nat_value_Any_nat[] v6;
    bool[][] v9;
    uint[][] v1;
    struct Bid {
        bool initialized;
        address sender;
        uint amount;
    }
    struct Election {
        bool initialized;
        uint[] eligibleVoters;
        table__key__One__record__key__key_One_ProposalName_value_Any_table____One__Voter proposals;
    }
    function closure_v0(bool b, bool res) public returns (bool b_out, bool res_out) {
        require((b) == (true), "FAILED TO SELECT");
        res = (res) || (true);
        delete b;
        b_out = b;
        res_out = res;
    }
    function createProposal(Election storage self, uint proposal) internal returns (bool __success) {
        uint name;
        name = proposal;
        delete proposal;
        uint[] storage voters = v1.push();
        v2.initialized = true;
        record____key_One_ProposalName_value_Any_table____One__Voter storage v2 = v3.push();
        v2.key = name;
        delete name;
        for (uint v4 = 0; (v4) < (voters.length); v4++) {
            v2.value.push(voters[v4]);
            delete voters[v4];
        }
        self.proposals.underlying_map[v2.key] = v2.value;
        self.proposals.keyset[v2.key] = true;
        self.proposals.keys.push(v2.key);
        delete v2;
        __success = (__success) || (true);
    }
    function giveRightToVote(Election storage self, uint voter) internal returns (bool __success) {
        self.eligibleVoters.push(voter);
        delete voter;
        __success = (__success) || (true);
    }
    function id(bool b) internal returns (bool res) {
        res = (res) || (b);
        delete b;
    }
    function invert(bool b) internal returns (bool res) {
        try this.closure_v0(b, res) returns (bool b_out, bool res_out) {
            b = b_out;
            res = res_out;
        } catch {
        }
    }
    struct record____key_Any_nat_value_Any_nat {
        bool initialized;
        uint key;
        uint value;
    }
    struct record____key_One_ProposalName_value_Any_table____One__Voter {
        bool initialized;
        uint key;
        uint[] value;
    }
    struct table__key__One__record__key__key_Any_nat_value_Any_nat {
        mapping (uint => uint) underlying_map;
        mapping (uint => bool) keyset;
        uint[] keys;
    }
    struct table__key__One__record__key__key_One_ProposalName_value_Any_table____One__Voter {
        mapping (uint => uint[]) underlying_map;
        mapping (uint => bool) keyset;
        uint[] keys;
    }
    struct table__key__One__record__key__key_One_address_value_Any_Token {
        mapping (address => uint) underlying_map;
        mapping (address => bool) keyset;
        address[] keys;
    }
    struct table__key__One__record__key__key_One_address_value_Any_nat {
        mapping (address => uint) underlying_map;
        mapping (address => bool) keyset;
        address[] keys;
    }
    function transfer(table__key__One__record__key__key_One_address_value_Any_nat storage balances, address src, uint amount, address dst) internal returns (bool __success) {
        require(balances.keyset[src], "KEY_NOT_FOUND");
        require((amount) <= (balances.underlying_map[src]), "UNDERFLOW");
        require(balances.keyset[dst], "KEY_NOT_FOUND");
        require((balances.underlying_map[dst]) <= ((balances.underlying_map[dst]) + (amount)), "OVERFLOW");
        balances.underlying_map[dst] = (balances.underlying_map[dst]) + (amount);
        balances.underlying_map[src] = (balances.underlying_map[src]) - (amount);
        __success = (__success) || (true);
    }
    function transferTok(table__key__One__record__key__key_One_address_value_Any_Token storage balances, address src, uint amount, address dst) internal returns (bool __success) {
        require(balances.keyset[src], "KEY_NOT_FOUND");
        require((amount) <= (balances.underlying_map[src]), "UNDERFLOW");
        require(balances.keyset[dst], "KEY_NOT_FOUND");
        require((balances.underlying_map[dst]) <= ((balances.underlying_map[dst]) + (amount)), "OVERFLOW");
        balances.underlying_map[dst] = (balances.underlying_map[dst]) + (amount);
        balances.underlying_map[src] = (balances.underlying_map[src]) - (amount);
        __success = (__success) || (true);
    }
    function vote(Election storage self, uint voter, uint proposal) internal returns (bool __success) {
        for (uint v5 = 0; (v5) < (self.eligibleVoters.length); v5++) {
            if ((self.eligibleVoters[v5]) == (voter)) {
                require(self.proposals.keyset[proposal], "KEY_NOT_FOUND");
                self.proposals.underlying_map[proposal].push(self.eligibleVoters[v5]);
                delete self.eligibleVoters[v5];
            }
        }
        __success = (__success) || (true);
    }
    constructor () {
        uint x;
        require((x) <= ((x) + (1)), "OVERFLOW");
        x = (x) + (1);
        uint y;
        require((y) <= ((y) + (4)), "OVERFLOW");
        y = (y) + (4);
        require((y) <= ((y) + (x)), "OVERFLOW");
        y = (y) + (x);
        x = (x) - (x);
        table__key__One__record__key__key_Any_nat_value_Any_nat storage m = v6.push();
        v7.initialized = true;
        record____key_Any_nat_value_Any_nat memory v7;
        require((v7.key) <= ((v7.key) + (0)), "OVERFLOW");
        v7.key = (v7.key) + (0);
        require((v7.value) <= ((v7.value) + (x)), "OVERFLOW");
        v7.value = (v7.value) + (x);
        x = (x) - (x);
        m.underlying_map[v7.key] = v7.value;
        m.keyset[v7.key] = true;
        m.keys.push(v7.key);
        delete v7;
        bool b;
        b = (b) || (false);
        uint[] storage nums = v1.push();
        nums.push(1);
        nums.push(2);
        nums.push(3);
        uint[] storage dest = v1.push();
        for (uint v8 = 0; (v8) < (nums.length); v8++) {
            if ((nums[v8]) == (4)) {
                dest.push(nums[v8]);
                delete nums[v8];
            }
            if ((nums[v8]) == (12)) {
                dest.push(nums[v8]);
                delete nums[v8];
            }
        }
        if ((4) == (4)) {
            dest.push(4);
        }
        if ((5) == (4)) {
            dest.push(5);
        }
        if ((6) == (4)) {
            dest.push(6);
        }
        bool[] storage bs = v9.push();
        uint v10 = 0;
        if (id(true)) {
            v10++;
            bs.push(true);
        }
        require(true, "FAILED_TO_SELECT_RIGHT_NUM");
        uint v11 = 0;
        if (id(false)) {
            v11++;
            bs.push(false);
        }
        require(true, "FAILED_TO_SELECT_RIGHT_NUM");
        uint z;
        require((2) <= (y), "UNDERFLOW");
        require((z) <= ((z) + (2)), "OVERFLOW");
        z = (z) + (2);
        y = (y) - (2);
        uint myToks;
        require((myToks) <= ((myToks) + (64)), "OVERFLOW");
        myToks = (myToks) + (64);
        Bid memory myBid;
        require((myBid.initialized) == (false), "ALREADY_INITIALIZED");
        myBid = Bid(true, address(0x0), 2);
        bool[] storage bs2 = v9.push();
        bs2.push(invert(true));
        bs2.push(invert(false));
    }
}
