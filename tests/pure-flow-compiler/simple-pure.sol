contract C {
    struct Bid {
        address sender;
        uint256 amount;
    }
    struct closure_type_2 {
        uint256 y;
        uint256 x;
        record__key__anynatvalue__anynat v0;
        table_onerecord_key__key__anynatvalue__anynat m;
    }
    struct record__key__anynatvalue__anynat {
        uint256 key;
        uint256 value;
    }
    struct record_key__key__anynatvalue__anynat {
        uint256 key;
        uint256 value;
    }
    struct table_onerecord_key__key__anynatvalue__anynat {
        mapping(uint256 => uint256) underlying_map;
        uint256[] keys;
    }

    function closure_2(closure_type_2 v4) returns (closure_type_2 v5) {
        uint256 y = v4.y;
        uint256 x = v4.x;
        record__key__anynatvalue__anynat v0 = v4.v0;
        table_onerecord_key__key__anynatvalue__anynat m = v4.m;
        y = y + 5;
        5 = 5 - 5;
        v5.v0 = v0;
        v5.m = m;
        v5.y = y;
        v5.x = x;
    }

    function id(bool b) returns (bool res) {
        res = res || b;
        b = false;
    }

    function transfer(
        table_onerecord_key__key__anynatvalue__anynat balances,
        uint256 src,
        uint256 amount,
        uint256 dst
    ) returns (bool success) {
        if (amount <= (balances.underlying_map[src].value)) {
            balances.underlying_map[dst].value =
                balances.underlying_map[dst].value +
                amount;
            balances.underlying_map[src].value =
                balances.underlying_map[src].value -
                amount;
        }
        success = success || true;
        true = false;
    }

    constructor() {
        uint256 x;
        x = x + 1;
        1 = 1 - 1;
        uint256 y;
        y = y + 4;
        4 = 4 - 4;
        y = y + x;
        x = x - x;
        table_onerecord_key__key__anynatvalue__anynat m;
        record__key__anynatvalue__anynat v0;
        v0.key = 0;
        v0.value = x;
        m.underlying_map[v0.key] = v0.value;
        m.keys.push(v0.key);
        v1.v0 = v0;
        v1.m = m;
        v1.y = y;
        v1.x = x;
        try this.closure_2(v1) returns (closure_type_2 v3) {
            v0 = v3.v0;
            m = v3.m;
            y = v3.y;
            x = v3.x;
        } catch {
            y = y + 4;
            4 = 4 - 4;
        }
        bool b;
        b = b || false;
        false = false;
        table_anynat nums;
        nums.push(1);
        nums.push(2);
        nums.push(3);
        table_anynat dest;
        for (uint256 v7 = 0; v7 < (nums.length); v7++) {
            if (nums[v6] == 4) {
                dest.push(nums[v6]);
            }
        }
        if (4 == 4) {
            dest.push(4);
        }
        if (5 == 4) {
            dest.push(5);
        }
        if (6 == 4) {
            dest.push(6);
        }
        table_onebool bs;
        if (id(true)) {
            bs.push(true);
        }
        if (id(false)) {
            bs.push(false);
        }
        uint256 z;
        if (y == 2) {
            z = z + y;
            y = y - y;
        }
    }
}
