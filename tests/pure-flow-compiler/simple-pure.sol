contract C {
    struct Bid {
        address sender;
        uint256 amount;
    }
    struct closure_type_7 {
        uint256 y;
        uint256 x;
        record__key__anynatvalue__anynat v2;
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

    function closure_7(closure_type_7 v9) returns (closure_type_7 v10) {
        uint256 y = v9.y;
        uint256 x = v9.x;
        record__key__anynatvalue__anynat v2 = v9.v2;
        table_onerecord_key__key__anynatvalue__anynat m = v9.m;
        uint256 v5 = 5;
        y = y + v5;
        v5 = 0;
        v10.v2 = v2;
        v10.m = m;
        v10.y = y;
        v10.x = x;
    }

    function id(bool b) returns (bool res) {
        res = res || b;
        b = false;
    }

    constructor() {
        uint256 v0 = 1;
        uint256 x;
        x = x + v0;
        v0 = 0;
        uint256 v1 = 4;
        uint256 y;
        y = y + v1;
        v1 = 0;
        y = y + x;
        x = 0;
        table_onerecord_key__key__anynatvalue__anynat m;
        record__key__anynatvalue__anynat v2;
        uint256 v3 = 0;
        v2.key = v3;
        v2.value = x;
        m.underlying_map[v2.key] = v2.value;
        m.keys.push(v2.key);
        v6.v2 = v2;
        v6.m = m;
        v6.y = y;
        v6.x = x;
        try this.closure_7(v6) returns (closure_type_7 v8) {
            v2 = v8.v2;
            m = v8.m;
            y = v8.y;
            x = v8.x;
        } catch {
            uint256 v4 = 4;
            y = y + v4;
            v4 = 0;
        }
        bool v11 = false;
        bool b;
        b = b || v11;
        v11 = false;
        uint256 v12 = 1;
        uint256 v13 = 2;
        uint256 v14 = 3;
        table_anynat nums;
        nums.push(v12);
        nums.push(v13);
        nums.push(v14);
        uint256 v15 = 4;
        table_anynat dest;
        for (uint256 v16 = 0; v16 < (nums.length); v16++) {
            if (nums[v16] == v15) {
                dest.push(nums[v16]);
            }
        }
        delete nums;
        uint256 v17 = 4;
        uint256 v18 = 5;
        uint256 v19 = 6;
        uint256 v20 = 4;
        if (v17 == v20) {
            dest.push(v17);
        }
        if (v18 == v20) {
            dest.push(v18);
        }
        if (v19 == v20) {
            dest.push(v19);
        }
        bool v21 = true;
        bool v22 = false;
        table_onebool bs;
        if (id(v21)) {
            bs.push(v21);
        }
        if (id(v22)) {
            bs.push(v22);
        }
    }
}
