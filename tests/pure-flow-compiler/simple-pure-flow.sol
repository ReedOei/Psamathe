contract C {
    struct Bid {
        address sender ;
        uint amount ;
    }
    struct key__anynatvalue__anynat {
        uint key ;
        uint value ;
    }
    struct map_anynat_to_anynat {
        mapping ( uint => uint ) underlying_map ;
        uint [] keys ;
    }
    constructor ( .SolArgs ) {
        uint x ;
        uint v0 = 1 ;
        x = x + v0 ;
        v0 = 0 ;
        uint y ;
        uint v1 = 4 ;
        y = y + v1 ;
        v1 = 0 ;
        y = y + x ;
        x = 0 ;
        map_anynat_to_anynat m ;
        key__anynatvalue__anynat [] v2 ;
        for ( uint v3 = 0 ; v3 < ( v2 . length ) ; v3 ++ ) {
            m . underlying_map [ v2 [ v3 ] . key ] = v2 [ v3 ] . value ;
            m . keys . push ( v2 [ v3 ] . key , .Exprs ) ;
        }
    }
}

