module java_map_time

open util/ordering[Time]


// ============================================================
// 1. BASIC TYPES
// ============================================================

sig Object {}

one sig null extends Object {}

sig Time {}


// ============================================================
// 2. MAP
// ============================================================

/*
 * A Map contains key-value entries at each point in Time.
 *
 * For each key:
 *
 *     0 or 1 value
 *
 * because of "lone".
 */
sig Map {
    entries : Object -> lone Object -> Time
}


// ============================================================
// 3. MAP FUNCTIONS
// ============================================================

fun Map.size[t : Time] : Int {
    #(this.entries.t)
}


pred Map.isEmpty[t : Time] {
    no this.entries.t
}


pred Map.containsKey[
    t : Time,
    k : Object
] {
    some this.entries.t[k]
}


pred Map.containsValue[
    t : Time,
    v : Object
] {
    some this.entries.t.v
}


fun Map.get[
    t : Time,
    k : Object
] : Object {
    let v = this.entries.t[k] |
        one v implies v else null
}


fun Map.keySet[
    t : Time
] : set Object {
    this.entries.t.Object
}


fun Map.values[
    t : Time
] : set Object {
    this.entries.t[Object]
}


fun Map.entrySet[
    t : Time
] : Object -> Object {
    this.entries.t
}


// ============================================================
// 4. MAP EQUALITY
// ============================================================

pred equals[
    a : Map,
    b : Map,
    t : Time
] {
    a.keySet[t] = b.keySet[t]

    all k : a.keySet[t] |
        a.get[t, k] = b.get[t, k]
}


// ============================================================
// 5. FRAME CONDITION
// ============================================================

pred unchangedMaps[
    t : Time,
    tNext : Time,
    changed : Map
] {
    all m : Map - changed |
        m.entries.tNext = m.entries.t
}


// ============================================================
// 6. PUT
// ============================================================

pred Map.put[
    t : Time,
    tNext : Time,
    k : Object,
    v : Object,
    r : Object
] {
    // r is the old value
    r = this.get[t, k]

    // Add or replace k -> v
    this.entries.tNext =
        this.entries.t ++ k -> v

    // Other Maps remain unchanged
    unchangedMaps[t, tNext, this]
}


// ============================================================
// 7. REMOVE
// ============================================================

pred Map.remove[
    t : Time,
    tNext : Time,
    k : Object,
    r : Object
] {
    this.containsKey[t, k]
    implies {
        // Return old value
        r = this.get[t, k]

        // Remove k and its value
        this.entries.tNext =
            this.entries.t - k -> Object
    }
    else {
        // Key was absent
        r = null

        // Map remains unchanged
        this.entries.tNext =
            this.entries.t
    }

    unchangedMaps[t, tNext, this]
}


// ============================================================
// 8. CLEAR
// ============================================================

pred Map.clear[
    t : Time,
    tNext : Time
] {
    no this.entries.tNext

    unchangedMaps[t, tNext, this]
}


// ============================================================
// 9. PUT ALL
// ============================================================

pred Map.putAll[
    t : Time,
    tNext : Time,
    other : Map
] {
    this.entries.tNext =
        this.entries.t ++ other.entries.t

    unchangedMaps[t, tNext, this]
}


// ============================================================
// 10. INITIAL STATE
// ============================================================

pred init {
    all m : Map |
        no m.entries.first
}


// ============================================================
// 11. TRACE
// ============================================================

fact Trace {

    init

    all t : Time - last |
        let tNext = next[t] |
        some m : Map |
            (
                some k, v, r : Object |
                    m.put[t, tNext, k, v, r]
            )
            or
            (
                some k, r : Object |
                    m.remove[t, tNext, k, r]
            )
            or
            (
                m.clear[t, tNext]
            )
            or
            (
                some other : Map |
                    m.putAll[t, tNext, other]
            )
}


// ============================================================
// 12. ASSERTIONS
// ============================================================


// ------------------------------------------------------------
// Assertion 1: Map invariant
// ------------------------------------------------------------

assert MapInvariant {

    all m : Map,
        t : Time,
        k : Object |

        lone m.entries.t[k]
}


// ------------------------------------------------------------
// Assertion 2: PUT correctness
// ------------------------------------------------------------

assert PutCorrect {

    all m : Map,
        t, tNext : Time,
        k, v, r : Object |

        m.put[t, tNext, k, v, r]

        implies

        m.entries.tNext[k] = v
}


// ------------------------------------------------------------
// Assertion 3: CLEAR correctness
// ------------------------------------------------------------

assert ClearCorrect {

    all m : Map,
        t, tNext : Time |

        m.clear[t, tNext]

        implies

        no m.entries.tNext
}


// ------------------------------------------------------------
// Assertion 4: REMOVE correctness
// ------------------------------------------------------------

assert RemoveCorrect {

    all m : Map,
        t, tNext : Time,
        k, r : Object |

        m.remove[t, tNext, k, r]

        implies

        not m.containsKey[tNext, k]
}


// ============================================================
// 13. ADDITIONAL BEHAVIORAL PROPERTIES
// ============================================================


// ------------------------------------------------------------
// Assertion 5: PUT preserves all other keys
// ------------------------------------------------------------

assert PutPreservesOtherKeys {

    all m : Map,
        t, tNext : Time,
        k, v, r : Object |

        m.put[t, tNext, k, v, r]

        implies

        all x : Object - k |
            m.entries.tNext[x] = m.entries.t[x]
}


// ------------------------------------------------------------
// Assertion 6: REMOVE preserves all other keys
// ------------------------------------------------------------

assert RemovePreservesOtherKeys {

    all m : Map,
        t, tNext : Time,
        k, r : Object |

        m.remove[t, tNext, k, r]

        implies

        all x : Object - k |
            m.entries.tNext[x] = m.entries.t[x]
}


// ------------------------------------------------------------
// Assertion 7: CLEAR makes Map empty
// ------------------------------------------------------------

assert ClearMakesEmpty {

    all m : Map,
        t, tNext : Time |

        m.clear[t, tNext]

        implies

        m.isEmpty[tNext]
}


// ============================================================
// 14. CHECK COMMANDS
// ============================================================

check MapInvariant
    for 4 but 2 Map, 5 Time

check PutCorrect
    for 4 but 2 Map, 5 Time

check ClearCorrect
    for 4 but 2 Map, 5 Time

check RemoveCorrect
    for 4 but 2 Map, 5 Time

check PutPreservesOtherKeys
    for 4 but 2 Map, 5 Time

check RemovePreservesOtherKeys
    for 4 but 2 Map, 5 Time

check ClearMakesEmpty
    for 4 but 2 Map, 5 Time


// ============================================================
// 15. VISUALIZATION COMMAND
// ============================================================

pred show {
    some Map
}

run show for 4 but 2 Map, 5 Time
