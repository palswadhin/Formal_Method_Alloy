module java_map_time

open util/ordering[Time]


// ============================================================
// BASIC TYPES
// ============================================================

sig Object {}

one sig null extends Object {}

sig Time {}


// ============================================================
// MAP
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
// MAP FUNCTIONS
// ============================================================

fun Map.size[t : Time] : Int {
    #(this.entries.t)
}


pred Map.isEmpty[t : Time] {
    no this.entries.t
}


pred Map.containsKey[t : Time, k : Object] {
    some this.entries.t[k]
}


pred Map.containsValue[t : Time, v : Object] {
    some this.entries.t.v
}


fun Map.get[t : Time, k : Object] : Object {
    let v = this.entries.t[k] |
        one v implies v else null
}


fun Map.keySet[t : Time] : set Object {
    this.entries.t.Object
}


fun Map.values[t : Time] : set Object {
    this.entries.t[Object]
}


fun Map.entrySet[t : Time] : Object -> Object {
    this.entries.t
}


// ============================================================
// MAP EQUALITY
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
// FRAME CONDITION
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
// PUT
// ============================================================

pred Map.put[
    t : Time,
    tNext : Time,
    k : Object,
    v : Object,
    r : Object
] {
    r = this.get[t, k]

    this.entries.tNext =
        this.entries.t ++ k -> v

    unchangedMaps[t, tNext, this]
}


// ============================================================
// REMOVE
// ============================================================

pred Map.remove[
    t : Time,
    tNext : Time,
    k : Object,
    r : Object
] {
    this.containsKey[t, k]
    implies {
        r = this.get[t, k]

        this.entries.tNext =
            this.entries.t - k -> Object
    }
    else {
        r = null

        this.entries.tNext =
            this.entries.t
    }

    unchangedMaps[t, tNext, this]
}


// ============================================================
// CLEAR
// ============================================================

pred Map.clear[
    t : Time,
    tNext : Time
] {
    no this.entries.tNext

    unchangedMaps[t, tNext, this]
}


// ============================================================
// PUT ALL
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
// INITIAL STATE
// ============================================================

pred init {
    all m : Map |
        no m.entries.first
}


// ============================================================
// TRACE
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
// ASSERTIONS
// ============================================================

assert MapInvariant {

    all m : Map, t : Time, k : Object |
        lone m.entries.t[k]
}


assert PutCorrect {

    all m : Map,
        t, tNext : Time,
        k, v, r : Object |

        m.put[t, tNext, k, v, r]
        implies
        m.entries.tNext[k] = v
}


assert ClearCorrect {

    all m : Map,
        t, tNext : Time |

        m.clear[t, tNext]
        implies
        no m.entries.tNext
}


assert RemoveCorrect {

    all m : Map,
        t, tNext : Time,
        k, r : Object |

        m.remove[t, tNext, k, r]
        implies
        not m.containsKey[tNext, k]
}


// ============================================================
// VISUALIZATION
// ============================================================

pred show {
    some Map
}


run show for 4 but 2 Map, 5 Time
