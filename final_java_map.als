module java_map_time

open util/ordering[Time]


sig Object {}
one sig null extends Object {}
sig Time {}


// M1 keys
one sig K1, K2, K3, K4 extends Object {}
// M2 keys
one sig A1, A2, A3 extends Object {}
// M1 values
one sig V1, V2, V3, V4 extends Object {}
// M2 values
one sig B1, B2, B3 extends Object {}

// separately in MapInvariant.
sig Map {
    entries : Object -> Object -> Time
}

one sig M1, M2 extends Map {}


//fun & pred
fun Map.size[t : Time] : Int {
    #(this.entries.t)
}

pred Map.isEmpty[t : Time] {
    no this.entries.t
}

pred Map.containsKey[ t : Time, k : Object] {
    some this.entries.t[k]
}

pred Map.containsValue[ t : Time, v : Object] {
    some this.entries.t.v
}

fun Map.get[t : Time,k : Object] : Object {
    let v = this.entries.t[k] | one v implies v else null
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

// equality of maps
pred equals[a : Map, b : Map, t : Time] {
    a.keySet[t] = b.keySet[t]

    all k : a.keySet[t] |
        a.get[t, k] = b.get[t, k]
}


//frame condition
pred unchangedMaps[t : Time, tNext : Time, changed : Map] {
    all m : Map - changed | m.entries.tNext = m.entries.t
}

//operations
pred Map.put[ t : Time, tNext : Time, k : Object, v : Object, r : Object] {
    // Return old value
    r = this.get[t, k]
    this.entries.tNext = this.entries.t ++ k -> v

    // Other Maps do not change
    unchangedMaps[t, tNext, this]
}

pred Map.remove[t : Time, tNext : Time, k : Object, r : Object] {
    this.containsKey[t, k] implies {
        // Return old value
        r = this.get[t, k]
        this.entries.tNext = this.entries.t - k -> Object
    }
    else {
        // Key was absent
        r = null
        this.entries.tNext = this.entries.t
    }
    unchangedMaps[t, tNext, this]
}


pred Map.clear[t : Time, tNext : Time] {
    // Map is empty after clear
    no this.entries.tNext
    unchangedMaps[t, tNext, this]
}


pred Map.putAll[t : Time, tNext : Time, other : Map] {
    // Add all entries from other at time t
    this.entries.tNext = this.entries.t ++ other.entries.t
    unchangedMaps[t, tNext, this]
}


/*initial state
 T0:

 M1:
     K1 -> V1
     K2 -> V2
     K3 -> V3

 M2:
     A1 -> B1
     A2 -> B2
     A3 -> B3  */


pred init {

    M1.entries.first =
        K1 -> V1 +
        K2 -> V2 +
        K3 -> V3

    M2.entries.first =
        A1 -> B1 +
        A2 -> B2 +
        A3 -> B3
}


/*
 T0
  |
  | M1.put(K4, V4)
  v
 T1
  |
  | M1.putAll(M2)
  v
 T2
  |
  | M2.remove(A2)
  v
 T3
  |
  | M1.clear()
  v
 T4
  |
  | no operation
  v
 T5 */


fact Trace {

    let t0 = first,
        t1 = next[t0],
        t2 = next[t1],
        t3 = next[t2],
        t4 = next[t3],
        t5 = next[t4] {
 
        // T0
        init
        
        // T0 -> T1
        // M1.put(K4, V4)
        some r1 : Object | M1.put[t0, t1, K4, V4, r1 ]
 
        // T1 -> T2
        // M1.putAll(M2)
        M1.putAll[t1, t2, M2]

        // T2 -> T3
        // M2.remove(A2)
        some r3 : Object | M2.remove[t2, t3, A2, r3]
       
        // T3 -> T4
        // M1.clear()
        M1.clear[t3, t4]

        // T4 -> T5
        // No operation.
        M1.entries.t5 = M1.entries.t4
        M2.entries.t5 = M2.entries.t4
    }
}


fact MapInvariant {all m : Map, t : Time, k : Object | lone m.entries.t[k]}

//assertions
assert PutCorrect {all m : Map, t, tNext : Time, k, v, r : Object | m.put[t, tNext, k, v, r]
        implies m.entries.tNext[k] = v
}

assert RemoveCorrect {all m : Map, t, tNext : Time, k, r : Object | m.remove[t, tNext, k, r]
        implies not m.containsKey[tNext, k]
}

assert PutPreservesOtherKeys {all m : Map, t, tNext : Time, k, v, r : Object |
        m.put[t, tNext, k, v, r] implies
        all x : Object - k | m.entries.tNext[x] = m.entries.t[x]
}

assert RemovePreservesOtherKeys {all m : Map, t, tNext : Time, k, r : Object | 
        m.remove[t, tNext, k, r] implies
        all x : Object - k | m.entries.tNext[x] = m.entries.t[x]
}

assert ClearMakesEmpty {all m : Map, t, tNext : Time |
        m.clear[t, tNext] implies m.isEmpty[tNext]
}

//check
check PutCorrect
    for 15 but exactly 2 Map, exactly 6 Time

check RemoveCorrect
    for 15 but exactly 2 Map, exactly 6 Time

check PutPreservesOtherKeys
    for 15 but exactly 2 Map, exactly 6 Time

check RemovePreservesOtherKeys
    for 15 but exactly 2 Map, exactly 6 Time

check ClearMakesEmpty
    for 15 but exactly 2 Map, exactly 6 Time


//visualization
pred show {
    some M1
    some M2
}


run show
    for 15 but exactly 2 Map, exactly 6 Time
