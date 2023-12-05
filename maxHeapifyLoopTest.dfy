// Computes the parent
function parent(i: int, heapSize: int): int
    ensures 0 < i < heapSize ==> parent(i, heapSize) == (i - 1) / 2
    ensures (0 >= i || i >= heapSize) ==> parent(i, heapSize) == -1
{
    if (0 < i < heapSize) then (i - 1) / 2 else -1
}

// Computes the left child
function lChild(i: int, heapSize: int): int
    ensures 0 <= i < heapSize ==> lChild(i, heapSize) == (2 * i) + 1
    ensures i >= heapSize ==> lChild(i, heapSize) == heapSize
{
    if (0 <= i < heapSize) then (2 * i) + 1 else heapSize
}

// Computes the right child
function rChild(i: int, heapSize: int): int
    ensures 0 <= i < heapSize ==> rChild(i, heapSize) == (2 * i) + 2
    ensures i >= heapSize ==> rChild(i, heapSize) == heapSize     
{
    if (0 <= i < heapSize) then (2 * i) + 2 else heapSize
}

// Checks that the max heap property holds on all elements in the array
predicate isMaxHeap(arr: seq<int>, heapSize: int)
    requires 0 <= heapSize <= |arr|
{
    forall i :: 0 <= i < heapSize ==>
        (lChild(i, heapSize) < heapSize ==> arr[i] >= arr[lChild(i, heapSize)])
        && (rChild(i, heapSize) < heapSize ==> arr[i] >= arr[rChild(i, heapSize)])
}

// Checks that the max heap property holds on all elements other than the given index in the array
// Also checks that the parent (if it exists) of the given index is greater than or equal to the index's children (if they exist)
predicate isMaxHeapParentAndChildren(arr: seq<int>, index: int, heapSize: int)
    requires 0 <= index <= heapSize <= |arr|
{
    (forall i :: 0 <= i < heapSize && i != index ==>
        (2*i+1 < heapSize ==> arr[i] >= arr[2*i+1])
        && (2*i+2 < heapSize ==> arr[i] >= arr[2*i+2]))
    && (0 <= parent(index, heapSize) < heapSize && 2*index+1 < heapSize ==> arr[parent(index, heapSize)] >= arr[2*index+1])
    && (0 <= parent(index, heapSize) < heapSize && 2*index+2 < heapSize ==> arr[parent(index, heapSize)] >= arr[2*index+2])
}

// Sorts the provided array so that all elements hold to the max heap property
method maxHeapify(root: int, heapSize: int, arr: array<int>)
    requires 0 <= root < heapSize <= arr.Length
    requires isMaxHeapParentAndChildren(arr[..], root, heapSize)
    modifies arr
    ensures isMaxHeapParentAndChildren(arr[..], heapSize, heapSize)
    ensures isMaxHeap(arr[..], heapSize)
{
    var i := root;

    while i < heapSize
        invariant 0 <= i <= heapSize
        invariant isMaxHeapParentAndChildren(arr[..], i, heapSize)
        decreases heapSize - i
    {   
        var largest := i;
        var left := lChild(i, heapSize);
        var right := rChild(i, heapSize);
        
        if left < heapSize && arr[left] >= arr[i]
        {
            largest := left;
        }

        if right < heapSize && arr[right] >= arr[largest]
        {
            largest := right;
        }
        
        if largest == i {
            assert(left < heapSize ==> arr[i] >= arr[left]);
            assert(right < heapSize ==> arr[i] >= arr[right]);
            assert(isMaxHeap(arr[..], heapSize));
            break;
        }
    
        if largest != i
        {
            assert(largest < heapSize);
            assert((largest == left) || (largest == right));
            arr[i], arr[largest] := arr[largest], arr[i];

            i := largest;
        }
    }
}

// Gets the max element in the heap (at index 0). Replaces it with the last element in the heap,
// then decrements the heapSize by 1, and then heapifies so that all elements hold to the max heap property.
method removeMax(arr: array<int>, heapSize: int) returns (root: int, newHeapSize: int)
    requires 0 < heapSize <= arr.Length
    requires isMaxHeapParentAndChildren(arr[..], heapSize, heapSize)
    requires isMaxHeap(arr[..], heapSize)
    modifies arr
    ensures 0 <= newHeapSize < arr.Length
    ensures newHeapSize == heapSize - 1
    ensures isMaxHeap(arr[..], newHeapSize)
    ensures root == old(arr[0])
{
    if heapSize == 1 {
        newHeapSize := heapSize - 1;
        root := arr[0];
    } else {
        root := arr[0];
        arr[0] := arr[heapSize - 1];
        newHeapSize := heapSize - 1;
        assert(isMaxHeapParentAndChildren(arr[..], 0, newHeapSize));
        maxHeapify(0, newHeapSize, arr);
    }
}

//InsertKey Section

predicate isMaxHeapParents(arr: seq<int>, index: int, heapSize: int)
    requires 0 <= index <= heapSize <= |arr|
{
    (forall i :: 0 <= i < heapSize && i != index ==>
        (0 <= parent(i, heapSize) < heapSize ==> arr[parent(i, heapSize)] >= arr[i]))
}

predicate isMaxHeapChildren(arr: seq<int>, index: int, heapSize: int)
    requires index <= heapSize <= |arr|
{
    (forall k :: 0 <= k < heapSize  ==>
        (2*k+1 < heapSize && 2*k+1 != index ==> arr[k] >= arr[2*k+1])
        && (2*k+2 < heapSize && 2*k+2 != index  ==> arr[k] >= arr[2*k+2]))
            && (0 <= parent(index, heapSize) < heapSize && 2*index+1 < heapSize ==> arr[parent(index, heapSize)] >= arr[2*index+1])
            && (0 <= parent(index, heapSize) < heapSize && 2*index+2 < heapSize ==> arr[parent(index, heapSize)] >= arr[2*index+2])
}

method insertKey(arr: array<int>, heapSize: int, x: int) returns (newHeapSize: int)
    requires 0 <= heapSize < arr.Length
    requires heapSize == 2
    requires isMaxHeapParentAndChildren(arr[..], heapSize, heapSize)
    requires isMaxHeapChildren(arr[..], 0, heapSize)
    requires isMaxHeap(arr[..], heapSize)
    modifies arr
    ensures 0 < newHeapSize <= arr.Length
    ensures newHeapSize == heapSize + 1
    ensures isMaxHeap(arr[..], newHeapSize)
{
    if heapSize == 0 {
        newHeapSize := heapSize + 1;
        arr[0] := x;
    } else {
        var i := heapSize;
        arr[i] := x;
        newHeapSize := heapSize + 1;
        assert(isMaxHeapParents(arr[..], i, newHeapSize));
        assert(isMaxHeapChildren(arr[..], i, newHeapSize));
        bubbleUp(i, newHeapSize, arr);
    }
}

method bubbleUp(bubble: int, heapSize: int, arr: array<int>)
    requires 0 <= bubble < heapSize <= arr.Length
    requires isMaxHeapChildren(arr[..], bubble, heapSize)
    modifies arr
    ensures isMaxHeapChildren(arr[..], 0, heapSize)
    ensures isMaxHeap(arr[..], heapSize)
{
    var i := bubble;
    
    while i > 0 && arr[(i-1)/2] < arr[i]
        invariant 0 <= i < heapSize
        invariant isMaxHeapChildren(arr[..], i, heapSize)
        decreases i
    {
        var parent := (i - 1)/2;
        assert(arr[i] > arr[parent]);
        //assert that element at index i is greater than or equal to its sibling
        assert((2*parent+1 < heapSize && 2*parent+1 != i ==> arr[i] >= arr[2*parent+1]) && (2*parent+2 < heapSize && 2*parent+2 != i ==> arr[i] >= arr[2*parent+2]));
        
        arr[i], arr[(i-1)/2] := arr[(i-1)/2], arr[i];
        i := (i-1)/2;
    }
}

// Test method that maxHeapify does it's job
method main() {
    var arr := new int[10];
    // assume(arr[0] == 10 && arr[1] == 0 && arr[2] == 9 && arr[3] == 8 && arr[4] == 9 && arr[5] == 7 && arr[6] == 6 && arr[7] == 5 && arr[8] == 4 && arr[9] == 3);
    arr[0] := 10; arr[1] := 0; arr[2] := 9; arr[3] := 8; arr[4] := 9; arr[5] := 7; arr[6] := 6; arr[7] := 5; arr[8] := 4; arr[9] := 3;
    assert(arr[1] <= arr[3]);
    assert(arr[1] <= arr[4]);
    maxHeapify(1, 10, arr);      // [10, 9, 9, 8, 3, 7, 6, 5, 4, 0]
    assert(arr[0] >= arr[1]);
    assert(arr[0] >= arr[2]);
    assert(arr[1] >= arr[3]);
    assert(arr[1] >= arr[4]);
    assert(arr[4] >= arr[9]);
    assert(isMaxHeap(arr[..], 10));
}