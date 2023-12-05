/*
    Helper functions and predicates
*/

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
        (2*i+1 < heapSize ==> arr[i] >= arr[2*i+1]) && (2*i+2 < heapSize ==> arr[i] >= arr[2*i+2]))
    && (0 <= parent(index, heapSize) < heapSize && 2*index+1 < heapSize ==> arr[parent(index, heapSize)] >= arr[2*index+1])
    && (0 <= parent(index, heapSize) < heapSize && 2*index+2 < heapSize ==> arr[parent(index, heapSize)] >= arr[2*index+2])
}

//Checks that the max heap property holds so that all children of all nodes are less than their parent, unless the child's index is equal to the given index
//Used to inductively verify insertion and key increase through the bubbleUp method
predicate isMaxHeapChildren(arr: seq<int>, index: int, heapSize: int)
    requires index <= heapSize <= |arr|
{
    (forall k :: 0 <= k < heapSize  ==>
        (2*k+1 < heapSize && 2*k+1 != index ==> arr[k] >= arr[2*k+1])
        && (2*k+2 < heapSize && 2*k+2 != index  ==> arr[k] >= arr[2*k+2]))
            && (0 <= parent(index, heapSize) < heapSize && 2*index+1 < heapSize ==> arr[parent(index, heapSize)] >= arr[2*index+1])
            && (0 <= parent(index, heapSize) < heapSize && 2*index+2 < heapSize ==> arr[parent(index, heapSize)] >= arr[2*index+2])
}

/*
    Part 1 of specification (Max Heap property is maintained before and after insertion of a new element)
*/

// Key Insertion
method insertKey(arr: array<int>, heapSize: int, x: int) returns (newHeapSize: int)
    requires 0 <= heapSize < arr.Length
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
        assert(isMaxHeapChildren(arr[..], i, newHeapSize));
        bubbleUp(i, newHeapSize, arr);
    }
}

// Method to move key up to its proper place in the complete binary tree
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
        arr[i], arr[(i-1)/2] := arr[(i-1)/2], arr[i];
        i := (i-1)/2;
    }
}

/*
    Part 2 of specification (Max Heap property is maintained before and after removal of an element from the heap)
*/

// Gets the max element in the heap (at index 0). Replaces it with the last element in the heap,
// then decrements the heapSize by 1, and then heapifies so that all elements hold to the max heap property.
method removeMax(arr: array<int>, heapSize: int) returns (root: int, newHeapSize: int)
    requires 0 < heapSize <= arr.Length
    requires isMaxHeapParentAndChildren(arr[..], heapSize, heapSize)
    requires isMaxHeap(arr[..], heapSize)
    modifies arr
    ensures 0 <= newHeapSize < arr.Length
    ensures newHeapSize == heapSize - 1
    ensures isMaxHeapParentAndChildren(arr[..], newHeapSize, newHeapSize)
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

/*
    Additional Heap methods not in original specification but nevertheless verified
*/

// Increase an element's value and fix the heap structure (Max Heap property maintained before and after operation)
method increaseKey(arr: array<int>, heapSize: int, i: int, newVal: int)
    requires 0 <= i < heapSize <= arr.Length
    requires newVal > arr[i]
    requires isMaxHeapParentAndChildren(arr[..], heapSize, heapSize)
    requires isMaxHeapChildren(arr[..], 0, heapSize)
    requires isMaxHeap(arr[..], heapSize)
    modifies arr
    ensures isMaxHeap(arr[..], heapSize)  
    ensures isMaxHeapParentAndChildren(arr[..], heapSize, heapSize)
{
    arr[i] := newVal;
    assert(isMaxHeapChildren(arr[..], i, heapSize));
    bubbleUp(i, heapSize, arr);
}