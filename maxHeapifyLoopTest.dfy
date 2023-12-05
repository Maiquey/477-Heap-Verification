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

// Checks that the max heap property holds on all elements other than the specified index in the array
// Also checks that the parent (if it exists) of each element are greater than or equal to the element's children (if they exist)
predicate isMaxHeapParentsAndChildren(arr: seq<int>, index: int, heapSize: int)
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
    requires isMaxHeapParentsAndChildren(arr[..], root, heapSize)
    modifies arr
    ensures isMaxHeapParentsAndChildren(arr[..], heapSize, heapSize)
    ensures isMaxHeap(arr[..], heapSize)
{
    var i := root;

    while i < heapSize
        invariant 0 <= i <= heapSize
        invariant isMaxHeapParentsAndChildren(arr[..], i, heapSize)
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

// Test method that maxHeapify does it's job
method main() {
    var arr := new int[10][10, 0, 9, 8, 9, 7, 6, 5, 4, 3];
    assume(arr[0] == 10 && arr[1] == 0 && arr[2] == 9 && arr[3] == 8 && arr[4] == 9 && arr[5] == 7 && arr[6] == 6 && arr[7] == 5 && arr[8] == 4 && arr[9] == 3);
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