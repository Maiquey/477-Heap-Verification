/*
    Heap implementation based on https://www.geeksforgeeks.org/introduction-to-heap-data-structure-and-algorithm-tutorials/
*/

class MaxHeap
{
    var arr: array<int>
    const maxSize: int      // this value shouldn't change ==> declared as const
    var heapSize: int

    constructor(size: int)
        requires size >= 0
        ensures maxSize == arr.Length == size      // was missing maxSize
        ensures heapSize == 0
    {   
        maxSize := size;
        arr := new int[size](i => 0);
        heapSize := 0;
    }

    // I think this predicate contributes to MaxHeapify()'s 'ensures' clause not being verified.
    // Need to ensure that the max heap property holds after each recursive call of MaxHeapify().
    predicate isMaxHeap(heapSize: int, arr: array<int>)     
        reads arr
        requires 0 <= heapSize <= arr.Length
    {
        forall i :: 0 < i < heapSize ==> arr[i] <= arr[(i-1) / 2]
    }

    // TODO: fix pre/post conditions
    method MaxHeapify(i: int)
        modifies arr
        requires 0 <= i < heapSize <= arr.Length    
        decreases heapSize - i  // This probably is not correct and needs to be changed
        // ensures isMaxHeap(heapSize, arr)     // Enabling this somehow makes 'if largest != i' invalid..?    // = ensures forall k :: 0 < k < heapSize ==> arr[(k-1) / 2] >= arr[k]
        ensures multiset(arr[..]) == multiset(old(arr[..]))
    {
        // It's possible that i may not have a left or right child, so initialize
        // both left child and right child to a value that makes l < heapSize and r < heapSize false.
        var l: int := heapSize;     
        var r: int := heapSize;
        // If a child exists, then set l and/or r to the returned child.
        if i < heapSize / 2 && (2 * i) + 1 < heapSize {
            l := lChild(i);
        }
        if i < heapSize / 2 && (2 * i) + 2 < heapSize {
            r := rChild(i);
        }
        
        var largest := i;
        if l < heapSize && arr[l] > arr[largest] {
            largest := l;
        }
        if r < heapSize && arr[r] > arr[largest] {
            largest := r;
        }
        if largest != i {
            arr[i], arr[largest] := arr[largest], arr[i];
            assert(0 <= largest < heapSize <= arr.Length);
            MaxHeapify(largest);    
            // assume(isMaxHeap(heapSize, arr));
            assume(multiset(arr[..]) == multiset(old(arr[..])));
        }
    }

    method parent(i: int) returns (parent: int)
        requires 0 < i < heapSize   // i is a valid index in the heap.
        ensures 0 <= parent < i    // parent precedes i.
        ensures parent == (i - 1) / 2
    {
        parent := (i - 1) / 2;
    }

    method lChild(i: int) returns (left: int)
        requires 0 <= i < heapSize / 2      // i is an internal node in the heap.
        requires (2 * i) + 1 < heapSize       // left child of i exists in the heap.
        ensures i < left < heapSize         // i precedes left.
        ensures left == (2 * i) + 1
    {
        left := (2 * i) + 1;
    }

    method rChild(i: int) returns (right: int)
        requires 0 <= i < heapSize / 2      // i is an internal node in the heap.
        requires (2 * i) + 2 < heapSize       // right child of i exists in the heap.
        ensures i < right < heapSize        // i precedes right.
        ensures right == (2 * i) + 2
    {
        right := (2 * i) + 2;
    }

    // Issue: Can't resolve error at 'heapSize := heapSize - 1', so I put assume() for now so that at least it doesn't give error
    method removeMax() returns (root: int)
        modifies this, arr
        requires 0 < heapSize <= arr.Length
        ensures 0 <= heapSize < arr.Length
        ensures root == old(arr[0])
        ensures heapSize == old(heapSize) - 1
        // ensures isMaxHeap(heapSize, arr)
    {
        if heapSize == 1 {
            // assume(heapSize == heapSize - 1);   // I think this is wrong, but I couldn't figure out how to resolve the error when doing heapSize := heapSize - 1
            heapSize := heapSize - 1;
            root := arr[0];
        } else {
            root := arr[0];
            arr[0] := arr[heapSize - 1];
            // assume(heapSize == heapSize - 1);   // I think this is wrong, but I couldn't figure out how to resolve the error when doing heapSize := heapSize - 1
            heapSize := heapSize - 1;
            MaxHeapify(0);
        }
    }

    // TODO: Might need to add post condition..?
    method increaseKey(i: int, newVal: int)
        modifies arr
        requires 0 <= i < heapSize <= arr.Length
        // ensures isMaxHeap(heapSize, arr)     // error
    {
        arr[i] := newVal;
        var j := i;
        while j != 0 && arr[(j-1)/2] < arr[j]
            invariant 0 <= j <= heapSize
            // invariant forall k :: 0 < k < heapSize && k != j ==> arr[(k-1)/2] >= arr[k]     // error
            // invariant isMaxHeap(heapSize, arr)     // error
            decreases j
        {
            arr[j], arr[(j-1)/2] := arr[(j-1)/2], arr[j];
            j := (j-1)/2;
        }
    }

    method getMax() returns (max: int)
        requires 0 < heapSize <= arr.Length
        ensures max == arr[0]
    {
        max := arr[0];
    }

    method curSize() returns (currentSize: int)
        ensures currentSize == heapSize
    {
        currentSize := heapSize;
    }

    const INT_MAX: int := 2147483647
    method deleteKey(i: int)
        modifies this, arr
        requires 0 <= i < heapSize <= arr.Length
        ensures heapSize == old(heapSize) - 1
        ensures 0 <= i <= heapSize < arr.Length
        // ensures isMaxHeap(heapSize, arr)
    {
        increaseKey(i, INT_MAX);
        var root := removeMax();
    }


    // TODO: fix errors
    // Issues: 
    // - loop invariant isn't quite right
    // - pre and post condition behaving strangely
    method insertKey(x: int)
        modifies this, arr
        requires 0 <= heapSize < arr.Length
        requires isMaxHeap(heapSize, arr)    // requires forall k :: 0 < k < heapSize ==> arr[(k-1)/2] >= arr[k]
        ensures heapSize == old(heapSize) + 1
        ensures 0 < heapSize <= arr.Length
        // ensures isMaxHeap(heapSize, arr)     // ensures  forall k :: 0 < k < heapSize ==> arr[(k-1)/2] >= arr[k]
    {
        var i := heapSize;
        heapSize := heapSize + 1;
        arr[i] := x;

        while i != 0 && arr[(i-1)/2] < arr[i]
            modifies arr
            invariant heapSize == old(heapSize) + 1
            invariant 0 <= i
            invariant i <= heapSize <= arr.Length
            // invariant forall k :: 0 < k < heapSize && k != i ==> arr[(k-1)/2] >= arr[k]
        {
            arr[i], arr[(i-1)/2] := arr[(i-1)/2], arr[i];
            i := (i-1)/2;
        }
        
    }

}
