/*
    Heap implementation based on https://www.geeksforgeeks.org/introduction-to-heap-data-structure-and-algorithm-tutorials/
*/

class MaxHeap
{
    var arr: array<int>;
    var heapSize: int;

    constructor(size: int)
        requires size >= 0
        ensures arr.Length == size
        ensures heapSize == 0
    {
        arr := new int[size](i => 0);
        heapSize := 0;
    }

    // Not sure if these are needed, sometimes break when inserting into other methods

    // predicate isMaxHeap()
    //     requires 0 <= heapSize <= arr.Length
    // {
    //     forall i :: 0 < i < heapSize ==> arr[(i) / 2] >= arr[i]
    // }

    // method leftChild(i: int) returns (left: int)
    // {
    //     left := (2*i) + 1;
    // }

    // method rightChild(i: int) returns (right: int)
    // {
    //     right := (2*i) + 2;
    // }

    // method parent(i: int) returns (parent: int)
    // {
    //     parent := (i-1) / 2;
    // }

    //TODO: fix errors
    //Issues: 
    // - 'modifies this' causes issues for arr indexing for some reason?
    // - loop invariant isn't quite right
    // - pre and post condition behaving strangely
    method insertKey(x: int)
        modifies arr
        modifies this
        requires 0 <= heapSize <= arr.Length
        requires forall k :: 0 < k < heapSize ==> arr[(k-1)/2] >= arr[k]
        ensures forall k :: 0 < k < heapSize ==> arr[(k-1)/2] >= arr[k]
    {
        if heapSize < arr.Length 
        {
            // var i := heapSize;
            var i := heapSize;
            heapSize := heapSize + 1;
            arr[i] := x;

            while i != 0 && arr[(i-1)/2] < arr[i]
                invariant 0 <= i <= heapSize
                invariant forall k :: 0 < k < heapSize + 1 && k != i ==> arr[(k-1)/2] >= arr[k]
            {
                arr[i], arr[(i-1)/2] := arr[(i-1)/2], arr[i];
                i := (i-1)/2;
            }
        }   
    }

    //TODO: fix pre/post conditions
    method maxHeapify(i: int)
        modifies arr
        requires i >= 0
        requires heapSize < arr.Length
        decreases heapSize - i // This probably is not correct and needs to be changed
        // ensures forall k :: 0 < k < heapSize ==> arr[(k-1) / 2] >= arr[k]
    {
        var l := (2*i) + 1;
        var r := (2*i) + 2;
        var largest := i;
        if l < heapSize && arr[l] > arr[i]{
            largest := l;
        }
        if r < heapSize && arr[r] > arr[largest] {
            largest := r;
        }
        if largest != i {
            arr[i], arr[largest] := arr[largest], arr[i];
            maxHeapify(largest);
        }
    }

    //TODO: removeMax() implementation + pre/post conditions

}