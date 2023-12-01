//Scrap file for testing ideas
//Don't mind the trash I've written here, it's just for trying things out

predicate isMaxHeap(heapSize: int, arr: array<int>)     
    reads arr
    requires 0 <= heapSize <= arr.Length
{
    forall i :: 0 < i < heapSize ==> arr[i] <= arr[(i-1) / 2]
}

method arrTest(x: int, arr: array<int>, size: int)
    modifies arr
    requires 0 <= size < arr.Length
    // requires isMaxHeap(size, arr)    // requires forall k :: 0 < k < heapSize ==> arr[(k-1)/2] >= arr[k]
    ensures 0 < size + 1 <= arr.Length
    ensures multiset(old(arr[0..size]) + [x]) == multiset(arr[0..(size + 1)]) 
    // ensures isMaxHeap(size + 1, arr)
{
    var newSize := size + 1;
    var i := size;
    arr[i] := x;
    // doWhile(arr, newSize);
    // while i != 0
    //     decreases i
    //     invariant 0 <= i <= size
    //     invariant multiset(old(arr[0..size]) + [x]) == multiset(arr[0..newSize])
    // {
    //     arr[i], arr[0] := arr[0], arr[i];
    //     i := i - 1;
    // } 
    while i != 0 && arr[(i-1)/2] < arr[i]
        modifies arr
        invariant 0 <= i
        invariant i <= newSize <= arr.Length
        // invariant forall k :: 0 < k < newSize && k != i ==> arr[(k-1)/2] >= arr[k]
        invariant multiset(old(arr[0..size]) + [x]) == multiset(arr[0..newSize])
        decreases i
    {
        arr[i], arr[(i-1)/2] := arr[(i-1)/2], arr[i];
        i := (i-1)/2;
    }   
}

method doWhile(arr: array<int>, size: int)
    modifies arr
    requires 0 < size <= arr.Length
    ensures multiset(arr[..]) == multiset(old(arr[..]))
{
    var i := size - 1;
    while i != 0 && arr[(i-1)/2] < arr[i]
            modifies arr
            invariant 0 <= i <= size <= arr.Length
            invariant multiset(arr[..]) == multiset(old(arr[..]))
            decreases i
    {
        arr[i], arr[(i-1)/2] := arr[(i-1)/2], arr[i];

        i := (i-1)/2;
    }
}

method arrTest2(x: int, arr: array<int>, size: int)
    modifies arr
    requires 0 <= size < arr.Length
    requires isMaxHeap(size, arr)    // requires forall k :: 0 < k < heapSize ==> arr[(k-1)/2] >= arr[k]
    ensures 0 < size + 1 <= arr.Length
    ensures multiset(old(arr[0..size + 1])) == multiset(arr[0..(size + 1)]) 
    ensures isMaxHeap(size + 1, arr)
{
    var newSize := size + 1;
    var i := size;

    while i != 0 && arr[(i-1)/2] < arr[i]
        modifies arr
        invariant 0 <= i
        invariant i <= newSize <= arr.Length
        invariant forall k :: 0 <= k < newSize && k != i ==> (k == 0 || arr[(k-1)/2] >= arr[k])
        invariant forall k :: i < k < newSize ==> arr[(k-1)/2] >= arr[k]
        // invariant i == size || (i > 0 ==> arr[(i-1)/2] >= arr[i])
        invariant forall  k :: 0 < k < i  ==> arr[k] >= old(arr[k])
        invariant multiset(old(arr[0..newSize])) == multiset(arr[0..newSize])
        decreases i
    {
        arr[i], arr[(i-1)/2] := arr[(i-1)/2], arr[i];
        i := (i-1)/2;
    }   
}