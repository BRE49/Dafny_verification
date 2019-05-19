module DafnyVerification{
    class SortingService {
        predicate sorted(a: array?<int>, l: int, u: int)
        reads a
        requires a != null
        {
            forall i, j :: 0 <= l <= i <= j <= u < a.Length ==> a[i] <= a[j]
        }

        predicate partitioned(a: array?<int>, i: int)
        reads a
        requires a != null
        {
            forall k, k' :: 0 <= k <= i < k' < a.Length ==> a[k] <= a[k']
        }

        method BubbleSort(a: array?<int>)
        modifies a
        requires a != null
        ensures sorted(a, 0, a.Length-1)
        {
            var i := a.Length - 1;
            while(i > 0)
            invariant i < 0 ==> a.Length == 0 // ask
            invariant sorted(a, i, a.Length-1)
            invariant partitioned(a, i)
            {
                var j := 0;
                while (j < i)
                invariant 0 < i < a.Length && 0 <= j <= i
                invariant sorted(a, i, a.Length-1)
                invariant partitioned(a, i)
                invariant forall k :: 0 <= k <= j ==> a[k] <= a[j]
                {
                    if(a[j] > a[j+1])
                    {
                        a[j], a[j+1] := a[j+1], a[j];
                    }
                    j := j + 1;
                }
                i := i -1;
            }
        }
    }

    class BinarySearchService{
        method BinarySearch(a: array<int>, key: int) returns (r: int)
        requires forall i,j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
        ensures 0 <= r ==> r < a.Length && a[r] == key
        ensures r < 0 ==> key !in a[..]
        {
        var lo, hi := 0, a.Length;
        while lo < hi
            invariant 0 <= lo <= hi <= a.Length
            invariant key !in a[..lo] && key !in a[hi..]
        {
            var mid := (lo + hi) / 2;
            if key < a[mid] {
            hi := mid;
            } else if a[mid] < key {
            lo := mid + 1;
            } else {
            return mid;
            }
        }
        return -1;
        }
    }

}