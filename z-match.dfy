/* Array Predicates */

predicate nonnull <T> (arr : array<T>)
{
  arr != null
}

predicate nonempty <T> (arr : array<T>)
  requires nonnull(arr)
{
  0 < arr.Length
}

predicate contains <T(==)> (ele : T, arr : array<T>)
  reads arr
  requires nonnull(arr)
{
  exists idx :: 0 <= idx < arr.Length && arr[idx] == ele
}

predicate same_size <S, T> (arr1 : array<S>, arr2 : array<T>)
  requires nonnull(arr1)
  requires nonnull(arr2)
{
  arr1.Length == arr2.Length
}

predicate valid_idx <T> (idx : int, arr : array<T>)
  requires nonnull(arr)
{
  0 <= idx < arr.Length
}

predicate valid_slice <T> (start : int, size : int, arr : array<T>)
  requires nonnull(arr)
{
  size == 0 || (valid_idx(start, arr) && valid_idx(start + size - 1, arr))
}

predicate slice_eq <T(==)> (start1 : int, arr1 : array<T>, start2 : int, arr2 : array<T>, size : int)
  reads arr1
  reads arr2
  requires nonnull(arr1)
  requires nonnull(arr2)
{
  valid_slice(start1, size, arr1) &&
  valid_slice(start2, size, arr2) &&
  forall offset :: 0 <= offset < size ==> arr1[start1 + offset] == arr2[start2 + offset]
}

/* Z Predicates */

predicate z_zero_correct (zs : array<int>)
  reads zs
  requires nonnull(zs)
  requires nonempty(zs)
{
  zs[0] == 0
}

predicate z_slices_valid (zs : array<int>)
  reads zs
  requires nonnull(zs)
{
  nonempty(zs) &&
  forall idx :: 1 <= idx < zs.Length ==> valid_slice(idx, zs[idx], zs)
}

predicate z_nonzero_correct (str : array<char>, zs : array<int>)
  reads str
  reads zs
  requires nonnull(str)
  requires nonnull(zs)
{
  forall idx :: 1 <= idx < zs.Length ==> forall k :: 0 <= k <= str.Length - idx ==>
    (zs[idx] >= k <==> slice_eq(0, str, idx, str, k))
}

predicate z_correct (str : array<char>, zs : array<int>)
  reads str
  reads zs
  requires nonnull(str)
  requires nonnull(zs)
  requires nonempty(str)
  requires nonempty(zs)
  requires same_size(str, zs)
{
  z_zero_correct(zs) &&
  z_slices_valid(zs) &&
  z_nonzero_correct(str, zs)
}

method z_algorithm_naive(str : array<char>) returns (zs : array<int>)
  requires nonnull(str)
  requires nonempty(str)

  ensures nonnull(zs)
  ensures same_size(str, zs)
  ensures z_correct(str, zs)
{
  zs := new int[str.Length];

  zs[0] := 0;

  var i := 1;

  while (i < zs.Length)
    invariant 1 <= i <= zs.Length
    invariant z_zero_correct(zs)
    invariant forall idx :: 1 <= idx < i ==> valid_slice(idx, zs[idx], zs)
    invariant forall idx :: 1 <= idx < i ==> forall k :: 0 <= k <= str.Length - idx ==>
      (zs[idx] >= k <==> slice_eq(0, str, idx, str, k))
  {
    var j := 0;

    while (j < zs.Length - i)
      invariant 0 <= j <= zs.Length - i
      invariant slice_eq(0, str, i, str, j)
    {
      if str[j] != str[i + j] {
        break;
      }

      j := j + 1;
    }

    zs[i] := j;

    i := i + 1;
  }
}

method z_algorithm(str : array<char>) returns (zs : array<int>)
  requires nonnull(str)
  requires nonempty(str)

  ensures nonnull(zs)
  ensures same_size(str, zs)
  ensures z_correct(str, zs)
{
  zs := new int[str.Length];

  zs[0] := 0;

  var i := 1;
  var j := 0;
  
  while (i< zs.Length)
    invariant 1 <= i <= zs.Length
    invariant z_zero_correct(zs)
    invariant j < i
    invariant forall idx :: 1 <= idx < i ==> valid_slice(idx, zs[idx], str)
    invariant forall idx :: 1 <= idx < i ==> slice_eq(0, str, idx, str, zs[idx])
    invariant forall idx :: 1 <= idx < i ==> forall k :: 0 <= k <= str.Length - idx ==>
      (zs[idx] >= k ==> slice_eq(0, str, idx, str, k))
    invariant forall idx :: 1 <= idx < i ==> (idx + zs[idx] < str.Length ==> str[zs[idx]] != str[idx + zs[idx]])
    invariant forall idx :: 1 <= idx < i ==> forall k :: 0 <= k <= str.Length - idx ==>
      (slice_eq(0, str, idx, str, k) ==> zs[idx] >= k)
  {
    if (j + zs[j] < i) { // no Z box before i extends past i
      var l := 0;

      while (l < str.Length - i)
        invariant 0 <= l <= str.Length - i
        invariant valid_slice(i, l, str)
        invariant slice_eq(0, str, i, str, l)
      {
        if (str[l] != str[i + l]) {
          break;
        }

        l := l + 1;
      }

      zs[i] := l;
      j := i;
    } else {
      var k := i - j;
      
      if (k + zs[k] < zs[j]) {
        zs[i] := zs[k];
      } else if (k + zs[k] > zs[j]) {
        zs[i] := j + zs[j] - i;
      } else {
        var tmp := j + zs[j];
        var l := 0;

        while (l < str.Length - tmp)
          invariant 0 <= l <= str.Length - i
          invariant valid_slice(i, tmp - i + l, str)
          invariant slice_eq(0, str, i, str, tmp - i + l)
        {
          if (str[tmp - i + l] != str[tmp + l]) {
            break;
          }

          l := l + 1;
        }

        zs[i] := tmp - i + l;
        j := i;
      }
    }

    i := i + 1;
  }
}

method print_arr <T> (arr : array<T>)
  requires nonnull(arr)
{
  var i := 0;

  print "[";

  if (arr.Length == 0)
  {
    print "[]";
    return;
  }

  while (i < arr.Length - 1)
    invariant 0 <= i <= arr.Length - 1
  {
    print arr[i];
    print " ";

    i := i + 1;
  }

  print arr[i];
  print "]\n";
}

method array_of_string (str : string) returns (ret : array<char>)
  requires 0 < |str|

  ensures nonnull(ret)
  ensures nonempty(ret)
  ensures |str| == ret.Length
  ensures forall idx :: 0 <= idx < |str| ==> str[idx] == ret[idx]
{
  ret := new char[|str|];

  var i := 0;

  while (i < |str|)
  invariant 0 <= i <= |str|
  invariant forall k :: 0 <= k < i ==> str[k] == ret[k]
  {
    ret[i] := str[i];

    i := i + 1;
  }
}

method matches(pattern : array<char>, text : array<char>) returns (ret : seq<int>)
  requires nonnull(pattern)
  requires nonnull(text)
  requires !contains('$', pattern)
  requires !contains('$', text)

  ensures forall idx :: 0 <= idx < text.Length ==> (slice_eq(0, pattern, idx, text, pattern.Length) <==> idx in ret)
{
  ret := [];

  var conc := new char[pattern.Length + text.Length + 1];

  var i := 0;

  while (i < conc.Length)
    invariant 0 <= i <= conc.Length
    invariant forall k :: 0 <= k < i ==> if k < pattern.Length then conc[k] == pattern[k] else if k == pattern.Length then conc[k] == '$' else conc[k] == text[k - (pattern.Length + 1)]
  {
    if (i < pattern.Length) {
      conc[i] := pattern[i];
    } else if (i == pattern.Length) {
      conc[i] := '$';
    } else {
      conc[i] := text[i - (pattern.Length + 1)];
    }

    i := i + 1;
  }

  print_arr(conc);

  var zs := z_algorithm(conc);

  print_arr(zs);

  i := 0;
	
  while (i < text.Length)
    invariant 0 <= i <= text.Length
		invariant forall i' :: i'>=i ==> (i' !in ret)
    invariant forall idx :: 0 <= idx < i ==> (slice_eq(0, pattern, idx, text, pattern.Length) <==> slice_eq(0, conc, idx + (pattern.Length + 1), conc, pattern.Length))
    invariant forall idx :: 0 <= idx < i ==> (zs[idx + (pattern.Length + 1)] >= pattern.Length <==> idx in ret)
  {
    if (zs[i + (pattern.Length + 1)] >= pattern.Length) {
      ret := ret + [i];
    } 
		i := i+1;
  }
}

method Main() {
  var pattern := "ana";
  var text := "banana";

  var pattern' := array_of_string(pattern);
  var text' := array_of_string(text);

  var b := matches(pattern', text');
  print b;
  print "\n";
}
