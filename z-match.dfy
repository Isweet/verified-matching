/* Integer Predicates */

predicate positive (i : int)
{
  1 <= i
}

predicate nonnegative (i : int)
{
  0 <= i
}

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

/* NOTE: Maybe slices could be a record? Not worth it right now. */

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
{ // TODO: Refactor invariants as predicates
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
  var maxZ := 0;
  var j := 0;
  var i := 1;
  
  while (i< zs.Length)
    invariant 1 <= i <= zs.Length
    invariant z_zero_correct(zs)
    invariant forall k :: 1 <= k < i ==> valid_slice(k, zs[k], zs)
    invariant j < i
    invariant j+zs[j] == maxZ
    invariant maxZ <= zs.Length
    invariant forall k :: 1 <= k < i ==> slice_eq(0, str, k, str, zs[k])
    invariant forall idx :: 1 <= idx < i ==> forall k :: 0 <= k <= str.Length - idx ==>
      (zs[idx] >= k ==> slice_eq(0, str, idx, str, k))
    invariant forall idx :: 1 <= idx < i ==> forall k :: 0 <= k <= str.Length - idx ==>
      (slice_eq(0, str, idx, str, k) ==> zs[idx] >= k)
  {
    if (maxZ < i){
      var l := 0;
      zs[i] := 0;
      
      while (i+l<str.Length) && (str[i+l]==str[l])
        invariant 1 <= i+l <= str.Length
        invariant z_zero_correct(zs)
        invariant forall k :: 1 <= k < i ==> valid_slice(k, zs[k], zs)
        invariant i+zs[i] <= zs.Length
        invariant zs[i] == l
        invariant maxZ <= zs.Length
        invariant forall k :: 1 <= k < i ==> slice_eq(0, str, k, str, zs[k])
        invariant slice_eq(0, str, i, str, zs[i])
        invariant forall idx :: 1 <= idx < i ==> forall k :: 0 <= k <= str.Length - idx ==>
          (zs[idx] >= k ==> slice_eq(0, str, idx, str, k))
        invariant forall idx :: 1 <= idx < i ==> forall k :: 0 <= k <= str.Length - idx ==>
          (slice_eq(0, str, idx, str, k) ==> zs[idx] >= k)
        invariant forall k :: 0 <= k <= l ==> slice_eq(0, str, i, str, k) ==> zs[i] >= k

      {
        zs[i] := zs[i]+1;
        l := l+1;  
      }
      maxZ := i+zs[i];
      j:= i;
    }
    else{
      assert (i <= j + zs[j]);
      var k := i-j;
      if (zs[k]+i < maxZ){ // case 1
        zs[i] := zs[k];
      }
      else if (zs[k]+i>maxZ){ // case 2
        zs[i] := maxZ-i;
      }
      else { // case 3: zs[k]+i == maxZ 
        zs[i] := maxZ-i;
        var l := zs[i];
        while (i+l<str.Length) && (str[i+l]==str[l])
            invariant 1 <= i <= zs.Length
            invariant z_zero_correct(zs)
            invariant forall k :: 1 <= k < i ==> valid_slice(k, zs[k], zs)
            invariant maxZ <= zs.Length
            invariant i+zs[i] <= zs.Length
            invariant zs[i] == l
            invariant forall k :: 1 <= k < i ==> slice_eq(0, str, k, str, zs[k])
            invariant slice_eq(0, str, i, str, zs[i])
            invariant forall idx :: 1 <= idx < i ==> forall k :: 0 <= k <= str.Length - idx ==>
              (zs[idx] >= k ==> slice_eq(0, str, idx, str, k))
            invariant forall idx :: 1 <= idx < i ==> forall k :: 0 <= k <= str.Length - idx ==>
              (slice_eq(0, str, idx, str, k) ==> zs[idx] >= k)
            invariant forall k :: 0 <= k <= l ==> slice_eq(0, str, i, str, k) ==> zs[i] >= k
        {
          zs[i] := zs[i]+1;
          l := l+1;
        }
        maxZ := i+zs[i];
        j:=i;
      }
    }
    i := i+1;
  }
}

/*

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

method matches(pattern : array<char>, text : array<char>) returns (ret : int)
  requires nonnull(pattern)
  requires nonnull(text)
  requires !contains('$', pattern)
  requires !contains('$', text)

  //ensures (ret != -1 && slice_eq(0, pattern, ret, text, pattern.Length)) || (ret == -1 && forall idx :: 0 <= idx < text.Length ==> !slice_eq(0, pattern, idx, text, pattern.Length))
{

  ret := -1;

  var conc := new char[pattern.Length + text.Length + 1];

  var i := 0;

  while (i < conc.Length)
  invariant 0 <= i <= conc.Length
  invariant forall k :: 0 <= k < i ==> if k < pattern.Length then conc[k] == pattern[k] else if k == pattern.Length then conc[k] == '$' else conc[k] == text[k - (pattern.Length + 1)]
  invariant forall k :: 0 <= k < i ==> if k < pattern.Length then slice_eq(0, pattern, 0, conc, k) else if k == pattern.Length then conc[k] == '$' else slice_eq(0, text, pattern.Length + 1, conc, k - (pattern.Length + 1))
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

  //assert(slice_eq(0, pattern, 0, conc, pattern.Length));
  //assert(slice_eq(0, text, pattern.Length + 1, conc, text.Length));

  var zs := z_algorithm(conc);

  // assert(forall idx :: 0 <= idx < zs.Length ==> zs[idx] <= pattern.Length);

  // assert (forall idx :: 0 <= idx < conc.Length ==> if zs[idx] == pattern.Length then slice_eq(0, conc, idx, conc, pattern.Length) else true);
  // assert (forall idx :: 0 <= idx < conc.Length ==> if slice_eq(0, conc, idx, conc, pattern.Length) then slice_eq(0, pattern, idx - (pattern.Length + 1), text, pattern.Length) else true);
  //assert (forall idx :: pattern.Length + 1 <= idx < conc.Length ==> if zs[idx] == pattern.Length then slice_eq(0, pattern, idx - (pattern.Length + 1), text, pattern.Length) else true);

  print_arr(zs);

  i := pattern.Length + 1;

  while (i < conc.Length)
    invariant pattern.Length + 1 <= i <= conc.Length
    //invariant ret == -1 || slice_eq(0, pattern, ret, text, pattern.Length)
    //invariant ret != -1 ==> slice_eq(0, pattern, ret, text, pattern.Length)
    //invariant ret == -1 ==> (forall k :: pattern.Length + 1 <= k < i ==> zs[k] < pattern.Length)
    //invariant ret == -1 ==> (forall k :: pattern.Length + 1 <= k < i ==> !slice_eq(0, pattern, k - (pattern.Length + 1), text, pattern.Length))
    //invariant (ret != -1 && slice_eq(0, pattern, ret, text, pattern.Length)) || (ret == -1 && forall k :: pattern.Length + 1 <= k < i ==> !slice_eq(0, pattern, k - (pattern.Length + 1), text, pattern.Length))
    // invariant b ==> exists idx :: 0 <= idx < i && slice_eq(0, pattern, idx - (pattern.Length + 1), text, pattern.Length)
  {
    if (zs[i] >= pattern.Length) {
      ret := i - (pattern.Length + 1);
      break;
    }

    i := i + 1;
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
*/
