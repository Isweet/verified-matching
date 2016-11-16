/* Array Predicates */

predicate nonempty <T> (arr : array<T>)
{
  arr != null && 0 < arr.Length
}

predicate same_size <S, T> (arr1 : array<S>, arr2 : array<T>)
  requires nonempty(arr1)
  requires nonempty(arr2)
{
  arr1.Length == arr2.Length
}

predicate valid_idx <T> (idx : int, arr : array<T>)
  requires nonempty(arr)
{
  0 <= idx < arr.Length
}

/* NOTE: Maybe slices could be a record? Not worth it right now. */

predicate valid_slice <T> (start : int, size : int, arr : array<T>)
  requires nonempty(arr)
{
  forall idx :: start <= idx < start + size ==> valid_idx(idx, arr)
}
/*
predicate slice_eq <T(==)> (start1 : int, arr1 : array<T>, start2 : int, arr2 : array<T>, size : int)
  reads arr1
  reads arr2
  requires nonempty(arr1)
  requires nonempty(arr2)
  requires valid_slice(start1, size, arr1)
  requires valid_slice(start2, size, arr2)
{
  forall offset :: 0 <= offset < size ==> arr1[start1] == arr2[start2]
}
*/
/* Z Predicates */

predicate z_zero_correct (zs : array<int>)
  reads zs
  requires nonempty(zs)
{
  zs[0] == 0
}

predicate z_nonzero_correct(str : array<char>, zs : array<int>)
  reads str
  reads zs
  requires same_size(str, zs)
  requires forall k :: 1 <= k < zs.Length ==> k + zs[k] <= zs.Length
{
  forall idx :: 1 <= idx < zs.Length ==> forall k :: 0 <= k < zs[idx] ==> str[k] == str[idx + k]
}

method z_algorithm_naive(str : array<char>) returns (zs : array<int>)
  requires nonempty(str)

  ensures same_size(str, zs)
  ensures z_zero_correct(zs)
  ensures forall k :: 1 <= k < zs.Length ==> k + zs[k] <= zs.Length // TODO: Add Z's sanity check predicate
  ensures z_nonzero_correct(str, zs)
{ // TODO: Refactor invariants as predicates
  zs := new int[str.Length];

  zs[0] := 0;

  var i := 1;

  while (i < zs.Length)
    invariant 1 <= i <= zs.Length
    invariant z_zero_correct(zs)
    invariant forall k :: 1 <= k < i ==> k + zs[k] <= zs.Length
    invariant forall k :: 1 <= k < i ==> forall l :: 0 <= l < zs[k] ==> str[l] == str[k + l]
  {
    var j := 0;

    while (j < zs.Length - i)
      invariant 0 <= j <= zs.Length - i
      invariant forall k :: 0 <= k < j ==> str[k] == str[i + k]
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
  requires nonempty(str)
  ensures same_size(str, zs)
  ensures z_zero_correct(zs)
  ensures forall k :: 1 <= k < zs.Length ==> k + zs[k] <= zs.Length // TODO: Add Z's sanity check predicate
  ensures z_nonzero_correct(str, zs)
{
  zs := new int[str.Length];
  zs[0] := 0;
  var maxZ := 0;
  var j := 0;
  var i := 1;
  
  while (i< zs.Length)
    invariant 1 <= i <= zs.Length
    invariant z_zero_correct(zs)
    invariant j < i
    invariant forall k :: 1 <= k < i ==> k + zs[k] <= zs.Length
    invariant j+zs[j] == maxZ
    invariant maxZ <= zs.Length
    invariant forall k :: 1 <= k < i ==> forall l :: 0 <= l < zs[k] ==> str[l] == str[k + l]
  {
    if (maxZ < i){
      var l := 0;
      zs[i] := 0;
      
      while (i+l<str.Length) && (str[i+l]==str[l])
        invariant 1 <= i+l <= str.Length
        invariant forall k :: 1 <= k < i ==> k + zs[k] <= zs.Length
        invariant i+zs[i] <= zs.Length
        invariant zs[i] == l
        invariant z_zero_correct(zs)
        invariant maxZ <= zs.Length
        invariant forall k :: 1 <= k < i ==> forall l :: 0 <= l < zs[k] ==> str[l] == str[k + l]
        invariant forall m :: 0 <= m < zs[i] ==> str[m] == str[i+m]
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
            invariant forall k :: 1 <= k < i ==> k + zs[k] <= zs.Length
            invariant maxZ <= zs.Length
            invariant i+zs[i] <= zs.Length
            invariant zs[i] == l
            invariant forall k :: 1 <= k < i ==> forall l :: 0 <= l < zs[k] ==> str[l] == str[k + l]
            invariant forall m :: 0 <= m < zs[i] ==> str[m] == str[i+m]
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

method print_arr <T> (arr : array<T>)
  requires nonempty(arr)
{
  var i := 0;

  print "[";

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

  ensures nonempty(ret)
{
  ret := new char[|str|];

  var i := 0;

  while (i < |str|)
  {
    ret[i] := str[i];

    i := i + 1;
  }
}

method Main() {
  var str := "heheh";
  var str_as_arr := array_of_string(str);
  print_arr(str_as_arr);
  var res := z_algorithm(str_as_arr);
  print_arr(res);
}
