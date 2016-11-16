predicate nonempty <T> (arr : array<T>)
{
  arr != null && 0 < arr.Length
}

predicate same_size <S, T> (arr1 : array<S>, arr2 : array<T>)
{
  nonempty(arr1) && nonempty(arr2) && arr1.Length == arr2.Length
}

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
