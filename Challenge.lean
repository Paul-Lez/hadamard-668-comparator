import Mathlib

open Matrix

namespace Hadamard

abbrev C := Fin 166
abbrev Q := Fin 4

/-- Packed forms of the four length-166 sign sequences; a set bit means $+1$. -/
def sBits : Q → BitVec 166 :=
  ![0x125953fe2c4fbd9e46d5424b2a5fc58e084c372557#166,
    0x383e32a915b5fb694a447f07c65522b4c092deb770#166,
    0x71876112ff7760ef2e578e30ec225fd913e21a350#166,
    0x14c464e997f8fcd16f35c2988c8d32fce065d21947#166]

/-- Decode one entry of a stored sequence as the integer $+1$ or $-1$. -/
def s (q : Q) (i : C) : ℤ := if (sBits q).getLsb i then 1 else -1

/-- The permutation matrix $R$ for the map $i \mapsto -i$ on $\mathbb Z/166\mathbb Z$. -/
def R : Matrix C C ℤ := (Equiv.neg C).permMatrix ℤ

/-- The circulant matrix $S(x)$ with entries $S(x)_{ij}=x_{i-j}$. -/
def S (x : C → ℤ) : Matrix C C ℤ := Matrix.circulant x

/-- The $4\times4$ block array defining the $664\times664$ core matrix. -/
def M_blocks (a b c d : C → ℤ) : Matrix Q Q (Matrix C C ℤ) :=
  let A := S a
  let B := S b
  let C := S c
  let D := S d
  !![A, B * R, C * R, D * R;
     -(B * R), A, D.transpose * R, -(C.transpose * R);
     -(C * R), -(D.transpose * R), A, B.transpose * R;
     -(D * R), C.transpose * R, -(B.transpose * R), A]

/-- The $664\times664$ core matrix $M$. -/
def M : Matrix (Q × C) (Q × C) ℤ := fun i j =>
  M_blocks (s 0) (s 1) (s 2) (s 3) i.1 j.1 i.2 j.2

/-- The fixed $4\times4$ northwest block $X$. -/
def X : Matrix Q Q ℤ :=
  !![-1, 1, 1, -1;
      1, -1, 1, -1;
      1, 1, -1, -1;
      -1, -1, -1, -1]

/-- The $4\times4$ sign pattern $Y$ for the top-right block. -/
def Y : Matrix Q Q ℤ :=
  !![1, -1, -1, 1;
     1, -1, 1, -1;
     1, 1, -1, -1;
     -1, -1, -1, -1]

/-- The $4\times4$ sign pattern $Z$ for the bottom-left block. -/
def Z : Matrix Q Q ℤ :=
  !![-1, -1, -1, 1;
     -1, -1, 1, -1;
     -1, 1, -1, -1;
     1, -1, -1, -1]

/-- Repeat each entry of `Y` across a block of 166 columns. -/
def Y_tilde : Matrix Q (Q × C) ℤ := fun i j => Y i j.1

/-- Repeat each entry of `Z` across a block of 166 rows. -/
def Z_tilde : Matrix (Q × C) Q ℤ := fun i j => Z i.1 j

def H_blocks : Matrix (Q ⊕ (Q × C)) (Q ⊕ (Q × C)) ℤ :=
  Matrix.fromBlocks X Y_tilde Z_tilde M

def indexEquiv : (Q ⊕ (Q × C)) ≃ Fin 668 :=
  (Equiv.sumCongr (Equiv.refl Q) finProdFinEquiv).trans finSumFinEquiv

/-- The order-668 integer matrix constructed above. -/
def H : Matrix (Fin 668) (Fin 668) ℤ :=
  Matrix.reindex indexEquiv indexEquiv H_blocks

/-- The displayed matrix `H` is Hadamard. -/
theorem H_isHadamard : H.IsHadamard := by
  sorry

theorem exists_hadamard_668 : ∃ (H : Matrix (Fin 668) (Fin 668) ℤ), H.IsHadamard := by
  sorry

end Hadamard
