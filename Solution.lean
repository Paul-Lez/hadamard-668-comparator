/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import Mathlib

open Matrix

namespace Hadamard

private abbrev C := Fin 166
private abbrev Q := Fin 4

-- The matrix construction

/-- Packed forms of the four length-166 sign sequences; a set bit means $+1$. -/
private def sBits : Q → BitVec 166 :=
  ![0x125953fe2c4fbd9e46d5424b2a5fc58e084c372557#166,
    0x383e32a915b5fb694a447f07c65522b4c092deb770#166,
    0x71876112ff7760ef2e578e30ec225fd913e21a350#166,
    0x14c464e997f8fcd16f35c2988c8d32fce065d21947#166]

/-- Decode one entry of a stored sequence as the integer $+1$ or $-1$. -/
private def s (q : Q) (i : C) : ℤ := if (sBits q).getLsb i then 1 else -1

/-- The permutation matrix $R$ for the map $i \mapsto -i$ on $\mathbb Z/166\mathbb Z$. -/
private def R : Matrix C C ℤ := (Equiv.neg C).permMatrix ℤ

/-- The circulant matrix $S(x)$ with entries $S(x)_{ij}=x_{i-j}$. -/
private def S (x : C → ℤ) : Matrix C C ℤ := Matrix.circulant x

/-- The $4\times4$ block array defining the $664\times664$ core matrix. -/
private def M_blocks (a b c d : C → ℤ) : Matrix Q Q (Matrix C C ℤ) :=
  let A := S a
  let B := S b
  let C := S c
  let D := S d
  !![A, B * R, C * R, D * R;
     -(B * R), A, D.transpose * R, -(C.transpose * R);
     -(C * R), -(D.transpose * R), A, B.transpose * R;
     -(D * R), C.transpose * R, -(B.transpose * R), A]

/-- The $4\times4$ block array flattened into a $664\times664$ matrix. -/
private def M : Matrix (Q × C) (Q × C) ℤ := fun i j =>
  M_blocks (s 0) (s 1) (s 2) (s 3) i.1 j.1 i.2 j.2

/-- The fixed $4\times4$ northwest block $X$. -/
private def X : Matrix Q Q ℤ :=
  !![-1, 1, 1, -1;
      1, -1, 1, -1;
      1, 1, -1, -1;
      -1, -1, -1, -1]

/-- The $4\times4$ sign pattern $Y$ for the top-right block. -/
private def Y : Matrix Q Q ℤ :=
  !![1, -1, -1, 1;
     1, -1, 1, -1;
     1, 1, -1, -1;
     -1, -1, -1, -1]

/-- The $4\times4$ sign pattern $Z$ for the bottom-left block. -/
private def Z : Matrix Q Q ℤ :=
  !![-1, -1, -1, 1;
     -1, -1, 1, -1;
     -1, 1, -1, -1;
     1, -1, -1, -1]

/-- Repeat each entry of `Y` across a block of 166 columns. -/
private def Y_tilde : Matrix Q (Q × C) ℤ := fun i j => Y i j.1

/-- Repeat each entry of `Z` across a block of 166 rows. -/
private def Z_tilde : Matrix (Q × C) Q ℤ := fun i j => Z i.1 j

/-- Adjoin the four border rows and columns to `M`. -/
private def H_blocks : Matrix (Q ⊕ (Q × C)) (Q ⊕ (Q × C)) ℤ :=
  Matrix.fromBlocks X Y_tilde Z_tilde M

private def indexEquiv : (Q ⊕ (Q × C)) ≃ Fin 668 :=
  (Equiv.sumCongr (Equiv.refl Q) finProdFinEquiv).trans finSumFinEquiv

/-- The order-668 integer matrix constructed above. -/
def H : Matrix (Fin 668) (Fin 668) ℤ :=
  Matrix.reindex indexEquiv indexEquiv H_blocks

-- Auxiliary definitions

private def M_blocksT (a b c d : C → ℤ) : Matrix Q Q (Matrix C C ℤ) :=
  let A := S a
  let B := S b
  let C := S c
  let D := S d
  !![A.transpose, -(B * R), -(C * R), -(D * R);
     B * R, A.transpose, -(D.transpose * R), C.transpose * R;
     C * R, D.transpose * R, A.transpose, -(B.transpose * R);
     D * R, -(C.transpose * R), B.transpose * R, A.transpose]

/-- The $(q,r)$ block of the Gram matrix of `M_blocks`. -/
private def blockGram (a b c d : C → ℤ) (q r : Q) : Matrix C C ℤ :=
  ∑ p : Q, (M_blocks a b c d p q).transpose * M_blocks a b c d p r

/-- The sum of the four circulant Gram matrices. -/
private def autoSum (a b c d : C → ℤ) : Matrix C C ℤ :=
  (S a).transpose * S a + (S b).transpose * S b +
    (S c).transpose * S c + (S d).transpose * S d

private def M_block_sums (sa sb sc sd : ℤ) : Matrix Q Q ℤ :=
  !![sa, sb, sc, sd;
     -sb, sa, sd, -sc;
     -sc, -sd, sa, sb;
     -sd, sc, -sb, sa]

/-- The dot product of a sign sequence with its cyclic shift by $t$. -/
private def periodicCorrelation (x : C → ℤ) (t : C) : ℤ :=
  ∑ i : C, x i * x (i + t)

/-- The sum of the periodic autocorrelations of four sequences. -/
private def autoKernel (a b c d : C → ℤ) : C → ℤ :=
  fun t => periodicCorrelation a t + periodicCorrelation b t +
    periodicCorrelation c t + periodicCorrelation d t

/-- The total periodic autocorrelation of the four stored sequences. -/
private def totalCorrelation (t : C) : ℤ :=
  ∑ q : Q, periodicCorrelation (s q) t

private def IsSign (z : ℤ) : Prop := z = 1 ∨ z = -1

-- Properties of the construction

private lemma s_sum (q : Q) : ∑ i, s q i = if q = 0 then 2 else 0 := by
  fin_cases q <;> decide +kernel

private lemma r_transpose : R.transpose = R := by
  change ((Equiv.neg C).permMatrix ℤ).transpose = (Equiv.neg C).permMatrix ℤ
  rw [Matrix.transpose_permMatrix]
  congr

private lemma r_mul_r : R * R = 1 := by
  have h : (Equiv.neg C : Equiv.Perm C) * Equiv.neg C = 1 := by
    ext i
    simp
  change (Equiv.neg C).permMatrix ℤ * (Equiv.neg C).permMatrix ℤ = 1
  rw [← Matrix.permMatrix_mul (R := ℤ) (Equiv.neg C) (Equiv.neg C)]
  rw [h, Matrix.permMatrix_one]

private lemma r_mul_s (x : C → ℤ) : R * S x = (S x).transpose * R := by
  rw [R, S, PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
  ext i j
  simp [Matrix.circulant, sub_eq_add_neg, add_comm]

private lemma r_mul_s_transpose (x : C → ℤ) :
    R * (S x).transpose = S x * R := by
  rw [R, PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
  ext i j
  simp [S, Matrix.circulant, sub_eq_add_neg, add_comm]

private lemma s_comm (x y : C → ℤ) : S x * S y = S y * S x := by
  exact Matrix.Fin.circulant_mul_comm x y

private lemma s_transpose_comm (x y : C → ℤ) :
    (S x).transpose * S y = S y * (S x).transpose := by
  simpa only [S, Matrix.transpose_circulant] using
    Matrix.Fin.circulant_mul_comm (fun i => x (-i)) y

private lemma s_transpose_comm_transpose (x y : C → ℤ) :
    (S x).transpose * (S y).transpose = (S y).transpose * (S x).transpose := by
  simpa only [S, Matrix.transpose_circulant] using
    Matrix.Fin.circulant_mul_comm (fun i => x (-i)) (fun i => y (-i))

private lemma s_normal (x : C → ℤ) :
    S x * (S x).transpose = (S x).transpose * S x := by
  exact (s_transpose_comm x x).symm

private lemma s_r_mul_s_r (x y : C → ℤ) :
    (S x * R) * (S y * R) = S x * (S y).transpose := by
  calc
    (S x * R) * (S y * R) = S x * (R * S y) * R := by
      noncomm_ring
    _ = S x * ((S y).transpose * R) * R := by rw [r_mul_s]
    _ = S x * (S y).transpose * (R * R) := by noncomm_ring
    _ = S x * (S y).transpose := by rw [r_mul_r, Matrix.mul_one]

private lemma s_r_mul_s_transpose_r (x y : C → ℤ) :
    (S x * R) * ((S y).transpose * R) = S x * S y := by
  calc
    (S x * R) * ((S y).transpose * R) =
        S x * (R * (S y).transpose) * R := by noncomm_ring
    _ = S x * (S y * R) * R := by rw [r_mul_s_transpose]
    _ = S x * S y * (R * R) := by noncomm_ring
    _ = S x * S y := by rw [r_mul_r, Matrix.mul_one]

private lemma s_transpose_r_mul_s_r (x y : C → ℤ) :
    ((S x).transpose * R) * (S y * R) =
      (S x).transpose * (S y).transpose := by
  calc
    ((S x).transpose * R) * (S y * R) =
        (S x).transpose * (R * S y) * R := by noncomm_ring
    _ = (S x).transpose * ((S y).transpose * R) * R := by
      rw [r_mul_s]
    _ = (S x).transpose * (S y).transpose * (R * R) := by noncomm_ring
    _ = (S x).transpose * (S y).transpose := by rw [r_mul_r, Matrix.mul_one]

private lemma s_transpose_r_mul_s_transpose_r (x y : C → ℤ) :
    ((S x).transpose * R) * ((S y).transpose * R) =
      (S x).transpose * S y := by
  calc
    ((S x).transpose * R) * ((S y).transpose * R) =
        (S x).transpose * (R * (S y).transpose) * R := by noncomm_ring
    _ = (S x).transpose * (S y * R) * R := by rw [r_mul_s_transpose]
    _ = (S x).transpose * S y * (R * R) := by noncomm_ring
    _ = (S x).transpose * S y := by rw [r_mul_r, Matrix.mul_one]

private lemma s_transpose_mul_s_r (x y : C → ℤ) :
    (S x).transpose * (S y * R) = (S y * R) * S x := by
  rw [Matrix.mul_assoc, r_mul_s]
  rw [← Matrix.mul_assoc, s_transpose_comm]
  noncomm_ring

private lemma s_transpose_mul_s_transpose_r (x y : C → ℤ) :
    (S x).transpose * ((S y).transpose * R) =
      ((S y).transpose * R) * S x := by
  rw [Matrix.mul_assoc, r_mul_s]
  rw [← Matrix.mul_assoc, s_transpose_comm_transpose]
  noncomm_ring

private lemma m_blocks_transpose (a b c d : C → ℤ) (p q : Q) :
    (M_blocks a b c d p q).transpose = M_blocksT a b c d q p := by
  fin_cases p <;> fin_cases q <;>
    simp [M_blocks, M_blocksT, r_transpose, r_mul_s, r_mul_s_transpose]

private lemma blockGram_all (a b c d : C → ℤ) (q r : Q) :
    blockGram a b c d q r = if q = r then autoSum a b c d else 0 := by
  simp only [blockGram, m_blocks_transpose]
  fin_cases q <;> fin_cases r
  all_goals
    simp [M_blocks, M_blocksT, autoSum, Fin.sum_univ_four, s_r_mul_s_r,
      s_r_mul_s_transpose_r, s_transpose_r_mul_s_r,
      s_transpose_r_mul_s_transpose_r, s_transpose_mul_s_r,
      s_transpose_mul_s_transpose_r, s_normal]
  all_goals try rw [s_transpose_comm]
  all_goals try rw [s_comm]
  all_goals try rw [s_transpose_comm_transpose]
  all_goals abel

private lemma periodicCorrelation_neg (x : C → ℤ) (t : C) :
    periodicCorrelation x (-t) = periodicCorrelation x t := by
  rw [periodicCorrelation, periodicCorrelation,
    ← Equiv.sum_comp (Equiv.addRight t) (fun i : C => x i * x (i + -t))]
  apply Finset.sum_congr rfl
  intro i _
  simp [mul_comm]

private lemma s_gram_apply (x : C → ℤ) (i j : C) :
    ((S x).transpose * S x) i j = periodicCorrelation x (i - j) := by
  rw [Matrix.mul_apply]
  simp only [Matrix.transpose_apply, S, Matrix.circulant_apply, periodicCorrelation]
  rw [← Equiv.sum_comp (Equiv.addRight i)
    (fun k : C => x (k - i) * x (k - j))]
  apply Finset.sum_congr rfl
  intro k _
  congr 2 <;> simp [add_sub_assoc]

private lemma autoSum_eq_circulant (a b c d : C → ℤ) :
    autoSum a b c d = Matrix.circulant (autoKernel a b c d) := by
  ext i j
  simp [autoSum, autoKernel, s_gram_apply, Matrix.circulant_apply]

private lemma totalCorrelation_neg (t : C) : totalCorrelation (-t) = totalCorrelation t := by
  simp [totalCorrelation, periodicCorrelation_neg]

private lemma totalCorrelation_zero : totalCorrelation 0 = 664 := by
  decide +kernel

private lemma totalCorrelation_first_half (t : C) (hlo : 1 ≤ t.val) (hhi : t.val < 84) :
    totalCorrelation t = -4 := by
  rcases t with ⟨t, ht⟩
  interval_cases t <;> decide +kernel +revert

private lemma totalCorrelation_nonzero (t : C) (ht : t ≠ 0) : totalCorrelation t = -4 := by
  have ht0 : 1 ≤ t.val := by
    by_contra h
    have : t.val = 0 := by omega
    exact ht (Fin.ext this)
  by_cases h84 : t.val < 84
  · exact totalCorrelation_first_half t ht0 h84
  · rw [← totalCorrelation_neg t]
    have hneg : (-t).val = 166 - t.val := by
      rw [Fin.val_neg']
      exact Nat.mod_eq_of_lt (by omega)
    apply totalCorrelation_first_half (-t) <;> omega

private lemma autoKernel_s (t : C) :
    autoKernel (s 0) (s 1) (s 2) (s 3) t = totalCorrelation t := by
  simp [autoKernel, totalCorrelation, Fin.sum_univ_four]

private lemma autoSum_s_apply (i j : C) :
    autoSum (s 0) (s 1) (s 2) (s 3) i j =
      if i = j then 664 else -4 := by
  rw [autoSum_eq_circulant, Matrix.circulant_apply, autoKernel_s]
  by_cases hij : i = j
  · subst j
    simp [totalCorrelation_zero]
  · rw [ite_eq_right hij, totalCorrelation_nonzero]
    intro h
    apply hij
    exact sub_eq_zero.mp h

private lemma s_col_sum (x : C → ℤ) (j : C) : ∑ i, S x i j = ∑ i, x i := by
  exact Equiv.sum_comp (Equiv.subRight j) x

private lemma s_transpose_col_sum (x : C → ℤ) (j : C) :
    ∑ i, (S x).transpose i j = ∑ i, x i := by
  exact Equiv.sum_comp (Equiv.subLeft j) x

private lemma s_r_col_sum (x : C → ℤ) (j : C) :
    ∑ i, (S x * R) i j = ∑ i, x i := by
  rw [R, Equiv.Perm.permMatrix, PEquiv.mul_toMatrix_toPEquiv]
  exact s_col_sum x ((Equiv.neg C).symm j)

private lemma s_transpose_r_col_sum (x : C → ℤ) (j : C) :
    ∑ i, ((S x).transpose * R) i j = ∑ i, x i := by
  rw [R, Equiv.Perm.permMatrix, PEquiv.mul_toMatrix_toPEquiv]
  exact s_transpose_col_sum x ((Equiv.neg C).symm j)

private lemma m_blocks_col_sum_general (a b c d : C → ℤ) (p q : Q) (j : C) :
    ∑ i, M_blocks a b c d p q i j =
      M_block_sums (∑ i, a i) (∑ i, b i) (∑ i, c i) (∑ i, d i) p q := by
  fin_cases p <;> fin_cases q
  · change (∑ i, S a i j) = ∑ i, a i
    exact s_col_sum a j
  · change (∑ i, (S b * R) i j) = ∑ i, b i
    exact s_r_col_sum b j
  · change (∑ i, (S c * R) i j) = ∑ i, c i
    exact s_r_col_sum c j
  · change (∑ i, (S d * R) i j) = ∑ i, d i
    exact s_r_col_sum d j
  · change (∑ i, -(S b * R) i j) = -(∑ i, b i)
    rw [Finset.sum_neg_distrib, s_r_col_sum]
  · change (∑ i, S a i j) = ∑ i, a i
    exact s_col_sum a j
  · change (∑ i, ((S d).transpose * R) i j) = ∑ i, d i
    exact s_transpose_r_col_sum d j
  · change (∑ i, -((S c).transpose * R) i j) = -(∑ i, c i)
    rw [Finset.sum_neg_distrib, s_transpose_r_col_sum]
  · change (∑ i, -(S c * R) i j) = -(∑ i, c i)
    rw [Finset.sum_neg_distrib, s_r_col_sum]
  · change (∑ i, -((S d).transpose * R) i j) = -(∑ i, d i)
    rw [Finset.sum_neg_distrib, s_transpose_r_col_sum]
  · change (∑ i, S a i j) = ∑ i, a i
    exact s_col_sum a j
  · change (∑ i, ((S b).transpose * R) i j) = ∑ i, b i
    exact s_transpose_r_col_sum b j
  · change (∑ i, -(S d * R) i j) = -(∑ i, d i)
    rw [Finset.sum_neg_distrib, s_r_col_sum]
  · change (∑ i, ((S c).transpose * R) i j) = ∑ i, c i
    exact s_transpose_r_col_sum c j
  · change (∑ i, -((S b).transpose * R) i j) = -(∑ i, b i)
    rw [Finset.sum_neg_distrib, s_transpose_r_col_sum]
  · change (∑ i, S a i j) = ∑ i, a i
    exact s_col_sum a j

private lemma m_block_sums_s : M_block_sums 2 0 0 0 = (2 : Matrix Q Q ℤ) := by
  ext p q
  fin_cases p <;> fin_cases q <;> norm_num [M_block_sums, Matrix.ofNat_apply]

private lemma m_blocks_col_sum (p q : Q) (j : C) :
    ∑ i, M_blocks (s 0) (s 1) (s 2) (s 3) p q i j =
      if p = q then 2 else 0 := by
  rw [m_blocks_col_sum_general]
  simp [s_sum, m_block_sums_s, Matrix.ofNat_apply]

private lemma m_gram_apply (q r : Q) (i j : C) :
    (M.transpose * M) (q, i) (r, j) =
      if q = r then autoSum (s 0) (s 1) (s 2) (s 3) i j else 0 := by
  by_cases hqr : q = r
  · subst r
    rw [ite_eq_left rfl, Matrix.mul_apply, Fintype.sum_prod_type]
    have h := congrArg (fun M : Matrix C C ℤ => M i j)
      (blockGram_all (s 0) (s 1) (s 2) (s 3) q q)
    rw [ite_eq_left rfl] at h
    simpa only [M, blockGram, Matrix.sum_apply, Matrix.mul_apply,
      Matrix.transpose_apply]
      using h
  · rw [ite_eq_right hqr, Matrix.mul_apply, Fintype.sum_prod_type]
    have h := congrArg (fun M : Matrix C C ℤ => M i j)
      (blockGram_all (s 0) (s 1) (s 2) (s 3) q r)
    rw [ite_eq_right hqr] at h
    simpa only [M, blockGram, Matrix.sum_apply, Matrix.mul_apply,
      Matrix.transpose_apply, Matrix.zero_apply] using h

private lemma x_gram : X.transpose * X = (4 : Matrix Q Q ℤ) := by
  decide +kernel

private lemma y_gram : Y.transpose * Y = (4 : Matrix Q Q ℤ) := by
  decide +kernel

private lemma z_gram : Z.transpose * Z = (4 : Matrix Q Q ℤ) := by
  decide +kernel

private lemma x_y_cross : X.transpose * Y + 2 • Z.transpose = 0 := by
  decide +kernel

private lemma s_sign (q : Q) (i : C) : IsSign (s q i) := by
  simp only [IsSign, s]
  split <;> simp

private lemma sign_neg {z : ℤ} (hz : IsSign z) : IsSign (-z) := by
  rcases hz with rfl | rfl <;> simp [IsSign]

private lemma s_matrix_sign (q : Q) (i j : C) : IsSign (S (s q) i j) := by
  exact s_sign q (i - j)

private lemma s_transpose_sign (q : Q) (i j : C) :
    IsSign ((S (s q)).transpose i j) := by
  exact s_sign q (j - i)

private lemma s_r_apply (x : C → ℤ) (i j : C) :
    (S x * R) i j = S x i ((Equiv.neg C).symm j) := by
  rw [R, Equiv.Perm.permMatrix, PEquiv.mul_toMatrix_toPEquiv]
  rfl

private lemma s_r_sign (q : Q) (i j : C) :
    IsSign ((S (s q) * R) i j) := by
  rw [s_r_apply]
  exact s_matrix_sign q i ((Equiv.neg C).symm j)

private lemma s_transpose_r_sign (q : Q) (i j : C) :
    IsSign (((S (s q)).transpose * R) i j) := by
  rw [R, Equiv.Perm.permMatrix, PEquiv.mul_toMatrix_toPEquiv]
  exact s_transpose_sign q i ((Equiv.neg C).symm j)

private lemma m_sign (i j : Q × C) : IsSign (M i j) := by
  rcases i with ⟨p, i⟩
  rcases j with ⟨q, j⟩
  fin_cases p <;> fin_cases q <;> simp only [M, M_blocks]
  all_goals first
    | exact s_matrix_sign 0 i j
    | exact s_r_sign 1 i j
    | exact s_r_sign 2 i j
    | exact s_r_sign 3 i j
    | exact sign_neg (s_r_sign 1 i j)
    | exact sign_neg (s_r_sign 2 i j)
    | exact sign_neg (s_r_sign 3 i j)
    | exact s_transpose_r_sign 1 i j
    | exact s_transpose_r_sign 2 i j
    | exact s_transpose_r_sign 3 i j
    | exact sign_neg (s_transpose_r_sign 1 i j)
    | exact sign_neg (s_transpose_r_sign 2 i j)
    | exact sign_neg (s_transpose_r_sign 3 i j)

private lemma h_blocks_sign (i j : Q ⊕ (Q × C)) : IsSign (H_blocks i j) := by
  rcases i with i | i <;> rcases j with j | j
  · fin_cases i <;> fin_cases j <;> simp [H_blocks, X, Matrix.fromBlocks, IsSign]
  · fin_cases i <;> rcases j with ⟨q, _j⟩ <;> fin_cases q <;>
      simp [H_blocks, Y_tilde, Y, Matrix.fromBlocks, IsSign]
  · rcases i with ⟨p, _i⟩
    fin_cases p <;> fin_cases j <;>
      simp [H_blocks, Z_tilde, Z, Matrix.fromBlocks, IsSign]
  · exact m_sign i j

private lemma z_tilde_gram :
    Z_tilde.transpose * Z_tilde = (664 : Matrix Q Q ℤ) := by
  ext i j
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  change (∑ p : Q, ∑ _k : C, Z p i * Z p j) = _
  calc
    (∑ p : Q, ∑ _k : C, Z p i * Z p j) =
        166 * ∑ p : Q, Z p i * Z p j := by
      simp [Finset.mul_sum]
    _ = 166 * (Z.transpose * Z) i j := by simp [Matrix.mul_apply]
    _ = (664 : Matrix Q Q ℤ) i j := by rw [z_gram]; simp [Matrix.ofNat_apply]

private lemma y_tilde_gram_apply (q r : Q) (i j : C) :
    (Y_tilde.transpose * Y_tilde) (q, i) (r, j) =
      if q = r then 4 else 0 := by
  change (∑ x, Y x q * Y x r) = _
  calc
    (∑ x, Y x q * Y x r) = (Y.transpose * Y) q r := by
      rfl
    _ = _ := by rw [y_gram]; simp [Matrix.ofNat_apply]

private lemma z_tilde_m_mul_apply (j : Q) (q : Q) (b : C) :
    (Z_tilde.transpose * M) j (q, b) = 2 * Z.transpose j q := by
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  change (∑ p : Q, ∑ k : C, Z p j *
    M_blocks (s 0) (s 1) (s 2) (s 3) p q k b) = _
  simp_rw [← Finset.mul_sum, m_blocks_col_sum]
  simp [Matrix.transpose_apply]
  ring

private lemma boundary_gram :
    X.transpose * X + Z_tilde.transpose * Z_tilde =
      (668 : Matrix Q Q ℤ) := by
  rw [x_gram, z_tilde_gram]
  ext i j
  by_cases hij : i = j <;> simp [hij, Matrix.ofNat_apply]

private lemma core_border_gram :
    Y_tilde.transpose * Y_tilde + M.transpose * M =
      (668 : Matrix (Q × C) (Q × C) ℤ) := by
  ext ⟨q, i⟩ ⟨r, j⟩
  rw [Matrix.add_apply, y_tilde_gram_apply, m_gram_apply]
  by_cases hqr : q = r
  · subst r
    rw [ite_eq_left rfl, autoSum_s_apply]
    by_cases hij : i = j
    · subst j
      simp [Matrix.ofNat_apply]
    · simp [hij, Matrix.ofNat_apply]
  · simp [hqr, Matrix.ofNat_apply]

private lemma border_core_cross :
    X.transpose * Y_tilde + Z_tilde.transpose * M = 0 := by
  ext j ⟨q, b⟩
  rw [Matrix.add_apply, z_tilde_m_mul_apply]
  have h := congrArg (fun M : Matrix Q Q ℤ => M j q) x_y_cross
  simpa only [Y_tilde, Matrix.mul_apply, Matrix.transpose_apply, Matrix.add_apply,
    Matrix.smul_apply, Matrix.zero_apply, two_nsmul, two_mul] using h

private lemma core_border_cross :
    Y_tilde.transpose * X + M.transpose * Z_tilde = 0 := by
  have h := congrArg Matrix.transpose border_core_cross
  simpa only [Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.transpose_zero] using h

private lemma h_blocks_gram :
    H_blocks.transpose * H_blocks =
      (668 : Matrix (Q ⊕ (Q × C)) (Q ⊕ (Q × C)) ℤ) := by
  rw [H_blocks, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply,
    boundary_gram, border_core_cross, core_border_cross, core_border_gram]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [Matrix.fromBlocks, Matrix.ofNat_apply]

/-- Every entry of `H` is $+1$ or $-1$. -/
private theorem H_sign (i j : Fin 668) : H i j = 1 ∨ H i j = -1 := by
  exact h_blocks_sign (indexEquiv.symm i) (indexEquiv.symm j)

set_option maxRecDepth 10000 in
/-- The columns of `H` are pairwise orthogonal and have squared norm 668. -/
private theorem H_gram :
    H.transpose * H = (668 : Matrix (Fin 668) (Fin 668) ℤ) := by
  change (Matrix.reindex indexEquiv indexEquiv H_blocks).transpose *
    Matrix.reindex indexEquiv indexEquiv H_blocks = _
  rw [Matrix.transpose_reindex]
  rw [← Matrix.coe_reindexAlgEquiv ℤ ℤ indexEquiv, ← map_mul, h_blocks_gram]
  rw [Matrix.coe_reindexAlgEquiv]
  ext i j
  simp [Matrix.reindex, Matrix.ofNat_apply]

/-- The displayed matrix `H` is Hadamard. -/
theorem H_isHadamard : H.IsHadamard := by
  have htranspose : H.transpose.IsHadamard := by
    apply Matrix.IsHadamard.of_mul_conjTranspose
    · intro i j
      exact Unitary.mem_iff_eq_one_or_eq_neg_one.mpr (H_sign j i)
    · rw [conjTranspose_eq_transpose_of_trivial, transpose_transpose]
      simpa using H_gram
    · norm_num [isRegular_iff_ne_zero']
  simpa using htranspose.transpose

end Hadamard
