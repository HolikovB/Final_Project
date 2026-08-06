import Final_Project.field_aut
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.Tactic

set_option warningAsError false




open Matrix BigOperators
open scoped MatrixGroups
open FieldAutomorphisms

noncomputable section

/-
Part 4 of the project.

This file uses the definitions from `field_aut.lean`.  In particular it uses
`AutSL3`, `GL3`, `ringAutSL3`, `innerAutSL3byGL3`, `invTransposeAutSL3`,
and the named matrices in the namespace `FieldAutomorphisms`.

Mathematical content: after the residue-field normalization, an automorphism of
`SL₃(R)` which is congruent to the identity on the six standard generators
`d₁,d₂,d₃,w₁,w₂,x₁₂(1)` is standard over the local ring.
-/

namespace LocalAutomorphisms

variable (R : Type*) [CommRing R] [IsLocalRing R] [Invertible (2 : R)]

/-- The maximal ideal of the local ring. -/
abbrev J : Ideal R :=
  IsLocalRing.maximalIdeal R

/-- Entrywise congruence of `3 × 3` matrices modulo the maximal ideal. -/
def MatrixCongruentModJ
    (A B : Matrix (Fin 3) (Fin 3) R) : Prop :=
  ∀ i j : Fin 3, A i j - B i j ∈ J R

/-- Congruence of elements of `SL₃(R)` modulo the maximal ideal. -/
def SLCongruentModJ (A B : SL3 R) : Prop :=
  MatrixCongruentModJ R
    (A : Matrix (Fin 3) (Fin 3) R)
    (B : Matrix (Fin 3) (Fin 3) R)

/-- Congruence of elements of `GL₃(R)` modulo the maximal ideal. -/
def GL3CongruentModJ (g h : GL3 R) : Prop :=
  MatrixCongruentModJ R
    (g : Matrix (Fin 3) (Fin 3) R)
    (h : Matrix (Fin 3) (Fin 3) R)

/-- A `GL₃(R)` element congruent to the identity modulo the maximal ideal. -/
def GL3IsOneModJ (g : GL3 R) : Prop :=
  GL3CongruentModJ R g 1

/-- An automorphism fixes a chosen `SL₃(R)` element modulo the maximal ideal. -/
def SL3FixedModJ (φ : AutSL3 R) (A : SL3 R) : Prop :=
  SLCongruentModJ R (φ A) A

/-- The three diagonal involutions are fixed modulo the maximal ideal. -/
def DiagonalFixedModJ (φ : AutSL3 R) : Prop :=
  SL3FixedModJ R φ (d1SL R) ∧
  SL3FixedModJ R φ (d2SL R) ∧
  SL3FixedModJ R φ (d3SL R)

/-- The two signed transposition matrices are fixed modulo the maximal ideal. -/
def SignedTranspositionsFixedModJ (φ : AutSL3 R) : Prop :=
  SL3FixedModJ R φ (w1SL R) ∧
  SL3FixedModJ R φ (w2SL R)

/-- The six normalized generators are fixed modulo the maximal ideal. -/
def BasicGeneratorsFixedModJ (φ : AutSL3 R) : Prop :=
  SL3FixedModJ R φ (d1SL R) ∧
  SL3FixedModJ R φ (d2SL R) ∧
  SL3FixedModJ R φ (d3SL R) ∧
  SL3FixedModJ R φ (w1SL R) ∧
  SL3FixedModJ R φ (w2SL R) ∧
  SL3FixedModJ R φ (x12SL R)

/-- Exact fixation of the six normalized generators. -/
def BasicGeneratorsFixed (φ : AutSL3 R) : Prop :=
  φ (d1SL R) = d1SL R ∧
  φ (d2SL R) = d2SL R ∧
  φ (d3SL R) = d3SL R ∧
  φ (w1SL R) = w1SL R ∧
  φ (w2SL R) = w2SL R ∧
  φ (x12SL R) = x12SL R

/-- The elementary transvection `xᵢⱼ(a)` as an element of `SL₃(R)`. -/
def xijSL (i j : Fin 3) (hij : i ≠ j) (a : R) : SL3 R :=
  ⟨Matrix.transvection i j a, by
    exact Matrix.det_transvection_of_ne i j hij a⟩

/--
Entrywise congruence modulo `J` is the same as equality after reduction to the
residue field.
-/
theorem sl_congruent_iff_reduction_eq {A B : SL3 R} :
    SLCongruentModJ R A B ↔
      (Matrix.SpecialLinearGroup.map (IsLocalRing.residue R)) A =
        (Matrix.SpecialLinearGroup.map (IsLocalRing.residue R)) B := by
  constructor
  · intro h
    ext i j
    exact (Ideal.Quotient.eq (I := J R) (x := A i j) (y := B i j)).2 (h i j)
  · intro h i j 
    have h' :
        (IsLocalRing.residue R) (A i j) = (IsLocalRing.residue R) (B i j) := by
      have h' := congrArg
          (fun X : SL3 (IsLocalRing.ResidueField R) =>
            (X : Matrix (Fin 3) (Fin 3) (IsLocalRing.ResidueField R)) i j) h
      simpa [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
        Matrix.map_apply] using h'
    exact (Ideal.Quotient.eq (I := J R) (x := A i j) (y := B i j)).1 h'

/-
Lemma 3 from Block 4: if the diagonal involutions are fixed modulo `J`, then a
change of basis congruent to the identity makes them fixed exactly.
-/
theorem diagonal_preserved_after_local_change_of_basis
    (φ : AutSL3 R) (hdiag : DiagonalFixedModJ R φ) :
    ∃ g₁ : GL3 R,
      GL3IsOneModJ R g₁ ∧
      innerAutSL3byGL3 g₁ (φ (d1SL R)) = d1SL R ∧
      innerAutSL3byGL3 g₁ (φ (d2SL R)) = d2SL R ∧
      innerAutSL3byGL3 g₁ (φ (d3SL R)) = d3SL R := by
  let τ1 : Matrix (Fin 3) (Fin 3) R := φ (d1SL R)
  let τ2 : Matrix (Fin 3) (Fin 3) R := φ (d2SL R)
  let τ3 : Matrix (Fin 3) (Fin 3) R := φ (d3SL R)
  let d1m : Matrix (Fin 3) (Fin 3) R := d1SL R
  let d2m : Matrix (Fin 3) (Fin 3) R := d2SL R
  let d3m : Matrix (Fin 3) (Fin 3) R := d3SL R
  let two_inv : R := ⅟2
  -- Construct the first transition matrix U directly
  let U : Matrix (Fin 3) (Fin 3) R := two_inv • (1 + τ1 * d1m)
  -- Prove τ1 is an involution (τ1 * τ1 = 1) because φ is a group homomorphism
  have ht1_sq : τ1 * τ1 = 1 := by
    have h_mul : τ1 * τ1 = ↑(φ (d1SL R) * φ (d1SL R)) := rfl
    rw [h_mul]
    rw [← map_mul]
    have hd1 : d1SL R * d1SL R = 1 := by
      apply Subtype.ext
      change d1 R * d1 R = 1
      dsimp [d1]
      rw [Matrix.diagonal_mul_diagonal]
      ext i j
      by_cases h : i = j
      · subst h
        simp only [Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
        fin_cases i <;> simp
      · simp [Matrix.diagonal_apply_ne _ h, Matrix.one_apply_ne h]
    rw [hd1]
    rw [map_one φ]
    rfl
  have hd1_sq : d1m * d1m = 1 := by
    dsimp [d1m]
    change d1 R * d1 R = 1
    dsimp[d1]
    rw[Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases h : i = j
    · subst h
      simp only [Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
      fin_cases i <;> simp
    · simp [Matrix.diagonal_apply_ne _ h, Matrix.one_apply_ne h]
  -- Prove U diagonalizes τ1
  have ht1U_eq_Ud1 : τ1 * U = U * d1m := by
    change τ1 * (two_inv • (1 + τ1 * d1m)) = (two_inv • (1 + τ1 * d1m)) * d1m
    rw [mul_smul_comm, smul_mul_assoc]
    congr 1
    rw [mul_add, add_mul]
    rw [mul_one, one_mul]
    rw [← mul_assoc τ1 τ1 d1m, mul_assoc τ1 d1m d1m]
    rw [ht1_sq, hd1_sq]
    rw [one_mul, mul_one]
    exact add_comm τ1 d1m
  -- Prove U is congruent to 1 mod J
  have hU_mod_J : MatrixCongruentModJ R U 1 := by
    -- MatrixCongruentModJ means ∀ i j, U i j - 1 i j ∈ J R
    intro i j
    -- We want to show U i j - 1 i j = two_inv * ∑ k, (τ1 i k - d1m i k) * d1m k j
    have h_eq : U i j - (1 : Matrix (Fin 3) (Fin 3) R) i j =
        two_inv * (∑ k : Fin 3, (τ1 i k - d1m i k) * d1m k j) := by
      have h_half (a b : R) : two_inv * (a + b) - a = two_inv * (b - a) := by
        have h_two : two_inv * (2 : R) = 1 := invOf_mul_self (2 : R)
        calc
          two_inv * (a + b) - a = two_inv * (a + b) - 1 * a := by rw [one_mul]
          _ = two_inv * (a + b) - (two_inv * 2) * a := by rw [h_two]
          _ = two_inv * (b - a) := by ring
      change two_inv * ((1 : Matrix (Fin 3) (Fin 3) R) i j + (τ1 * d1m) i j) -
        (1 : Matrix (Fin 3) (Fin 3) R) i j = _
      have h_step := h_half ((1 : Matrix (Fin 3) (Fin 3) R) i j) ((τ1 * d1m) i j)
      rw [h_step]
      have h1 : (1 : Matrix (Fin 3) (Fin 3) R) i j = (d1m * d1m) i j := by rw [← hd1_sq]
      rw [h1]
      simp only [Matrix.mul_apply]
      rw [← Finset.sum_sub_distrib]
      congr 1
      apply Finset.sum_congr rfl
      intro k _
      ring
    rw [h_eq]
    have h_sum : (∑ k : Fin 3, (τ1 i k - d1m i k) * d1m k j) ∈ J R := by
      apply (J R).sum_mem
      intro k _
      apply (J R).mul_mem_right (d1m k j)
      exact hdiag.1 i k
    exact (J R).mul_mem_left two_inv h_sum
  -- Because U ≡ 1 mod J, its determinant is ≡ 1 mod J, hence a unit.
  -- This allows you to lift U to GL3(R)
  have hU_isUnit : IsUnit (U.det) := by
    let π := IsLocalRing.residue R
    have h_map_U : U.map π = 1 := by
      ext i j
      simp only [Matrix.map_apply]
      have h_quot : π (U i j) = π ((1 : Matrix (Fin 3) (Fin 3) R) i j) :=
        (Ideal.Quotient.eq (I := J R) (x := U i j) (y := (1 : Matrix (Fin 3) (Fin 3) R) i j)).mpr
        (hU_mod_J i j)
      rw [h_quot]
      simp only [Matrix.one_apply]
      split_ifs
      · exact map_one π
      · exact map_zero π
    -- The determinant of U maps to the determinant of the identity matrix
    have h_det_map : π U.det = 1 := by
      calc
        π U.det = (U.map π).det := (RingHom.map_det π U).symm
        _ = (1 : Matrix (Fin 3) (Fin 3) _).det := by rw [h_map_U]
        _ = 1 := Matrix.det_one
    have h_unit_pi : IsUnit (π U.det) := by
      rw [h_det_map]
      exact isUnit_one
    -- Because π(U.det) is a unit in the residue field, U.det is a unit in R.
    exact isUnit_of_map_unit π U.det h_unit_pi
  let U_GL : GL3 R := Matrix.nonsingInvUnit U hU_isUnit
  -- repeat the process for τ2 in the new basis
  let U_val : Matrix (Fin 3) (Fin 3) R := ↑U_GL
  let U_inv : Matrix (Fin 3) (Fin 3) R := ↑(U_GL⁻¹)
  let τ2_prime : Matrix (Fin 3) (Fin 3) R := U_inv * τ2 * U_val
  -- Define V analogously to U
  let V : Matrix (Fin 3) (Fin 3) R := two_inv • (1 + τ2_prime * d2m)
  have ht2_sq : τ2 * τ2 = 1 := by
      have h_mul : τ2 * τ2 = ↑(φ (d2SL R) * φ (d2SL R)) := rfl
      rw [h_mul, ← map_mul]
      have hd2 : d2SL R * d2SL R = 1 := by
        apply Subtype.ext
        change d2 R * d2 R = 1
        dsimp [d2]
        rw [Matrix.diagonal_mul_diagonal]
        ext i j
        by_cases h : i = j
        · subst h
          simp only [Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
          fin_cases i <;> simp
        · simp [Matrix.diagonal_apply_ne _ h, Matrix.one_apply_ne h]
      rw [hd2, map_one]
      rfl
  have ht2_prime_sq : τ2_prime * τ2_prime = 1 := by
    dsimp [τ2_prime]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc U_val U_inv (τ2 * U_val)]
    have h_U_mul_inv : U_val * U_inv = 1 := by
      dsimp [U_val, U_inv]
      exact Units.mul_inv U_GL
    rw [h_U_mul_inv]
    rw [Matrix.one_mul]
    rw [← Matrix.mul_assoc τ2 τ2 U_val]
    rw [ht2_sq]
    rw [Matrix.one_mul]
    dsimp [U_inv, U_val]
    exact Units.inv_mul U_GL
  have hd2_sq : d2m * d2m = 1 := by
    -- same proof structure as hd1_sq
    dsimp [d2m]
    change d2 R * d2 R = 1
    dsimp[d2]
    rw[Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases h : i = j
    · subst h
      simp only [Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
      fin_cases i <;> simp
    · simp [Matrix.diagonal_apply_ne _ h, Matrix.one_apply_ne h]
  have ht2primeV_eq_Vd2 : τ2_prime * V = V * d2m := by
    change τ2_prime * (two_inv • (1 + τ2_prime * d2m)) = (two_inv • (1 + τ2_prime * d2m)) * d2m
    rw [mul_smul_comm, smul_mul_assoc]
    congr 1
    rw [mul_add, add_mul]
    rw [mul_one, one_mul]
    rw [← mul_assoc τ2_prime τ2_prime d2m, mul_assoc τ2_prime d2m d2m]
    rw [ht2_prime_sq, hd2_sq]
    rw [one_mul, mul_one]
    exact add_comm τ2_prime d2m
  have hd1_t2prime_comm : d1m * τ2_prime = τ2_prime * d1m := by
    have ht1_t2_comm : τ1 * τ2 = τ2 * τ1 := by
      have h_mul1 : τ1 * τ2 = ↑(φ (d1SL R) * φ (d2SL R)) := rfl
      have h_mul2 : τ2 * τ1 = ↑(φ (d2SL R) * φ (d1SL R)) := rfl
      rw [h_mul1, h_mul2, ← map_mul, ← map_mul]
      have hd1d2 : d1SL R * d2SL R =
                   d2SL R * d1SL R := by
        apply Subtype.ext
        change d1 R * d2 R = d2 R *
        d1 R
        dsimp [d1, d2]
        rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
        ext i j
        by_cases h : i = j
        · subst h; simp only [Matrix.diagonal_apply_eq]; ring
        · simp [Matrix.diagonal_apply_ne _ h]
      rw [hd1d2]
    have hU_d1 : U_val * d1m = τ1 * U_val := ht1U_eq_Ud1.symm
    have hd1_Uinv : d1m * U_inv = U_inv * τ1 := by
      have h_inv_mul : U_inv * U_val = 1 := by exact Units.inv_mul U_GL
      have h_mul_inv : U_val * U_inv = 1 := by exact Units.mul_inv U_GL
      have h1 : d1m * U_inv = 1 * (d1m * U_inv) := by rw [Matrix.one_mul]
      rw [h1]
      rw [← h_inv_mul]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc U_val d1m U_inv]
      rw [hU_d1]
      simp only [Matrix.mul_assoc]
      rw [h_mul_inv]
      rw [Matrix.mul_one]
    dsimp [τ2_prime]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc d1m U_inv (τ2 * U_val)]
    rw [hd1_Uinv]
    rw [Matrix.mul_assoc U_inv τ1 (τ2 * U_val)]
    rw [← Matrix.mul_assoc τ1 τ2 U_val]
    rw [ht1_t2_comm]
    rw [Matrix.mul_assoc τ2 τ1 U_val]
    rw [← hU_d1]
  have hd1_V_comm : d1m * V = V * d1m := by
    have hd1d2_comm : d1m * d2m = d2m * d1m := by
      dsimp [d1m, d2m]
      change d1 R * d2 R = d2 R *
      d1 R
      dsimp [d1, d2]
      rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
      ext i j
      by_cases h : i = j
      · subst h; simp only [Matrix.diagonal_apply_eq]; ring
      · simp [Matrix.diagonal_apply_ne _ h]
    change d1m * (two_inv • (1 + τ2_prime * d2m)) = (two_inv • (1 + τ2_prime * d2m)) * d1m
    rw [mul_smul_comm, smul_mul_assoc]
    congr 1
    rw [mul_add, add_mul]
    rw [mul_one, one_mul]
    rw [← Matrix.mul_assoc d1m τ2_prime d2m]
    rw [hd1_t2prime_comm]
    rw [Matrix.mul_assoc τ2_prime d1m d2m]
    rw [hd1d2_comm]
    rw [← Matrix.mul_assoc τ2_prime d2m d1m]
  have hV_mod_J : MatrixCongruentModJ R V 1 := by
    let π := IsLocalRing.residue R
    have h_map_U : U_val.map π = 1 := by
      ext i j
      simp only [Matrix.map_apply]
      have h_quot : π (U_val i j) = π ((1 : Matrix (Fin 3) (Fin 3) R) i j) :=
        (Ideal.Quotient.eq (I := J R) (x := U_val i j)
        (y := (1 : Matrix (Fin 3) (Fin 3) R) i j)).mpr (hU_mod_J i j)
      rw [h_quot]
      simp only [Matrix.one_apply]
      split_ifs
      · exact map_one π
      · exact map_zero π
    have h_map_one : (1 : Matrix (Fin 3) (Fin 3) R).map π = 1 := by
      ext i j
      simp only [Matrix.map_apply, Matrix.one_apply]
      split_ifs
      · exact map_one π
      · exact map_zero π 
    have h_map_U_inv : U_inv.map π = 1 := by
      have h_inv : U_inv * U_val = 1 := Units.inv_mul U_GL
      have h_map_inv : (U_inv * U_val).map π = (1 : Matrix (Fin 3) (Fin 3) R).map π := by rw [h_inv]
      rw [Matrix.map_mul] at h_map_inv
      rw [h_map_U] at h_map_inv
      rw [Matrix.mul_one] at h_map_inv
      rw [h_map_one] at h_map_inv
      exact h_map_inv
    have h_map_t2 : τ2.map π = d2m.map π := by
      ext i j
      simp only [Matrix.map_apply]
      exact (Ideal.Quotient.eq (I := J R) (x := τ2 i j) (y := d2m i j)).mpr (hdiag.2.1 i j)
    have h_map_t2_prime : τ2_prime.map π = d2m.map π := by
      dsimp [τ2_prime]
      rw [Matrix.map_mul, Matrix.map_mul]
      rw [h_map_U_inv, h_map_U, h_map_t2]
      rw [Matrix.one_mul, Matrix.mul_one]
    have ht2_prime_mod_J : MatrixCongruentModJ R τ2_prime d2m := by
      intro i j
      have h_eq := congr_fun (congr_fun h_map_t2_prime i) j
      simp only [Matrix.map_apply] at h_eq
      exact (Ideal.Quotient.eq (I := J R) (x := τ2_prime i j) (y := d2m i j)).mp h_eq
    intro i j
    have h_eq : V i j - (1 : Matrix (Fin 3) (Fin 3) R) i j =
        two_inv * (∑ k : Fin 3, (τ2_prime i k - d2m i k) * d2m k j) := by
      have h_half (a b : R) : two_inv * (a + b) - a = two_inv * (b - a) := by
        have h_two : two_inv * (2 : R) = 1 := invOf_mul_self (2 : R)
        calc
          two_inv * (a + b) - a = two_inv * (a + b) - 1 * a := by rw [one_mul]
          _ = two_inv * (a + b) - (two_inv * 2) * a := by rw [h_two]
          _ = two_inv * (b - a) := by ring
      change two_inv * ((1 : Matrix (Fin 3) (Fin 3) R) i j + (τ2_prime * d2m) i j) -
        (1 : Matrix (Fin 3) (Fin 3) R) i j = _
      have h_step := h_half ((1 : Matrix (Fin 3) (Fin 3) R) i j) ((τ2_prime * d2m) i j)
      rw [h_step]
      have h1 : (1 : Matrix (Fin 3) (Fin 3) R) i j = (d2m * d2m) i j := by rw [← hd2_sq]
      rw [h1]
      simp only [Matrix.mul_apply]
      rw [← Finset.sum_sub_distrib]
      congr 1
      apply Finset.sum_congr rfl
      intro k _
      ring
    rw [h_eq]
    have h_sum : (∑ k : Fin 3, (τ2_prime i k - d2m i k) * d2m k j) ∈ J R := by
      apply (J R).sum_mem
      intro k _
      apply (J R).mul_mem_right (d2m k j)
      exact ht2_prime_mod_J i k
    exact (J R).mul_mem_left two_inv h_sum
  have hV_isUnit : IsUnit (V.det) := by
    let π := IsLocalRing.residue R
    have h_map_V : V.map π = 1 := by
      ext i j
      simp only [Matrix.map_apply]
      have h_quot : π (V i j) = π ((1 : Matrix (Fin 3) (Fin 3) R) i j) :=
        (Ideal.Quotient.eq (I := J R) (x := V i j)
        (y := (1 : Matrix (Fin 3) (Fin 3) R) i j)).mpr (hV_mod_J i j)
      rw [h_quot]
      simp only [Matrix.one_apply]
      split_ifs
      · exact map_one π
      · exact map_zero π
    have h_det_map : π V.det = 1 := by
      calc
        π V.det = (V.map π).det := (RingHom.map_det π V).symm
        _ = (1 : Matrix (Fin 3) (Fin 3) _).det := by rw [h_map_V]
        _ = 1 := Matrix.det_one
    have h_unit_pi : IsUnit (π V.det) := by
      rw [h_det_map]
      exact isUnit_one
    exact isUnit_of_map_unit π V.det h_unit_pi
  let V_GL : GL3 R := Matrix.nonsingInvUnit V hV_isUnit
  -- final transition matrix P and witness g₁
  let P_GL : GL3 R := U_GL * V_GL
  let g1 : GL3 R := P_GL⁻¹
  have hg1_mod_J : GL3IsOneModJ R g1 := by
    intro i j
    let π := IsLocalRing.residue R
    have h_quot := Ideal.Quotient.eq (I := J R) (x := (↑g1 : Matrix (Fin 3) (Fin 3) R) i j)
      (y := (1 : Matrix (Fin 3) (Fin 3) R) i j)
    apply h_quot.mp
    have h_map_U : U_val.map π = 1 := by
      ext x y
      simp only [Matrix.map_apply]
      have hq : π (U_val x y) = π ((1 : Matrix (Fin 3) (Fin 3) R) x y) :=
        (Ideal.Quotient.eq (I := J R) (x := U_val x y)
        (y := (1 : Matrix (Fin 3) (Fin 3) R) x y)).mpr (hU_mod_J x y)
      rw [hq]
      simp only [Matrix.one_apply]
      split_ifs
      · exact map_one π
      · exact map_zero π
    have h_map_V : V.map π = 1 := by
      ext x y
      simp only [Matrix.map_apply]
      have hq : π (V x y) = π ((1 : Matrix (Fin 3) (Fin 3) R) x y) :=
        (Ideal.Quotient.eq (I := J R) (x := V x y) (y := (1 : Matrix (Fin 3) (Fin 3) R) x y)).mpr
        (hV_mod_J x y)
      rw [hq]
      simp only [Matrix.one_apply]
      split_ifs
      · exact map_one π
      · exact map_zero π
    have h_map_one : (1 : Matrix (Fin 3) (Fin 3) R).map π = 1 := by
      ext x y
      simp only [Matrix.map_apply, Matrix.one_apply]
      split_ifs
      · exact map_one π
      · exact map_zero π
    have h_P_val : (↑P_GL : Matrix (Fin 3) (Fin 3) R) = U_val * V := Units.val_mul U_GL V_GL
    have h_map_P : (↑P_GL : Matrix (Fin 3) (Fin 3) R).map π = 1 := by
      rw [h_P_val, Matrix.map_mul, h_map_U, h_map_V, Matrix.mul_one]
    have h_P_val : (↑P_GL : Matrix (Fin 3) (Fin 3) R) = U_val * V := rfl
    have h_map_P : (↑P_GL : Matrix (Fin 3) (Fin 3) R).map π = 1 := by
      rw [h_P_val, Matrix.map_mul, h_map_U, h_map_V, Matrix.mul_one]
    have h_g1_P : (↑g1 : Matrix (Fin 3) (Fin 3) R) * (↑P_GL : Matrix (Fin 3) (Fin 3) R) = 1 := by
      change (↑(P_GL⁻¹) : Matrix (Fin 3) (Fin 3) R) * (↑P_GL : Matrix (Fin 3) (Fin 3) R) = 1
      exact Units.inv_mul P_GL
    have h_map_g1_P : ((↑g1 : Matrix (Fin 3) (Fin 3) R) * (↑P_GL : Matrix (Fin 3) (Fin 3) R)).map π
    = (1 : Matrix (Fin 3) (Fin 3) R).map π := by
      rw [h_g1_P]
    rw [Matrix.map_mul, h_map_P, Matrix.mul_one, h_map_one] at h_map_g1_P
    have h_final := congr_fun (congr_fun h_map_g1_P i) j
    simp only [Matrix.map_apply, Matrix.one_apply] at h_final
    change π ((↑g1 : Matrix (Fin 3) (Fin 3) R) i j) = π ((1 : Matrix (Fin 3) (Fin 3) R) i j)
    rw [h_final]
    simp only [Matrix.one_apply]
    split_ifs
    · exact (map_one π).symm
    · exact (map_zero π).symm
  have hd1_goal : innerAutSL3byGL3 g1 (φ (d1SL R)) = d1SL R
  := by
    apply Subtype.ext
    change (↑g1 : Matrix (Fin 3) (Fin 3) R) * τ1 * (↑(g1⁻¹) : Matrix (Fin 3) (Fin 3) R) = d1m
    have hg1_val : (↑g1 : Matrix (Fin 3) (Fin 3) R) = ↑(P_GL⁻¹) := rfl
    have hg1_inv : (↑(g1⁻¹) : Matrix (Fin 3) (Fin 3) R) = ↑P_GL := rfl
    rw [hg1_val, hg1_inv]
    have hP_val : (↑P_GL : Matrix (Fin 3) (Fin 3) R) = U_val * V := rfl
    have hP_inv : (↑(P_GL⁻¹) : Matrix (Fin 3) (Fin 3) R) = (↑(V_GL⁻¹) : Matrix (Fin 3) (Fin 3) R) *
    U_inv
    := rfl
    rw [hP_val, hP_inv]
    simp only [Matrix.mul_assoc]
    have h_t1_Uval : τ1 * U_val = U_val * d1m := ht1U_eq_Ud1
    rw [← Matrix.mul_assoc τ1 U_val V]
    rw [h_t1_Uval]
    rw [Matrix.mul_assoc U_val d1m V]
    rw [← Matrix.mul_assoc U_inv U_val (d1m * V)]
    have h_inv_val : U_inv * U_val = 1 := Units.inv_mul U_GL
    rw [h_inv_val]
    rw [Matrix.one_mul]
    rw [hd1_V_comm]
    rw [← Matrix.mul_assoc (↑(V_GL⁻¹) : Matrix (Fin 3) (Fin 3) R) V d1m]
    have hV_inv_val : (↑(V_GL⁻¹) : Matrix (Fin 3) (Fin 3) R) * V = 1 := by
      have hV_eq : V = (↑V_GL : Matrix (Fin 3) (Fin 3) R) := rfl
      rw [hV_eq]
      exact Units.inv_mul V_GL
    rw [hV_inv_val]
    rw [Matrix.one_mul]
  have hd2_goal : innerAutSL3byGL3 g1 (φ (d2SL R)) = d2SL R
  := by
    apply Subtype.ext
    change (↑g1 : Matrix (Fin 3) (Fin 3) R) * τ2 * (↑(g1⁻¹) : Matrix (Fin 3) (Fin 3) R) = d2m
    have hg1_val : (↑g1 : Matrix (Fin 3) (Fin 3) R) = ↑(P_GL⁻¹) := rfl
    have hg1_inv : (↑(g1⁻¹) : Matrix (Fin 3) (Fin 3) R) = ↑P_GL := rfl
    rw [hg1_val, hg1_inv]
    have hP_val : (↑P_GL : Matrix (Fin 3) (Fin 3) R) = U_val * V := rfl
    have hP_inv : (↑(P_GL⁻¹) : Matrix (Fin 3) (Fin 3) R) = (↑(V_GL⁻¹) : Matrix (Fin 3) (Fin 3) R) *
     U_inv := rfl
    rw [hP_val, hP_inv]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc τ2 U_val V]
    rw [← Matrix.mul_assoc U_inv (τ2 * U_val) V]
    rw [← Matrix.mul_assoc U_inv τ2 U_val]
    have h_t2_prime_eq : (U_inv * τ2) * U_val = τ2_prime := rfl
    rw [h_t2_prime_eq]
    have h_t2prime_V : τ2_prime * V = V * d2m := ht2primeV_eq_Vd2
    rw [h_t2prime_V]
    rw [← Matrix.mul_assoc (↑(V_GL⁻¹) : Matrix (Fin 3) (Fin 3) R) V d2m]
    have hV_inv_val : (↑(V_GL⁻¹) : Matrix (Fin 3) (Fin 3) R) * V = 1 := by
      have hV_eq : V = (↑V_GL : Matrix (Fin 3) (Fin 3) R) := rfl
      rw [hV_eq]
      exact Units.inv_mul V_GL
    rw [hV_inv_val]
    rw [Matrix.one_mul]
  -- Final Witness & Goal Resolution
  use g1
  refine ⟨hg1_mod_J, hd1_goal, hd2_goal, ?_⟩
  · have hd3_split : d3SL R = d1SL R * d2SL R
     := by
      apply Subtype.ext
      change d3 R = d1 R * d2 R
      dsimp [d1, d2, d3]
      rw [Matrix.diagonal_mul_diagonal]
      ext i j
      by_cases h : i = j
      · subst h
        simp only [Matrix.diagonal_apply_eq]
        fin_cases i <;> simp
      · simp [Matrix.diagonal_apply_ne _ h]
    rw [hd3_split]
    rw [map_mul φ]
    rw [map_mul (innerAutSL3byGL3 g1)]
    rw [hd1_goal, hd2_goal]

/-
Lemma 4 from Block 4: once the diagonal involutions are fixed exactly and the
signed transpositions are fixed modulo `J`, a diagonal change of basis congruent
to the identity fixes the signed transpositions exactly.
-/
theorem signed_transpositions_preserved_after_local_change_of_basis
    (φ : AutSL3 R)
    (hdiag_exact :
      φ (d1SL R) = d1SL R ∧
      φ (d2SL R) = d2SL R ∧
      φ (d3SL R) = d3SL R)
    (hw_mod : SignedTranspositionsFixedModJ R φ) :
    ∃ g₂ : GL3 R,
      GL3IsOneModJ R g₂ ∧
      innerAutSL3byGL3 g₂ (φ (d1SL R)) = d1SL R ∧
      innerAutSL3byGL3 g₂ (φ (d2SL R)) = d2SL R ∧
      innerAutSL3byGL3 g₂ (φ (d3SL R)) = d3SL R ∧
      innerAutSL3byGL3 g₂ (φ (w1SL R)) = w1SL R ∧
      innerAutSL3byGL3 g₂ (φ (w2SL R)) = w2SL R := by
  let v1_mat : Matrix (Fin 3) (Fin 3) R := ↑(φ (w1SL R))
  let v2_mat : Matrix (Fin 3) (Fin 3) R := ↑(φ (w2SL R))
  let π := IsLocalRing.residue R
  -- Extract λ = v1_mat 0 1 and show it maps to 1 in the residue field.
  have h_map_lam : π (v1_mat 0 1) = 1 := by
    have hq : π (v1_mat 0 1) = π ((w1 R) 0 1) :=
      (Ideal.Quotient.eq (I := J R) (x := v1_mat 0 1) (y := (w1 R) 0 1)).mpr
      (hw_mod.1 0 1)
    have hw1_01 : (w1 R) 0 1 = 1 := rfl
    rw [hw1_01] at hq
    rw [hq, map_one]
  have h_lam_unit_pi : IsUnit (π (v1_mat 0 1)) := by
    rw [h_map_lam]
    exact isUnit_one
  have h_lam_unit : IsUnit (v1_mat 0 1) := isUnit_of_map_unit π (v1_mat 0 1) h_lam_unit_pi
  let lam_u : Rˣ := h_lam_unit.unit
  -- Extract μ = v2_mat 1 2 and show it maps to 1 in the residue field.
  have h_map_mu : π (v2_mat 1 2) = 1 := by
    have hq : π (v2_mat 1 2) = π ((w2 R) 1 2) :=
      (Ideal.Quotient.eq (I := J R) (x := v2_mat 1 2) (y := (w2 R) 1 2)).mpr 
      (hw_mod.2 1 2)
    have hw2_12 : (w2 R) 1 2 = 1 := rfl
    rw [hw2_12] at hq
    rw [hq, map_one]
  have h_mu_unit_pi : IsUnit (π (v2_mat 1 2)) := by
    rw [h_map_mu]
    exact isUnit_one
  have h_mu_unit : IsUnit (v2_mat 1 2) := isUnit_of_map_unit π (v2_mat 1 2) h_mu_unit_pi
  let mu_u : Rˣ := h_mu_unit.unit
  -- Define g2 = diag(λ⁻¹, 1, μ)
  let g2_mat : Matrix (Fin 3) (Fin 3) R := Matrix.diagonal ![↑(lam_u⁻¹), 1, ↑mu_u]
  have h_g2_det : g2_mat.det = ↑(lam_u⁻¹) * 1 * ↑mu_u := by
    dsimp [g2_mat]
    simp [Matrix.det_diagonal, Fin.prod_univ_three]
  have h_g2_isUnit : IsUnit g2_mat.det := by
    rw [h_g2_det]
    apply IsUnit.mul
    · apply IsUnit.mul
      · exact Units.isUnit lam_u⁻¹
      · exact isUnit_one
    · exact Units.isUnit mu_u
  let g2 : GL3 R := Matrix.nonsingInvUnit g2_mat h_g2_isUnit
  -- Prove g2 ≡ I (mod J)
  have hg2_mod_J : GL3IsOneModJ R g2 := by
    intro i j
    have h_quot := Ideal.Quotient.eq (I := J R) (x := (↑g2 : Matrix (Fin 3) (Fin 3) R) i j) (y := 
    (1 : Matrix (Fin 3) (Fin 3) R) i j)
    apply h_quot.mp
    have hg2_val : (↑g2 : Matrix (Fin 3) (Fin 3) R) = Matrix.diagonal ![↑(lam_u⁻¹), 1, ↑mu_u] := rfl
    rw [hg2_val]
    simp only [Matrix.one_apply]
    by_cases h : i = j
    · subst h
      simp only [Matrix.diagonal_apply_eq]
      fin_cases i
      · change π ↑(lam_u⁻¹) = 1
        have h_lam_pi : π (↑lam_u : R) = 1 := h_map_lam
        have h_lam_inv_pi : π (↑(lam_u⁻¹) : R) = 1 := by
          have h_mul : π (↑(lam_u⁻¹) : R) * π (↑lam_u : R) = 1 := by
            rw [← map_mul π, ← Units.val_mul]
            simp
          rw [h_lam_pi, mul_one] at h_mul
          exact h_mul
        exact h_lam_inv_pi
      · change π 1 = 1
        exact map_one π
      · change π (↑mu_u : R) = 1
        exact h_map_mu
    · simp [Matrix.diagonal_apply_ne _ h, map_zero]
      exact h
  -- Prove fixing of d1
  have hd1_goal : innerAutSL3byGL3 g2 (φ (d1SL R)) = d1SL R 
  := by
    apply Subtype.ext
    let d1m : Matrix (Fin 3) (Fin 3) R := ↑(d1SL R)
    let τ1 : Matrix (Fin 3) (Fin 3) R := ↑(φ (d1SL R))
    change (↑g2 : Matrix (Fin 3) (Fin 3) R) * τ1 * (↑(g2⁻¹) : Matrix (Fin 3) (Fin 3) R) = d1m
    have h_phi_d1 : τ1 = d1m := congrArg Subtype.val hdiag_exact.1
    rw [h_phi_d1]
    have h_comm : (↑g2 : Matrix (Fin 3) (Fin 3) R) * d1m = d1m * (↑g2 : Matrix (Fin 3) (Fin 3) R) 
    := by
      have hg2_val : (↑g2 : Matrix (Fin 3) (Fin 3) R) = Matrix.diagonal ![↑(lam_u⁻¹), 1, ↑mu_u] 
      := rfl
      have hd1_val : d1m = Matrix.diagonal ![1, -1, -1] := rfl
      rw [hg2_val, hd1_val]
      rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
      ext i j
      by_cases h : i = j
      · subst h; simp only [Matrix.diagonal_apply_eq]; ring
      · simp [Matrix.diagonal_apply_ne _ h]
    rw [h_comm, Matrix.mul_assoc, Units.mul_inv g2, Matrix.mul_one]
  -- Prove fixing of d2
  have hd2_goal : innerAutSL3byGL3 g2 (φ (d2SL R)) = d2SL R 
  := by
    apply Subtype.ext
    let d2m : Matrix (Fin 3) (Fin 3) R := ↑(d2SL R)
    let τ2 : Matrix (Fin 3) (Fin 3) R := ↑(φ (d2SL R))
    change (↑g2 : Matrix (Fin 3) (Fin 3) R) * τ2 * (↑(g2⁻¹) : Matrix (Fin 3) (Fin 3) R) = d2m
    have h_phi_d2 : τ2 = d2m := congrArg Subtype.val hdiag_exact.2.1
    rw [h_phi_d2]
    have h_comm : (↑g2 : Matrix (Fin 3) (Fin 3) R) * d2m = d2m * (↑g2 : Matrix (Fin 3) (Fin 3) R) 
    := by
      have hg2_val : (↑g2 : Matrix (Fin 3) (Fin 3) R) = Matrix.diagonal ![↑(lam_u⁻¹), 1, ↑mu_u] 
      := rfl
      have hd2_val : d2m = Matrix.diagonal ![-1, 1, -1] := rfl
      rw [hg2_val, hd2_val]
      rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
      ext i j
      by_cases h : i = j
      · subst h; simp only [Matrix.diagonal_apply_eq]; ring
      · simp [Matrix.diagonal_apply_ne _ h]
    rw [h_comm, Matrix.mul_assoc, Units.mul_inv g2, Matrix.mul_one]
  -- Prove fixing of d3
  have hd3_goal : innerAutSL3byGL3 g2 (φ (d3SL R)) = d3SL R 
  := by
    apply Subtype.ext
    let d3m : Matrix (Fin 3) (Fin 3) R := ↑(d3SL R)
    let τ3 : Matrix (Fin 3) (Fin 3) R := ↑(φ (d3SL R))
    change (↑g2 : Matrix (Fin 3) (Fin 3) R) * τ3 * (↑(g2⁻¹) : Matrix (Fin 3) (Fin 3) R) = d3m
    have h_phi_d3 : τ3 = d3m := congrArg Subtype.val hdiag_exact.2.2
    rw [h_phi_d3]
    have h_comm : (↑g2 : Matrix (Fin 3) (Fin 3) R) * d3m = d3m * (↑g2 : Matrix (Fin 3) (Fin 3) R) 
    := by
      have hg2_val : (↑g2 : Matrix (Fin 3) (Fin 3) R) = Matrix.diagonal ![↑(lam_u⁻¹), 1, ↑mu_u] 
      := rfl
      have hd3_val : d3m = Matrix.diagonal ![-1, -1, 1] := rfl
      rw [hg2_val, hd3_val]
      rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
      ext i j
      by_cases h : i = j
      · subst h; simp only [Matrix.diagonal_apply_eq]; ring
      · simp [Matrix.diagonal_apply_ne _ h]
    rw [h_comm, Matrix.mul_assoc, Units.mul_inv g2, Matrix.mul_one]
  -- Prove fixing of w1
  have hw1_goal : innerAutSL3byGL3 g2 (φ (w1SL R)) = w1SL R 
  := by
    apply Subtype.ext
    let w1m : Matrix (Fin 3) (Fin 3) R := ↑(w1SL R)
    change (↑g2 : Matrix (Fin 3) (Fin 3) R) * v1_mat * (↑(g2⁻¹) : Matrix (Fin 3) (Fin 3) R) = w1m
    have h_mul_inv : (↑g2 : Matrix (Fin 3) (Fin 3) R) * v1_mat *
    (↑(g2⁻¹) : Matrix (Fin 3) (Fin 3) R) =
    w1m ↔ (↑g2 : Matrix (Fin 3) (Fin 3) R) * v1_mat = w1m * (↑g2 : Matrix (Fin 3) (Fin 3) R) := by
      constructor
      · intro h
        calc (↑g2 : Matrix (Fin 3) (Fin 3) R) * v1_mat = (↑g2 : Matrix (Fin 3) (Fin 3) R) * v1_mat *
         (↑(g2⁻¹) : Matrix (Fin 3) (Fin 3) R) * (↑g2 : Matrix (Fin 3) (Fin 3) R) 
         := by rw [Matrix.mul_assoc, Units.inv_mul g2, Matrix.mul_one]
             _ = w1m * (↑g2 : Matrix (Fin 3) (Fin 3) R) := by rw [h]
      · intro h
        calc (↑g2 : Matrix (Fin 3) (Fin 3) R) * v1_mat * (↑(g2⁻¹) : Matrix (Fin 3) (Fin 3) R) =
        w1m * (↑g2 : Matrix (Fin 3) (Fin 3) R) * (↑(g2⁻¹) : Matrix (Fin 3) (Fin 3) R) := by rw [h]
             _ = w1m := by rw [Matrix.mul_assoc, Units.mul_inv g2, Matrix.mul_one]
    apply h_mul_inv.mpr
    have h_zero_of_eq_neg (x : R) (h : x = -x) : x = 0 := by
      have h_two : ⅟(2 : R) * 2 = 1 := invOf_mul_self (2 : R)
      have h2 : x * 2 = 0 := by
        calc x * 2 = x - (-x) := by ring
             _ = x - x := by rw [← h]
             _ = 0 := by ring
      calc x = x * 1 := by ring
           _ = x * (⅟(2 : R) * 2) := by rw [← h_two]
           _ = (x * 2) * ⅟(2 : R) := by ring
           _ = 0 * ⅟(2 : R) := by rw [h2]
           _ = 0 := by ring
    let d1m : Matrix (Fin 3) (Fin 3) R := ↑(d1SL R)
    let d2m : Matrix (Fin 3) (Fin 3) R := ↑(d2SL R)
    let d3m : Matrix (Fin 3) (Fin 3) R := ↑(d3SL R)
    have eq_d3 : v1_mat * d3m = d3m * v1_mat := by
      have h_sl3 : w1SL R * d3SL R =
      d3SL R * w1SL R := by
        apply Subtype.ext
        change w1 R * d3 R =
        d3 R * w1 R
        ext i j
        dsimp [w1, d3]
        rw [Matrix.mul_apply, Matrix.mul_apply]
        rw [Fin.sum_univ_three, Fin.sum_univ_three]
        fin_cases i <;> fin_cases j <;> (simp)
      have h_phi_eq := congrArg φ h_sl3
      rw [map_mul, map_mul] at h_phi_eq
      have h_mat_eq : v1_mat * (↑(φ (d3SL R)) : Matrix (Fin 3) (Fin 3) R) =
      (↑(φ (d3SL R)) : Matrix (Fin 3) (Fin 3) R) * v1_mat :=
        congrArg (fun x : SL3 R => (↑x : Matrix (Fin 3) (Fin 3) R)) h_phi_eq
      have h_phi_d3 : ↑(φ (d3SL R)) = d3m := congrArg Subtype.val hdiag_exact.2.2
      rw [h_phi_d3] at h_mat_eq
      exact h_mat_eq
    have eq_d1 : v1_mat * d1m = d2m * v1_mat := by
      have h_sl3 : w1SL R * d1SL R =
      d2SL R * w1SL R := by
        apply Subtype.ext
        change w1 R * d1 R =
        d2 R * w1 R
        ext i j
        dsimp [w1, d1, d2]
        rw [Matrix.mul_apply, Matrix.mul_apply]
        rw [Fin.sum_univ_three, Fin.sum_univ_three]
        fin_cases i <;> fin_cases j <;> (simp)
      have h_phi_eq := congrArg φ h_sl3
      rw [map_mul, map_mul] at h_phi_eq
      have h_mat_eq : v1_mat * (↑(φ (d1SL R)) : Matrix (Fin 3) (Fin 3) R) =
      (↑(φ (d2SL R)) : Matrix (Fin 3) (Fin 3) R) * v1_mat :=
        congrArg (fun x : SL3 R => (↑x : Matrix (Fin 3) (Fin 3) R)) h_phi_eq
      have h_phi_d1 : ↑(φ (d1SL R)) = d1m := congrArg Subtype.val hdiag_exact.1
      have h_phi_d2 : ↑(φ (d2SL R)) = d2m := congrArg Subtype.val hdiag_exact.2.1
      rw [h_phi_d1, h_phi_d2] at h_mat_eq
      exact h_mat_eq
    have eq_sq : v1_mat * v1_mat = d3m := by
      have h_sl3 : w1SL R * w1SL R =
      d3SL R := by
        apply Subtype.ext
        change w1 R * w1 R = d3 R
        ext i j
        dsimp [w1, d3]
        rw [Matrix.mul_apply]
        rw [Fin.sum_univ_three]
        fin_cases i <;> fin_cases j <;> (simp)
      have h_phi_eq := congrArg φ h_sl3
      rw [map_mul] at h_phi_eq
      have h_mat_eq : v1_mat * v1_mat =
      (↑(φ (d3SL R)) : Matrix (Fin 3) (Fin 3) R) :=
        congrArg (fun x : SL3 R => (↑x : Matrix (Fin 3) (Fin 3) R)) h_phi_eq
      have h_phi_d3 : ↑(φ (d3SL R)) = d3m := congrArg Subtype.val hdiag_exact.2.2
      rw [h_phi_d3] at h_mat_eq
      exact h_mat_eq
    have hd3_val : d3m = Matrix.diagonal ![-1, -1, 1] := rfl
    have hd1_val : d1m = Matrix.diagonal ![1, -1, -1] := rfl
    have hd2_val : d2m = Matrix.diagonal ![-1, 1, -1] := rfl
    have hv20 : v1_mat 2 0 = 0 := by
      have h := congr_fun (congr_fun eq_d3 2) 0
      rw [Matrix.mul_apply, Fin.sum_univ_three, Matrix.mul_apply, Fin.sum_univ_three] at h
      have h00 : d3m 0 0 = -1 := rfl
      have h10 : d3m 1 0 = 0 := rfl
      have h20 : d3m 2 0 = 0 := rfl
      have h21 : d3m 2 1 = 0 := rfl
      have h22 : d3m 2 2 = 1 := rfl
      rw [h00, h10, h20, h21, h22] at h
      have eq' : v1_mat 2 0 = - (v1_mat 2 0) := by
        calc v1_mat 2 0 = 0 * v1_mat 0 0 + 0 * v1_mat 1 0 + 1 * v1_mat 2 0 := by ring
             _ = v1_mat 2 0 * -1 + v1_mat 2 1 * 0 + v1_mat 2 2 * 0 := h.symm
             _ = - (v1_mat 2 0) := by ring
      exact h_zero_of_eq_neg _ eq'
    have hv21 : v1_mat 2 1 = 0 := by
      have h := congr_fun (congr_fun eq_d3 2) 1
      rw [Matrix.mul_apply, Fin.sum_univ_three, Matrix.mul_apply, Fin.sum_univ_three] at h
      have h01 : d3m 0 1 = 0 := rfl
      have h11 : d3m 1 1 = -1 := rfl
      have h21 : d3m 2 1 = 0 := rfl
      have h20 : d3m 2 0 = 0 := rfl
      have h22 : d3m 2 2 = 1 := rfl
      rw [h01, h11, h21, h20, h22] at h
      have eq' : v1_mat 2 1 = - (v1_mat 2 1) := by
        calc v1_mat 2 1 = 0 * v1_mat 0 1 + 0 * v1_mat 1 1 + 1 * v1_mat 2 1 := by ring
             _ = v1_mat 2 0 * 0 + v1_mat 2 1 * -1 + v1_mat 2 2 * 0 := h.symm
             _ = - (v1_mat 2 1) := by ring
      exact h_zero_of_eq_neg _ eq'
    have hv02 : v1_mat 0 2 = 0 := by
      have h := congr_fun (congr_fun eq_d3 0) 2
      rw [Matrix.mul_apply, Fin.sum_univ_three, Matrix.mul_apply, Fin.sum_univ_three] at h
      have h02 : d3m 0 2 = 0 := rfl
      have h12 : d3m 1 2 = 0 := rfl
      have h22 : d3m 2 2 = 1 := rfl
      have h00 : d3m 0 0 = -1 := rfl
      have h01 : d3m 0 1 = 0 := rfl
      rw [h02, h12, h22, h00, h01] at h
      have eq' : v1_mat 0 2 = - (v1_mat 0 2) := by
        calc v1_mat 0 2 = v1_mat 0 2 * 1 := by ring
             _ = v1_mat 0 0 * 0 + v1_mat 0 1 * 0 + v1_mat 0 2 * 1 := by ring
             _ = -1 * v1_mat 0 2 + 0 * v1_mat 1 2 + 0 * v1_mat 2 2 := h
             _ = - (v1_mat 0 2) := by ring
      exact h_zero_of_eq_neg _ eq'
    have hv12 : v1_mat 1 2 = 0 := by
      have h := congr_fun (congr_fun eq_d3 1) 2
      rw [Matrix.mul_apply, Fin.sum_univ_three, Matrix.mul_apply, Fin.sum_univ_three] at h
      have h02 : d3m 0 2 = 0 := rfl
      have h12 : d3m 1 2 = 0 := rfl
      have h22 : d3m 2 2 = 1 := rfl
      have h10 : d3m 1 0 = 0 := rfl
      have h11 : d3m 1 1 = -1 := rfl
      rw [h02, h12, h22, h10, h11] at h
      have eq' : v1_mat 1 2 = - (v1_mat 1 2) := by
        calc v1_mat 1 2 = v1_mat 1 0 * 0 + v1_mat 1 1 * 0 + v1_mat 1 2 * 1 := by ring
             _ = 0 * v1_mat 0 2 + -1 * v1_mat 1 2 + 0 * v1_mat 2 2 := h
             _ = - (v1_mat 1 2) := by ring
      exact h_zero_of_eq_neg _ eq'
    have hv00 : v1_mat 0 0 = 0 := by
      have h := congr_fun (congr_fun eq_d1 0) 0
      rw [Matrix.mul_apply, Fin.sum_univ_three, Matrix.mul_apply, Fin.sum_univ_three] at h
      have hd1_00 : d1m 0 0 = 1 := rfl
      have hd1_10 : d1m 1 0 = 0 := rfl
      have hd1_20 : d1m 2 0 = 0 := rfl
      have hd2_00 : d2m 0 0 = -1 := rfl
      have hd2_01 : d2m 0 1 = 0 := rfl
      have hd2_02 : d2m 0 2 = 0 := rfl
      rw [hd1_00, hd1_10, hd1_20, hd2_00, hd2_01, hd2_02] at h
      have eq' : v1_mat 0 0 = - (v1_mat 0 0) := by
        calc v1_mat 0 0 = v1_mat 0 0 * 1 + v1_mat 0 1 * 0 + v1_mat 0 2 * 0 := by ring
             _ = -1 * v1_mat 0 0 + 0 * v1_mat 1 0 + 0 * v1_mat 2 0 := h
             _ = - (v1_mat 0 0) := by ring
      exact h_zero_of_eq_neg _ eq'
    have hv11 : v1_mat 1 1 = 0 := by
      have h := congr_fun (congr_fun eq_d1 1) 1
      rw [Matrix.mul_apply, Fin.sum_univ_three, Matrix.mul_apply, Fin.sum_univ_three] at h
      have hd1_01 : d1m 0 1 = 0 := rfl
      have hd1_11 : d1m 1 1 = -1 := rfl
      have hd1_21 : d1m 2 1 = 0 := rfl
      have hd2_10 : d2m 1 0 = 0 := rfl
      have hd2_11 : d2m 1 1 = 1 := rfl
      have hd2_12 : d2m 1 2 = 0 := rfl
      rw [hd1_01, hd1_11, hd1_21, hd2_10, hd2_11, hd2_12] at h
      have eq' : v1_mat 1 1 = - (v1_mat 1 1) := by
        calc v1_mat 1 1 = 0 * v1_mat 0 1 + 1 * v1_mat 1 1 + 0 * v1_mat 2 1 := by ring
             _ = v1_mat 1 0 * 0 + v1_mat 1 1 * -1 + v1_mat 1 2 * 0 := h.symm
             _ = - (v1_mat 1 1) := by ring
      exact h_zero_of_eq_neg _ eq'
    have hv01_v10 : v1_mat 0 1 * v1_mat 1 0 = -1 := by
      have h := congr_fun (congr_fun eq_sq 0) 0
      rw [Matrix.mul_apply, Fin.sum_univ_three] at h
      have hd3_00 : d3m 0 0 = -1 := rfl
      rw [hd3_00, hv00, hv02] at h
      calc v1_mat 0 1 * v1_mat 1 0 = 0 * 0 + v1_mat 0 1 * v1_mat 1 0 + 0 * v1_mat 2 0 := by ring
           _ = -1 := h
    have h_det : v1_mat.det = 1 := (φ (w1SL R)).property
    have h_det_exp : v1_mat.det = - (v1_mat 0 1 * v1_mat 1 0 * v1_mat 2 2) := by
      rw [Matrix.det_fin_three]
      rw [hv00, hv11, hv20, hv21, hv02, hv12]
      ring
    have hv22 : v1_mat 2 2 = 1 := by
      calc v1_mat 2 2 = - (-1 * v1_mat 2 2) := by ring
           _ = - (v1_mat 0 1 * v1_mat 1 0 * v1_mat 2 2) := by rw [hv01_v10]
           _ = v1_mat.det := h_det_exp.symm
           _ = 1 := h_det
    have hv01 : v1_mat 0 1 = ↑lam_u := rfl
    have hv10 : v1_mat 1 0 = - ↑(lam_u⁻¹) := by
      have h_inv : (↑lam_u : R) * (- v1_mat 1 0) = 1 := by
        calc (↑lam_u : R) * (- v1_mat 1 0) = v1_mat 0 1 * (- v1_mat 1 0) := by rw [hv01]
             _ = - (v1_mat 0 1 * v1_mat 1 0) := by ring
             _ = - (-1) := by rw [hv01_v10]
             _ = 1 := by ring
      have h_lam_inv : (↑(lam_u⁻¹) : R) * ↑lam_u = 1 := by
        rw [← Units.val_mul]
        simp
      calc v1_mat 1 0 = - (1 * (- v1_mat 1 0)) := by ring
           _ = - ((↑(lam_u⁻¹) * ↑lam_u) * (- v1_mat 1 0)) := by rw [h_lam_inv]
           _ = - (↑(lam_u⁻¹) * ((↑lam_u : R) * (- v1_mat 1 0))) := by ring
           _ = - (↑(lam_u⁻¹) * 1) := by rw [h_inv]
           _ = - ↑(lam_u⁻¹) := by ring
    ext i j
    have hg2_val : (↑g2 : Matrix (Fin 3) (Fin 3) R) = Matrix.diagonal ![↑(lam_u⁻¹), 1, ↑mu_u] := rfl
    rw [hg2_val]
    rw [Matrix.mul_apply, Matrix.mul_apply]
    rw [Fin.sum_univ_three, Fin.sum_univ_three]
    have h_inv : (↑(lam_u⁻¹) : R) * ↑lam_u = 1 := by
      rw [← Units.val_mul]
      simp
    fin_cases i <;> fin_cases j
    · change (↑(lam_u⁻¹) : R) * v1_mat 0 0 + 0 * v1_mat 1 0 + 0 * v1_mat 2 0 =
      (0 : R) * ↑(lam_u⁻¹) + (1 : R) * 0 + 0 * 0
      rw [hv00]; ring
    · change (↑(lam_u⁻¹) : R) * v1_mat 0 1 + 0 * v1_mat 1 1 + 0 * v1_mat 2 1 =
      (0 : R) * 0 + (1 : R) * 1 + 0 * 0
      rw [hv01]
      calc (↑(lam_u⁻¹) : R) * ↑lam_u + 0 * v1_mat 1 1 + 0 * v1_mat 2 1
        _ = (↑(lam_u⁻¹) : R) * ↑lam_u := by ring
        _ = 1 := h_inv
        _ = (0 : R) * 0 + (1 : R) * 1 + 0 * 0 := by ring
    · change (↑(lam_u⁻¹) : R) * v1_mat 0 2 + 0 * v1_mat 1 2 + 0 * v1_mat 2 2 =
      (0 : R) * 0 + (1 : R) * 0 + 0 * ↑mu_u
      rw [hv02]; ring
    · change (0 : R) * v1_mat 0 0 + 1 * v1_mat 1 0 + 0 * v1_mat 2 0 =
      (-1 : R) * ↑(lam_u⁻¹) + 0 * 0 + 0 * 0
      rw [hv10]; ring
    · change (0 : R) * v1_mat 0 1 + 1 * v1_mat 1 1 + 0 * v1_mat 2 1 =
      (-1 : R) * 0 + 0 * 1 + 0 * 0
      rw [hv11]; ring
    · change (0 : R) * v1_mat 0 2 + 1 * v1_mat 1 2 + 0 * v1_mat 2 2 =
      (-1 : R) * 0 + 0 * 0 + 0 * ↑mu_u
      rw [hv12]; ring
    · change (0 : R) * v1_mat 0 0 + 0 * v1_mat 1 0 + ↑mu_u * v1_mat 2 0 =
      (0 : R) * ↑(lam_u⁻¹) + 0 * 0 + 1 * 0
      rw [hv20]; ring
    · change (0 : R) * v1_mat 0 1 + 0 * v1_mat 1 1 + ↑mu_u * v1_mat 2 1 =
      (0 : R) * 0 + 0 * 1 + 1 * 0
      rw [hv21]; ring
    · change (0 : R) * v1_mat 0 2 + 0 * v1_mat 1 2 + ↑mu_u * v1_mat 2 2 =
      (0 : R) * 0 + 0 * 0 + 1 * ↑mu_u
      rw [hv22]; ring
  -- Prove fixing of w2
  have hw2_goal : innerAutSL3byGL3 g2 (φ (w2SL R)) =
  w2SL R := by
    apply Subtype.ext
    let w2m : Matrix (Fin 3) (Fin 3) R := ↑(w2SL R)
    change (↑g2 : Matrix (Fin 3) (Fin 3) R) * v2_mat * (↑(g2⁻¹) : Matrix (Fin 3) (Fin 3) R) = w2m
    have h_mul_inv : (↑g2 : Matrix (Fin 3) (Fin 3) R) * v2_mat *
    (↑(g2⁻¹) : Matrix (Fin 3) (Fin 3) R) = w2m ↔ (↑g2 : Matrix (Fin 3) (Fin 3) R) * v2_mat =
    w2m * (↑g2 : Matrix (Fin 3) (Fin 3) R) := by
      constructor
      · intro h
        calc (↑g2 : Matrix (Fin 3) (Fin 3) R) * v2_mat = (↑g2 : Matrix (Fin 3) (Fin 3) R) * v2_mat *
        (↑(g2⁻¹) : Matrix (Fin 3) (Fin 3) R) * (↑g2 : Matrix (Fin 3) (Fin 3) R)
        := by rw [Matrix.mul_assoc, Units.inv_mul g2, Matrix.mul_one]
             _ = w2m * (↑g2 : Matrix (Fin 3) (Fin 3) R) := by rw [h]
      · intro h
        calc (↑g2 : Matrix (Fin 3) (Fin 3) R) * v2_mat * (↑(g2⁻¹) : Matrix (Fin 3) (Fin 3) R) =
        w2m * (↑g2 : Matrix (Fin 3) (Fin 3) R) * (↑(g2⁻¹) : Matrix (Fin 3) (Fin 3) R) := by rw [h]
             _ = w2m := by rw [Matrix.mul_assoc, Units.mul_inv g2, Matrix.mul_one]
    apply h_mul_inv.mpr
    have h_zero_of_eq_neg (x : R) (h : x = -x) : x = 0 := by
      have h_two : ⅟(2 : R) * 2 = 1 := invOf_mul_self (2 : R)
      have h2 : x * 2 = 0 := by
        calc x * 2 = x - (-x) := by ring
             _ = x - x := by rw [← h]
             _ = 0 := by ring
      calc x = x * 1 := by ring
           _ = x * (⅟(2 : R) * 2) := by rw [← h_two]
           _ = (x * 2) * ⅟(2 : R) := by ring
           _ = 0 * ⅟(2 : R) := by rw [h2]
           _ = 0 := by ring
    let d1m : Matrix (Fin 3) (Fin 3) R := ↑(d1SL R)
    let d2m : Matrix (Fin 3) (Fin 3) R := ↑(d2SL R)
    let d3m : Matrix (Fin 3) (Fin 3) R := ↑(d3SL R)
    have eq_d1_v2 : v2_mat * d1m = d1m * v2_mat := by
      have h_sl3 : w2SL R * d1SL R =
      d1SL R * w2SL R := by
        apply Subtype.ext
        change w2 R * d1 R =
        d1 R * w2 R
        ext i j
        dsimp [w2, d1]
        rw [Matrix.mul_apply, Matrix.mul_apply]
        rw [Fin.sum_univ_three, Fin.sum_univ_three]
        fin_cases i <;> fin_cases j <;> (simp)
      have h_phi_eq := congrArg φ h_sl3
      rw [map_mul, map_mul] at h_phi_eq
      have h_mat_eq : v2_mat * (↑(φ (d1SL R)) : Matrix (Fin 3) (Fin 3) R) =
      (↑(φ (d1SL R)) : Matrix (Fin 3) (Fin 3) R) * v2_mat :=
        congrArg (fun x : SL3 R => (↑x : Matrix (Fin 3) (Fin 3) R)) h_phi_eq
      have h_phi_d1 : ↑(φ (d1SL R)) = d1m := congrArg Subtype.val hdiag_exact.1
      rw [h_phi_d1] at h_mat_eq
      exact h_mat_eq
    have eq_d2_v2 : v2_mat * d2m = d3m * v2_mat := by
      have h_sl3 : w2SL R * d2SL R =
      d3SL R * w2SL R := by
        apply Subtype.ext
        change w2 R * d2 R =
        d3 R * w2 R
        ext i j
        dsimp [w2, d2, d3]
        rw [Matrix.mul_apply, Matrix.mul_apply]
        rw [Fin.sum_univ_three, Fin.sum_univ_three]
        fin_cases i <;> fin_cases j <;> (simp)
      have h_phi_eq := congrArg φ h_sl3
      rw [map_mul, map_mul] at h_phi_eq
      have h_mat_eq : v2_mat * (↑(φ (d2SL R)) : Matrix (Fin 3) (Fin 3) R) =
      (↑(φ (d3SL R)) : Matrix (Fin 3) (Fin 3) R) * v2_mat :=
        congrArg (fun x : SL3 R => (↑x : Matrix (Fin 3) (Fin 3) R)) h_phi_eq
      have h_phi_d2 : ↑(φ (d2SL R)) = d2m := congrArg Subtype.val hdiag_exact.2.1
      have h_phi_d3 : ↑(φ (d3SL R)) = d3m := congrArg Subtype.val hdiag_exact.2.2
      rw [h_phi_d2, h_phi_d3] at h_mat_eq
      exact h_mat_eq
    have eq_sq_v2 : v2_mat * v2_mat = d1m := by
      have h_sl3 : w2SL R * w2SL R =
      d1SL R := by
        apply Subtype.ext
        change w2 R * w2 R = d1 R
        ext i j
        dsimp [w2, d1]
        rw [Matrix.mul_apply]
        rw [Fin.sum_univ_three]
        fin_cases i <;> fin_cases j <;> (simp)
      have h_phi_eq := congrArg φ h_sl3
      rw [map_mul] at h_phi_eq
      have h_mat_eq : v2_mat * v2_mat =
      (↑(φ (d1SL R)) : Matrix (Fin 3) (Fin 3) R) :=
        congrArg (fun x : SL3 R => (↑x : Matrix (Fin 3) (Fin 3) R)) h_phi_eq
      have h_phi_d1 : ↑(φ (d1SL R)) = d1m := congrArg Subtype.val hdiag_exact.1
      rw [h_phi_d1] at h_mat_eq
      exact h_mat_eq
    have hd1_val : d1m = Matrix.diagonal ![1, -1, -1] := rfl
    have hd2_val : d2m = Matrix.diagonal ![-1, 1, -1] := rfl
    have hd3_val : d3m = Matrix.diagonal ![-1, -1, 1] := rfl
    have hv01 : v2_mat 0 1 = 0 := by
      have h := congr_fun (congr_fun eq_d1_v2 0) 1
      rw [Matrix.mul_apply, Fin.sum_univ_three, Matrix.mul_apply, Fin.sum_univ_three] at h
      have h01_1 : d1m 0 1 = 0 := rfl
      have h11_1 : d1m 1 1 = -1 := rfl
      have h21_1 : d1m 2 1 = 0 := rfl
      have h00_1 : d1m 0 0 = 1 := rfl
      have h02_1 : d1m 0 2 = 0 := rfl
      rw [h01_1, h11_1, h21_1, h00_1, h02_1] at h
      have eq' : v2_mat 0 1 = - (v2_mat 0 1) := by
        calc v2_mat 0 1 = 1 * v2_mat 0 1 + 0 * v2_mat 1 1 + 0 * v2_mat 2 1 := by ring
             _ = v2_mat 0 0 * 0 + v2_mat 0 1 * -1 + v2_mat 0 2 * 0 := h.symm
             _ = - (v2_mat 0 1) := by ring
      exact h_zero_of_eq_neg _ eq'
    have hv02 : v2_mat 0 2 = 0 := by
      have h := congr_fun (congr_fun eq_d1_v2 0) 2
      rw [Matrix.mul_apply, Fin.sum_univ_three, Matrix.mul_apply, Fin.sum_univ_three] at h
      have h02_1 : d1m 0 2 = 0 := rfl
      have h12_1 : d1m 1 2 = 0 := rfl
      have h22_1 : d1m 2 2 = -1 := rfl
      have h00_1 : d1m 0 0 = 1 := rfl
      have h01_1 : d1m 0 1 = 0 := rfl
      rw [h02_1, h12_1, h22_1, h00_1, h01_1] at h
      have eq' : v2_mat 0 2 = - (v2_mat 0 2) := by
        calc v2_mat 0 2 = 1 * v2_mat 0 2 + 0 * v2_mat 1 2 + 0 * v2_mat 2 2 := by ring
             _ = v2_mat 0 0 * 0 + v2_mat 0 1 * 0 + v2_mat 0 2 * -1 := h.symm
             _ = - (v2_mat 0 2) := by ring
      exact h_zero_of_eq_neg _ eq'
    have hv10 : v2_mat 1 0 = 0 := by
      have h := congr_fun (congr_fun eq_d1_v2 1) 0
      rw [Matrix.mul_apply, Fin.sum_univ_three, Matrix.mul_apply, Fin.sum_univ_three] at h
      have h00_1 : d1m 0 0 = 1 := rfl
      have h10_1 : d1m 1 0 = 0 := rfl
      have h20_1 : d1m 2 0 = 0 := rfl
      have h11_1 : d1m 1 1 = -1 := rfl
      have h12_1 : d1m 1 2 = 0 := rfl
      rw [h00_1, h10_1, h20_1, h11_1, h12_1] at h
      have eq' : v2_mat 1 0 = - (v2_mat 1 0) := by
        calc v2_mat 1 0 = v2_mat 1 0 * 1 + v2_mat 1 1 * 0 + v2_mat 1 2 * 0 := by ring
             _ = 0 * v2_mat 0 0 + -1 * v2_mat 1 0 + 0 * v2_mat 2 0 := h
             _ = - (v2_mat 1 0) := by ring
      exact h_zero_of_eq_neg _ eq'
    have hv20 : v2_mat 2 0 = 0 := by
      have h := congr_fun (congr_fun eq_d1_v2 2) 0
      rw [Matrix.mul_apply, Fin.sum_univ_three, Matrix.mul_apply, Fin.sum_univ_three] at h
      have h00_1 : d1m 0 0 = 1 := rfl
      have h10_1 : d1m 1 0 = 0 := rfl
      have h20_1 : d1m 2 0 = 0 := rfl
      have h21_1 : d1m 2 1 = 0 := rfl
      have h22_1 : d1m 2 2 = -1 := rfl
      rw [h00_1, h10_1, h20_1, h21_1, h22_1] at h
      have eq' : v2_mat 2 0 = - (v2_mat 2 0) := by
        calc v2_mat 2 0 = v2_mat 2 0 * 1 + v2_mat 2 1 * 0 + v2_mat 2 2 * 0 := by ring
             _ = 0 * v2_mat 0 0 + 0 * v2_mat 1 0 + -1 * v2_mat 2 0 := h
             _ = - (v2_mat 2 0) := by ring
      exact h_zero_of_eq_neg _ eq'
    have hv11 : v2_mat 1 1 = 0 := by
      have h := congr_fun (congr_fun eq_d2_v2 1) 1
      rw [Matrix.mul_apply, Fin.sum_univ_three, Matrix.mul_apply, Fin.sum_univ_three] at h
      have h01_2 : d2m 0 1 = 0 := rfl
      have h11_2 : d2m 1 1 = 1 := rfl
      have h21_2 : d2m 2 1 = 0 := rfl
      have h10_3 : d3m 1 0 = 0 := rfl
      have h11_3 : d3m 1 1 = -1 := rfl
      have h12_3 : d3m 1 2 = 0 := rfl
      rw [h01_2, h11_2, h21_2, h10_3, h11_3, h12_3] at h
      have eq' : v2_mat 1 1 = - (v2_mat 1 1) := by
        calc v2_mat 1 1 = v2_mat 1 0 * 0 + v2_mat 1 1 * 1 + v2_mat 1 2 * 0 := by ring
             _ = 0 * v2_mat 0 1 + -1 * v2_mat 1 1 + 0 * v2_mat 2 1 := h
             _ = - (v2_mat 1 1) := by ring
      exact h_zero_of_eq_neg _ eq'
    have hv22 : v2_mat 2 2 = 0 := by
      have h := congr_fun (congr_fun eq_d2_v2 2) 2
      rw [Matrix.mul_apply, Fin.sum_univ_three, Matrix.mul_apply, Fin.sum_univ_three] at h
      have h02_2 : d2m 0 2 = 0 := rfl
      have h12_2 : d2m 1 2 = 0 := rfl
      have h22_2 : d2m 2 2 = -1 := rfl
      have h20_3 : d3m 2 0 = 0 := rfl
      have h21_3 : d3m 2 1 = 0 := rfl
      have h22_3 : d3m 2 2 = 1 := rfl
      rw [h02_2, h12_2, h22_2, h20_3, h21_3, h22_3] at h
      have eq' : v2_mat 2 2 = - (v2_mat 2 2) := by
        calc v2_mat 2 2 = 0 * v2_mat 0 2 + 0 * v2_mat 1 2 + 1 * v2_mat 2 2 := by ring
             _ = v2_mat 2 0 * 0 + v2_mat 2 1 * 0 + v2_mat 2 2 * -1 := h.symm
             _ = - (v2_mat 2 2) := by ring
      exact h_zero_of_eq_neg _ eq'
    have hv12_v21 : v2_mat 1 2 * v2_mat 2 1 = -1 := by
      have h := congr_fun (congr_fun eq_sq_v2 1) 1
      rw [Matrix.mul_apply, Fin.sum_univ_three] at h
      have hd1_11 : d1m 1 1 = -1 := rfl
      rw [hd1_11, hv10, hv11] at h
      calc v2_mat 1 2 * v2_mat 2 1 = 0 * v2_mat 0 1 + 0 * 0 + v2_mat 1 2 * v2_mat 2 1 := by ring
           _ = -1 := h
    have h_det : v2_mat.det = 1 := (φ (w2SL R)).property
    have h_det_exp : v2_mat.det = - (v2_mat 0 0 * v2_mat 1 2 * v2_mat 2 1) := by
      rw [Matrix.det_fin_three]
      rw [hv01, hv02, hv10, hv20, hv11, hv22]
      ring
    have hv00 : v2_mat 0 0 = 1 := by
      calc v2_mat 0 0 = - (-1 * v2_mat 0 0) := by ring
           _ = - (v2_mat 1 2 * v2_mat 2 1 * v2_mat 0 0) := by rw [hv12_v21]
           _ = - (v2_mat 0 0 * v2_mat 1 2 * v2_mat 2 1) := by ring
           _ = v2_mat.det := h_det_exp.symm
           _ = 1 := h_det
    have hv12 : v2_mat 1 2 = ↑mu_u := by
      have h_mu_val : (↑mu_u : R) = v2_mat 1 2 := rfl
      rw [← h_mu_val]
    have hv21 : v2_mat 2 1 = - ↑(mu_u⁻¹) := by
      have h_inv : (↑mu_u : R) * (- v2_mat 2 1) = 1 := by
        calc (↑mu_u : R) * (- v2_mat 2 1) = - (v2_mat 1 2 * v2_mat 2 1) := by rw [hv12]; ring
             _ = - (-1) := by rw [hv12_v21]
             _ = 1 := by ring
      have h_mu_inv : (↑(mu_u⁻¹) : R) * ↑mu_u = 1 := by
        rw [← Units.val_mul]
        simp
      have h_neg_v21 : - v2_mat 2 1 = ↑(mu_u⁻¹) := by
        calc - v2_mat 2 1 = 1 * (- v2_mat 2 1) := by ring
             _ = (↑(mu_u⁻¹) * ↑mu_u) * (- v2_mat 2 1) := by rw [h_mu_inv]
             _ = ↑(mu_u⁻¹) * ((↑mu_u : R) * (- v2_mat 2 1)) := by ring
             _ = ↑(mu_u⁻¹) * 1 := by rw [h_inv]
             _ = ↑(mu_u⁻¹) := by ring
      calc v2_mat 2 1 = - (- v2_mat 2 1) := by ring
           _ = - ↑(mu_u⁻¹) := by rw [h_neg_v21]
    ext i j
    have hg2_val : (↑g2 : Matrix (Fin 3) (Fin 3) R) = Matrix.diagonal ![↑(lam_u⁻¹), 1, ↑mu_u] := rfl
    rw [hg2_val]
    rw [Matrix.mul_apply, Matrix.mul_apply]
    rw [Fin.sum_univ_three, Fin.sum_univ_three]
    have h_inv : ↑mu_u * (↑(mu_u⁻¹) : R) = 1 := by 
      rw [← Units.val_mul]
      simp
    fin_cases i <;> fin_cases j
    · change (↑(lam_u⁻¹) : R) * v2_mat 0 0 + 0 * v2_mat 1 0 + 0 * v2_mat 2 0 =
      (1 : R) * ↑(lam_u⁻¹) + 0 * 0 + 0 * 0
      rw [hv00]; ring
    · change (↑(lam_u⁻¹) : R) * v2_mat 0 1 + 0 * v2_mat 1 1 + 0 * v2_mat 2 1 =
      (1 : R) * 0 + 0 * 1 + 0 * 0
      rw [hv01]; ring
    · change (↑(lam_u⁻¹) : R) * v2_mat 0 2 + 0 * v2_mat 1 2 + 0 * v2_mat 2 2 =
      (1 : R) * 0 + 0 * 0 + 0 * ↑mu_u
      rw [hv02]; ring
    · change (0 : R) * v2_mat 0 0 + 1 * v2_mat 1 0 + 0 * v2_mat 2 0 =
      (0 : R) * ↑(lam_u⁻¹) + 0 * 0 + 1 * 0
      rw [hv10]; ring
    · change (0 : R) * v2_mat 0 1 + 1 * v2_mat 1 1 + 0 * v2_mat 2 1 =
      (0 : R) * 0 + 0 * 1 + 1 * 0
      rw [hv11]; ring
    · change (0 : R) * v2_mat 0 2 + 1 * v2_mat 1 2 + 0 * v2_mat 2 2 =
      (0 : R) * 0 + 0 * 0 + 1 * ↑mu_u
      rw [hv12]; ring
    · change (0 : R) * v2_mat 0 0 + 0 * v2_mat 1 0 + ↑mu_u * v2_mat 2 0 =
      (0 : R) * ↑(lam_u⁻¹) + (-1 : R) * 0 + 0 * 0
      rw [hv20]; ring
    · change (0 : R) * v2_mat 0 1 + 0 * v2_mat 1 1 + ↑mu_u * v2_mat 2 1 =
      (0 : R) * 0 + (-1 : R) * 1 + 0 * 0
      rw [hv21, hv01, hv11]
      calc (0 : R) * 0 + 0 * 0 + ↑mu_u * -↑(mu_u⁻¹)
        _ = -(↑mu_u * ↑(mu_u⁻¹)) := by ring
        _ = -1 := by rw [h_inv]
        _ = (0 : R) * 0 + (-1 : R) * 1 + 0 * 0 := by ring
    · change (0 : R) * v2_mat 0 2 + 0 * v2_mat 1 2 + ↑mu_u * v2_mat 2 2 =
      (0 : R) * 0 + (-1 : R) * 0 + 0 * ↑mu_u
      rw [hv22]; ring
  use g2

/-! ### Facts about the standard generators

Algebra of the transvections `xᵢⱼ(c)`, and how `d₁`, `d₃`, `w₁` and `w₂` interact
with them. Everything here is elementary and checked entrywise. -/

/-! #### Conjugation

Written as `w * x = y * w` rather than `w * x * w⁻¹ = y`, so that no inverses in
`SL₃` appear. The parameter is arbitrary, so the `±1` cases are instances. -/

omit [IsLocalRing R] [Invertible (2 : R)] in
/-- `w₂ · x₁₂(c) = x₁₃(-c) · w₂`. -/
private theorem w2SL_mul_xij01 (c : R) :
    w2SL R * xijSL R 0 1 (by decide) c = xijSL R 0 2 (by decide) (-c) * w2SL R := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [xijSL, w2SL, w2, Matrix.transvection, Matrix.single, Matrix.mul_apply,
      Fin.sum_univ_three]

omit [IsLocalRing R] [Invertible (2 : R)] in
/-- `w₁ · x₁₃(c) = x₂₃(-c) · w₁`. -/
private theorem w1SL_mul_xij02 (c : R) :
    w1SL R * xijSL R 0 2 (by decide) c = xijSL R 1 2 (by decide) (-c) * w1SL R := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [xijSL, w1SL, w1, Matrix.transvection, Matrix.single, Matrix.mul_apply,
      Fin.sum_univ_three]

omit [IsLocalRing R] [Invertible (2 : R)] in
/-- `w₁ · x₁₂(c) = x₂₁(-c) · w₁`. -/
private theorem w1SL_mul_xij01 (c : R) :
    w1SL R * xijSL R 0 1 (by decide) c = xijSL R 1 0 (by decide) (-c) * w1SL R := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [xijSL, w1SL, w1, Matrix.transvection, Matrix.single, Matrix.mul_apply,
      Fin.sum_univ_three]

omit [IsLocalRing R] [Invertible (2 : R)] in
/-- `w₂ · x₂₁(c) = x₃₁(-c) · w₂`. -/
private theorem w2SL_mul_xij10 (c : R) :
    w2SL R * xijSL R 1 0 (by decide) c = xijSL R 2 0 (by decide) (-c) * w2SL R := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [xijSL, w2SL, w2, Matrix.transvection, Matrix.single, Matrix.mul_apply,
      Fin.sum_univ_three]

omit [IsLocalRing R] [Invertible (2 : R)] in
/-- `w₁ · x₃₁(c) = x₃₂(-c) · w₁`. -/
private theorem w1SL_mul_xij20 (c : R) :
    w1SL R * xijSL R 2 0 (by decide) c = xijSL R 2 1 (by decide) (-c) * w1SL R := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [xijSL, w1SL, w1, Matrix.transvection, Matrix.single, Matrix.mul_apply,
      Fin.sum_univ_three]

/-! #### Commutation

Proved here rather than imported, so this file needs only the *definitions* from
`field_aut.lean` and is unaffected by changes to its proofs. -/

omit [IsLocalRing R] [Invertible (2 : R)] in
/-- `x₁₂(u)` commutes with `x₁₃(1)`. -/
private theorem xij01_commute_xij02 (u : R) :
    xijSL R 0 1 (by decide) u * xijSL R 0 2 (by decide) 1
      = xijSL R 0 2 (by decide) 1 * xijSL R 0 1 (by decide) u := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [xijSL, Matrix.transvection, Matrix.single, Matrix.mul_apply, Fin.sum_univ_three]

omit [IsLocalRing R] [Invertible (2 : R)] in
/-- `x₁₂(u)` commutes with `x₃₂(1)`. -/
private theorem xij01_commute_xij21 (u : R) :
    xijSL R 0 1 (by decide) u * xijSL R 2 1 (by decide) 1
      = xijSL R 2 1 (by decide) 1 * xijSL R 0 1 (by decide) u := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [xijSL, Matrix.transvection, Matrix.single, Matrix.mul_apply, Fin.sum_univ_three]

omit [IsLocalRing R] [Invertible (2 : R)] in
/-- The commutator relation `[x₁₂(u), x₂₃(v)] = x₁₃(uv)`, in product form. -/
private theorem xij01_mul_xij12 (u v : R) :
    xijSL R 0 1 (by decide) u * xijSL R 1 2 (by decide) v
      = xijSL R 0 2 (by decide) (u * v) * xijSL R 1 2 (by decide) v
        * xijSL R 0 1 (by decide) u := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [xijSL, Matrix.transvection, Matrix.single, Matrix.mul_apply, Fin.sum_univ_three]

omit [IsLocalRing R] in
/-- If `x = -x` and `2` is invertible then `x = 0`.

Self-contained replacement for `FieldAutomorphisms.zero_iff_eq_neg_self`, so that
this file depends on `field_aut.lean` only for *definitions*, never for theorems. -/
private theorem eq_zero_of_eq_neg_self {x : R} (h : x = -x) : x = 0 := by
  have h2 : (2 : R) * x = 0 := by linear_combination h
  have h3 := congrArg (fun y : R => ⅟(2:R) * y) h2
  simp only [mul_zero] at h3
  rwa [← mul_assoc, invOf_mul_self, one_mul] at h3

omit [IsLocalRing R] [Invertible (2 : R)] in
/-- Bridge: the named `x12SL` is the generic transvection at `(0,1)` with parameter `1`. -/
private theorem xij01_eq_x12SL : xijSL R 0 1 (by decide) 1 = x12SL R := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [xijSL, x12SL, x12, Matrix.transvection, Matrix.single]

omit [IsLocalRing R] [Invertible (2 : R)] in
/-- `xᵢⱼ(c) * xᵢⱼ(d) = xᵢⱼ(c+d)`. -/
private theorem xijSL_mul (i j : Fin 3) (hij : i ≠ j) (c d : R) :
    xijSL R i j hij c * xijSL R i j hij d = xijSL R i j hij (c + d) := by
  apply Subtype.ext
  show Matrix.transvection i j c * Matrix.transvection i j d = Matrix.transvection i j (c + d)
  exact Matrix.transvection_mul_transvection_same i j hij c d

omit [IsLocalRing R] [Invertible (2 : R)] in
/-- `xᵢⱼ(0) = 1`. -/
private theorem xijSL_zero (i j : Fin 3) (hij : i ≠ j) : xijSL R i j hij 0 = 1 := by
  apply Subtype.ext
  show Matrix.transvection i j (0 : R) = 1
  exact Matrix.transvection_zero i j

omit [IsLocalRing R] [Invertible (2 : R)] in
/-- `xᵢⱼ(c)⁻¹ = xᵢⱼ(-c)`. -/
private theorem xijSL_inv (i j : Fin 3) (hij : i ≠ j) (c : R) :
    (xijSL R i j hij c)⁻¹ = xijSL R i j hij (-c) := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [xijSL_mul R i j hij, add_neg_cancel, xijSL_zero R i j hij]

omit [IsLocalRing R] [Invertible (2 : R)] in
/-- Transport along a conjugation relation `w * a = b * w`. -/
private theorem map_eq_self_of_conj (φ : AutSL3 R) {w a b : SL3 R}
    (hw : φ w = w) (ha : φ a = a) (h : w * a = b * w) : φ b = b := by
  have hcong := congrArg φ h
  rw [map_mul, map_mul, hw, ha, h] at hcong
  exact (mul_right_cancel hcong).symm

omit [IsLocalRing R] [Invertible (2 : R)] in
/-- `φ` fixes `xᵢⱼ(-1)` whenever it fixes `xᵢⱼ(1)`. -/
private theorem map_xijSL_neg_one_eq_self (φ : AutSL3 R) (i j : Fin 3) (hij : i ≠ j)
    (h : φ (xijSL R i j hij 1) = xijSL R i j hij 1) :
    φ (xijSL R i j hij (-1)) = xijSL R i j hij (-1) := by
  rw [← xijSL_inv R i j hij 1, map_inv, h]

omit [IsLocalRing R] [Invertible (2 : R)] in
/-- Step G: fixing `w₁, w₂, x₁₂(1)` forces every `xᵢⱼ(1)` to be fixed. -/
private theorem map_xijSL_one_eq_self (φ : AutSL3 R)
    (hw1 : φ (w1SL R) = w1SL R) (hw2 : φ (w2SL R) = w2SL R)
    (hx12 : φ (xijSL R 0 1 (by decide) 1) = xijSL R 0 1 (by decide) 1) :
    ∀ i j : Fin 3, ∀ hij : i ≠ j,
      φ (xijSL R i j hij 1) = xijSL R i j hij 1 := by
  have hx12n := map_xijSL_neg_one_eq_self R φ 0 1 (by decide) hx12
  have hx13 : φ (xijSL R 0 2 (by decide) 1) = xijSL R 0 2 (by decide) 1 :=
    map_eq_self_of_conj R φ hw2 hx12n (by simpa using w2SL_mul_xij01 R (-1))
  have hx13n := map_xijSL_neg_one_eq_self R φ 0 2 (by decide) hx13
  have hx23 : φ (xijSL R 1 2 (by decide) 1) = xijSL R 1 2 (by decide) 1 :=
    map_eq_self_of_conj R φ hw1 hx13n (by simpa using w1SL_mul_xij02 R (-1))
  have hx21 : φ (xijSL R 1 0 (by decide) 1) = xijSL R 1 0 (by decide) 1 :=
    map_eq_self_of_conj R φ hw1 hx12n (by simpa using w1SL_mul_xij01 R (-1))
  have hx21n := map_xijSL_neg_one_eq_self R φ 1 0 (by decide) hx21
  have hx31 : φ (xijSL R 2 0 (by decide) 1) = xijSL R 2 0 (by decide) 1 :=
    map_eq_self_of_conj R φ hw2 hx21n (by simpa using w2SL_mul_xij10 R (-1))
  have hx31n := map_xijSL_neg_one_eq_self R φ 2 0 (by decide) hx31
  have hx32 : φ (xijSL R 2 1 (by decide) 1) = xijSL R 2 1 (by decide) 1 :=
    map_eq_self_of_conj R φ hw1 hx31n (by simpa using w1SL_mul_xij20 R (-1))
  intro i j hij
  fin_cases i <;> fin_cases j <;> first
    | exact absurd rfl hij
    | assumption

omit [IsLocalRing R] [Invertible (2 : R)] in
/-- Step A relation: `d₃` commutes with `x₁₂(1)`. -/
private theorem d3SL_commute_xij01 :
    d3SL R * xijSL R 0 1 (by decide) 1 = xijSL R 0 1 (by decide) 1 * d3SL R := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [xijSL, d3SL, d3, Matrix.transvection, Matrix.single, Matrix.mul_apply,
      Matrix.diagonal]

omit [IsLocalRing R] [Invertible (2 : R)] in
/-- Step C relation: `d₁` inverts `x₁₂(1)`. -/
private theorem d1SL_conj_xij01 :
    d1SL R * xijSL R 0 1 (by decide) 1 * d1SL R = xijSL R 0 1 (by decide) (-1) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [xijSL, d1SL, d1, Matrix.transvection, Matrix.single, Matrix.mul_apply,
      Matrix.diagonal]

/-- Steps A–C: the image of `x₁₂(1)` has the constrained shape, with `b` a unit. -/
private theorem coe_map_x12SL_form (φ : AutSL3 R)
    (hd1 : φ (d1SL R) = d1SL R) (hd3 : φ (d3SL R) = d3SL R)
    (hmod : SLCongruentModJ R (φ (x12SL R)) (x12SL R)) :
    ∃ a b c : R, IsUnit b ∧ a * a - b * c = 1 ∧
      ((φ (x12SL R) : Matrix (Fin 3) (Fin 3) R)) = !![a, b, 0; c, a, 0; 0, 0, 1] := by
  set X : Matrix (Fin 3) (Fin 3) R := (φ (x12SL R) : Matrix (Fin 3) (Fin 3) R) with hX
  -- Step A : X commutes with d3, killing the off-block entries.
  have hAsl : d3SL R * φ (x12SL R) = φ (x12SL R) * d3SL R := by
    have h := congrArg φ (d3SL_commute_xij01 R)
    rw [map_mul, map_mul, hd3, xij01_eq_x12SL] at h
    exact h
  have hA : (d3 R) * X = X * (d3 R) := by
    have h : ((d3SL R * φ (x12SL R) : SL3 R) : Matrix (Fin 3) (Fin 3) R)
        = ((φ (x12SL R) * d3SL R : SL3 R) : Matrix (Fin 3) (Fin 3) R) := by rw [hAsl]
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul] at h
    exact h
  have e02 : X 0 2 = 0 := by
    have h := congr_fun (congr_fun hA 0) 2
    simp [Matrix.mul_apply, d3, Matrix.diagonal] at h
    exact eq_zero_of_eq_neg_self R h.symm
  have e12 : X 1 2 = 0 := by
    have h := congr_fun (congr_fun hA 1) 2
    simp [Matrix.mul_apply, d3, Matrix.diagonal] at h
    exact eq_zero_of_eq_neg_self R h.symm
  have e20 : X 2 0 = 0 := by
    have h := congr_fun (congr_fun hA 2) 0
    simp [Matrix.mul_apply, d3, Matrix.diagonal] at h
    exact eq_zero_of_eq_neg_self R h
  have e21 : X 2 1 = 0 := by
    have h := congr_fun (congr_fun hA 2) 1
    simp [Matrix.mul_apply, d3, Matrix.diagonal] at h
    exact eq_zero_of_eq_neg_self R h
  -- the block shape
  have hshape : X = !![X 0 0, X 0 1, 0; X 1 0, X 1 1, 0; 0, 0, X 2 2] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [e02, e12, e20, e21]
  -- Step B : the (0,1) entry is a unit, because it is 1 mod J.
  have hbunit : IsUnit (X 0 1) := by
    have hj : X 0 1 - (1 : R) ∈ J R := by
      have h := hmod 0 1
      simpa [x12SL, x12, hX] using h
    have hres : IsLocalRing.residue R (X 0 1) = 1 := by
      have h := (Ideal.Quotient.eq (I := J R) (x := X 0 1) (y := (1 : R))).2 hj
      rw [map_one] at h
      exact h
    exact isUnit_of_map_unit (IsLocalRing.residue R) _ (by rw [hres]; exact isUnit_one)
  -- Step C : d1 inverts X.
  have hCsl : d1SL R * φ (x12SL R) * d1SL R = (φ (x12SL R))⁻¹ := by
    have h := congrArg φ (d1SL_conj_xij01 R)
    rw [map_mul, map_mul, hd1, ← xijSL_inv R 0 1 (by decide) 1, map_inv,
      xij01_eq_x12SL] at h
    exact h
  have hC : ((d1 R) * X * (d1 R)) * X = 1 := by
    have h : ((d1SL R * φ (x12SL R) * d1SL R * φ (x12SL R) : SL3 R) :
          Matrix (Fin 3) (Fin 3) R)
        = ((1 : SL3 R) : Matrix (Fin 3) (Fin 3) R) := by
      rw [hCsl, inv_mul_cancel]
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one] at h
    exact h
  rw [hshape] at hC
  have q00 := congr_fun (congr_fun hC 0) 0
  have q01 := congr_fun (congr_fun hC 0) 1
  have q22 := congr_fun (congr_fun hC 2) 2
  simp [Matrix.mul_apply, d1, Matrix.diagonal, Fin.sum_univ_three] at q00 q01 q22
  -- determinant
  have hdet : X.det = 1 := (φ (x12SL R)).property
  rw [hshape, Matrix.det_fin_three] at hdet
  simp at hdet
  -- b is a unit, so a = d
  have hbd : X 0 1 * (X 0 0 - X 1 1) = 0 := by linear_combination q01
  have hsub : X 0 0 - X 1 1 = 0 := (hbunit.mul_right_eq_zero).mp hbd
  have hd : X 1 1 = X 0 0 := (sub_eq_zero.mp hsub).symm
  rw [hd] at hdet
  -- the determinant then forces e = 1
  have he : X 2 2 = 1 := by linear_combination hdet - X 2 2 * q00
  refine ⟨X 0 0, X 0 1, X 1 0, hbunit, by linear_combination q00, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [e02, e12, e20, e21, hd, he]

omit [IsLocalRing R] [Invertible (2 : R)] in
/-- `w₂` transposed, as a literal. -/
private theorem w2_transpose : (w2 R)ᵀ = !![1, 0, 0; 0, 0, -1; 0, 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [w2, Matrix.transpose]

omit [IsLocalRing R] [Invertible (2 : R)] in
/-- `w₂` is orthogonal. -/
private theorem w2_mul_transpose_self : (w2 R) * (w2 R)ᵀ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [w2, Matrix.mul_apply, Matrix.transpose, Fin.sum_univ_three]

/-- Steps D–E: the image of `x₁₂(1)` is `x₁₂(b)` for a unit `b`. -/
private theorem coe_map_x12SL_eq_xij01 (φ : AutSL3 R)
    (hd1 : φ (d1SL R) = d1SL R) (hd3 : φ (d3SL R) = d3SL R)
    (hw2 : φ (w2SL R) = w2SL R)
    (hmod : SLCongruentModJ R (φ (x12SL R)) (x12SL R)) :
    ∃ b : R, IsUnit b ∧
      ((φ (x12SL R) : Matrix (Fin 3) (Fin 3) R)) = !![1, b, 0; 0, 1, 0; 0, 0, 1] ∧
      ((φ (xijSL R 0 2 (by decide) 1) : Matrix (Fin 3) (Fin 3) R))
        = !![1, 0, b; 0, 1, 0; 0, 0, 1] := by
  obtain ⟨a, b, c, hb, hq, hX⟩ := coe_map_x12SL_form R φ hd1 hd3 hmod
  -- X⁻¹ = d1 * X * d1
  have hCsl : d1SL R * φ (x12SL R) * d1SL R = (φ (x12SL R))⁻¹ := by
    have h := congrArg φ (d1SL_conj_xij01 R)
    rw [map_mul, map_mul, hd1, ← xijSL_inv R 0 1 (by decide) 1, map_inv,
      xij01_eq_x12SL] at h
    exact h
  have hinv : ((((φ (x12SL R))⁻¹ : SL3 R)) : Matrix (Fin 3) (Fin 3) R)
      = !![a, -b, 0; -c, a, 0; 0, 0, 1] := by
    have h : ((d1SL R * φ (x12SL R) * d1SL R : SL3 R) : Matrix (Fin 3) (Fin 3) R)
        = (((φ (x12SL R))⁻¹ : SL3 R) : Matrix (Fin 3) (Fin 3) R) := by rw [hCsl]
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul] at h
    rw [← h, hX]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [d1SL, d1, Matrix.mul_apply, Matrix.diagonal]
  -- Z * w2 = w2 * X⁻¹  (from C1 pushed through φ)
  have hZsl : φ (xijSL R 0 2 (by decide) 1) * w2SL R
      = w2SL R * (φ (x12SL R))⁻¹ := by
    have h := congrArg φ (show w2SL R * xijSL R 0 1 (by decide) (-1)
        = xijSL R 0 2 (by decide) 1 * w2SL R by simpa using w2SL_mul_xij01 R (-1))
    rw [map_mul, map_mul, hw2, ← xijSL_inv R 0 1 (by decide) 1, map_inv,
      xij01_eq_x12SL] at h
    exact h.symm
  have hZm : ((φ (xijSL R 0 2 (by decide) 1) : SL3 R) : Matrix (Fin 3) (Fin 3) R) * (w2 R)
      = (w2 R) * !![a, -b, 0; -c, a, 0; 0, 0, 1] := by
    have h : ((φ (xijSL R 0 2 (by decide) 1) * w2SL R : SL3 R) :
          Matrix (Fin 3) (Fin 3) R)
        = ((w2SL R * (φ (x12SL R))⁻¹ : SL3 R) : Matrix (Fin 3) (Fin 3) R) := by
      rw [hZsl]
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hinv] at h
    exact h
  have hZ : ((φ (xijSL R 0 2 (by decide) 1) : SL3 R) : Matrix (Fin 3) (Fin 3) R)
      = !![a, 0, b; 0, 1, 0; c, 0, a] := by
    have h := congrArg (fun M : Matrix (Fin 3) (Fin 3) R => M * (w2 R)ᵀ) hZm
    simp only [Matrix.mul_assoc, w2_mul_transpose_self, Matrix.mul_one] at h
    rw [h, w2_transpose]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [w2, Matrix.mul_apply, Fin.sum_univ_three]
  -- X and Z commute
  have hcm : ((φ (x12SL R) : SL3 R) : Matrix (Fin 3) (Fin 3) R)
        * ((φ (xijSL R 0 2 (by decide) 1) : SL3 R) : Matrix (Fin 3) (Fin 3) R)
      = ((φ (xijSL R 0 2 (by decide) 1) : SL3 R) : Matrix (Fin 3) (Fin 3) R)
        * ((φ (x12SL R) : SL3 R) : Matrix (Fin 3) (Fin 3) R) := by
    have h := congrArg φ (xij01_commute_xij02 R 1)
    rw [map_mul, map_mul, xij01_eq_x12SL] at h
    have h2 : ((φ (x12SL R) * φ (xijSL R 0 2 (by decide) 1) : SL3 R) :
          Matrix (Fin 3) (Fin 3) R)
        = ((φ (xijSL R 0 2 (by decide) 1) * φ (x12SL R) : SL3 R) :
          Matrix (Fin 3) (Fin 3) R) := by rw [h]
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul] at h2
    exact h2
  rw [hX, hZ] at hcm
  have p01 := congr_fun (congr_fun hcm 0) 1
  have p12 := congr_fun (congr_fun hcm 1) 2
  simp [Matrix.mul_apply, Fin.sum_univ_three] at p01 p12
  -- b a unit turns these into a = 1 and c = 0
  have ha : a = 1 := by
    refine hb.mul_left_cancel ?_
    rw [mul_one]
    linear_combination -p01
  have hc : c = 0 := by
    refine (hb.mul_right_eq_zero).mp ?_
    linear_combination p12
  exact ⟨b, hb, by rw [hX, ha, hc], by rw [hZ, ha, hc]⟩

omit [IsLocalRing R] [Invertible (2 : R)] in
/-- `w₁` transposed, as a literal. -/
private theorem w1_transpose : (w1 R)ᵀ = !![0, -1, 0; 1, 0, 0; 0, 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [w1, Matrix.transpose]

omit [IsLocalRing R] [Invertible (2 : R)] in
/-- `w₁` is orthogonal. -/
private theorem w1_mul_transpose_self : (w1 R) * (w1 R)ᵀ = 1 := by
  rw [w1_transpose]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [w1, Matrix.mul_apply, Fin.sum_univ_three]

/-- Step F: `φ` fixes `x₁₂(1)` exactly. -/
private theorem map_xij01_eq_self (φ : AutSL3 R)
    (hd1 : φ (d1SL R) = d1SL R) (hd3 : φ (d3SL R) = d3SL R)
    (hw1 : φ (w1SL R) = w1SL R) (hw2 : φ (w2SL R) = w2SL R)
    (hmod : SLCongruentModJ R (φ (x12SL R)) (x12SL R)) :
    φ (xijSL R 0 1 (by decide) 1) = xijSL R 0 1 (by decide) 1 := by
  obtain ⟨b, hb, hX, hZ⟩ := coe_map_x12SL_eq_xij01 R φ hd1 hd3 hw2 hmod
  -- φ(x₁₃(-1)) = x₁₃(-b), via `w₂ · x₁₂(1) = x₁₃(-1) · w₂`
  have hZnegsl : w2SL R * φ (x12SL R)
      = φ (xijSL R 0 2 (by decide) (-1)) * w2SL R := by
    have h := congrArg φ (w2SL_mul_xij01 R 1)
    rw [map_mul, map_mul, hw2, xij01_eq_x12SL] at h
    exact h
  have hZnegm : (w2 R) * ((φ (x12SL R) : SL3 R) : Matrix (Fin 3) (Fin 3) R)
      = ((φ (xijSL R 0 2 (by decide) (-1)) : SL3 R) : Matrix (Fin 3) (Fin 3) R) * (w2 R) := by
    have h : ((w2SL R * φ (x12SL R) : SL3 R) : Matrix (Fin 3) (Fin 3) R)
        = ((φ (xijSL R 0 2 (by decide) (-1)) * w2SL R : SL3 R) :
          Matrix (Fin 3) (Fin 3) R) := by rw [hZnegsl]
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul] at h
    exact h
  have hZneg : ((φ (xijSL R 0 2 (by decide) (-1)) : SL3 R) : Matrix (Fin 3) (Fin 3) R)
      = !![1, 0, -b; 0, 1, 0; 0, 0, 1] := by
    have h := congrArg (fun M : Matrix (Fin 3) (Fin 3) R => M * (w2 R)ᵀ) hZnegm.symm
    simp only [Matrix.mul_assoc, w2_mul_transpose_self, Matrix.mul_one] at h
    rw [h, hX, w2_transpose]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [w2, Matrix.mul_apply, Fin.sum_univ_three]
  -- φ(x₂₃(1)) = x₂₃(b)
  have hYsl : w1SL R * φ (xijSL R 0 2 (by decide) (-1))
      = φ (xijSL R 1 2 (by decide) 1) * w1SL R := by
    have h := congrArg φ (show w1SL R * xijSL R 0 2 (by decide) (-1)
        = xijSL R 1 2 (by decide) 1 * w1SL R by simpa using w1SL_mul_xij02 R (-1))
    rw [map_mul, map_mul, hw1] at h
    exact h
  have hYm : (w1 R) * ((φ (xijSL R 0 2 (by decide) (-1)) : SL3 R) : Matrix (Fin 3) (Fin 3) R)
      = ((φ (xijSL R 1 2 (by decide) 1) : SL3 R) : Matrix (Fin 3) (Fin 3) R) * (w1 R) := by
    have h : ((w1SL R * φ (xijSL R 0 2 (by decide) (-1)) : SL3 R) :
          Matrix (Fin 3) (Fin 3) R)
        = ((φ (xijSL R 1 2 (by decide) 1) * w1SL R : SL3 R) :
          Matrix (Fin 3) (Fin 3) R) := by rw [hYsl]
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul] at h
    exact h
  have hY : ((φ (xijSL R 1 2 (by decide) 1) : SL3 R) : Matrix (Fin 3) (Fin 3) R)
      = !![1, 0, 0; 0, 1, b; 0, 0, 1] := by
    have h := congrArg (fun M : Matrix (Fin 3) (Fin 3) R => M * (w1 R)ᵀ) hYm.symm
    simp only [Matrix.mul_assoc, w1_mul_transpose_self, Matrix.mul_one] at h
    rw [h, hZneg, w1_transpose]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [w1, Matrix.mul_apply, Fin.sum_univ_three]
  -- the commutator relation forces b² = b
  have hrel : ((φ (x12SL R) : SL3 R) : Matrix (Fin 3) (Fin 3) R)
        * ((φ (xijSL R 1 2 (by decide) 1) : SL3 R) : Matrix (Fin 3) (Fin 3) R)
      = ((φ (xijSL R 0 2 (by decide) 1) : SL3 R) : Matrix (Fin 3) (Fin 3) R)
        * ((φ (xijSL R 1 2 (by decide) 1) : SL3 R) : Matrix (Fin 3) (Fin 3) R)
        * ((φ (x12SL R) : SL3 R) : Matrix (Fin 3) (Fin 3) R) := by
    have h := congrArg φ (show xijSL R 0 1 (by decide) 1 * xijSL R 1 2 (by decide) 1
        = xijSL R 0 2 (by decide) 1 * xijSL R 1 2 (by decide) 1 * xijSL R 0 1 (by decide) 1
      by simpa using xij01_mul_xij12 R 1 1)
    rw [map_mul, map_mul, map_mul, xij01_eq_x12SL] at h
    have h2 : ((φ (x12SL R) * φ (xijSL R 1 2 (by decide) 1) : SL3 R) :
          Matrix (Fin 3) (Fin 3) R)
        = ((φ (xijSL R 0 2 (by decide) 1) * φ (xijSL R 1 2 (by decide) 1)
            * φ (x12SL R) : SL3 R) : Matrix (Fin 3) (Fin 3) R) := by rw [h]
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_mul] at h2
    exact h2
  rw [hX, hY, hZ] at hrel
  have hbb := congr_fun (congr_fun hrel 0) 2
  simp [Matrix.mul_apply, Fin.sum_univ_three] at hbb
  -- b is a unit and b² = b, so b = 1
  have hb1 : b = 1 := by
    refine hb.mul_left_cancel ?_
    rw [mul_one]
    linear_combination hbb
  rw [xij01_eq_x12SL]
  apply Subtype.ext
  rw [hX, hb1]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [x12SL, x12]

/--
Lemma 5 from Block 4: after the previous normalizations, the congruence
condition on `x₁₂(1)` forces all elementary transvections with parameter `1` to
be fixed exactly.
-/
theorem transvections_one_preserved_after_local_normalization
    (φ : AutSL3 R)
    (hdiag_w_exact :
      φ (d1SL R) = d1SL R ∧
      φ (d2SL R) = d2SL R ∧
      φ (d3SL R) = d3SL R ∧
      φ (w1SL R) = w1SL R ∧
      φ (w2SL R) = w2SL R)
    (hx12_mod : SL3FixedModJ R φ (x12SL R)) :
    ∀ i j : Fin 3, ∀ hij : i ≠ j,
      φ (xijSL R i j hij 1) = xijSL R i j hij 1 := by
  obtain ⟨hd1, _hd2, hd3, hw1, hw2⟩ := hdiag_w_exact
  exact map_xijSL_one_eq_self R φ hw1 hw2
    (map_xij01_eq_self R φ hd1 hd3 hw1 hw2 hx12_mod)

/-- A local-ring version of the predicate that an element is an elementary transvection. -/
def IsTransvectionSL3 (x : SL3 R) : Prop :=
  ∃ i j : Fin 3, ∃ hij : i ≠ j, ∃ c : R,
    x = xijSL R i j hij c

/-! ### From fixed generators to a ring automorphism

If `φ` fixes every `xᵢⱼ(1)`, then it sends `x₁₂(u)` to `x₁₂(f u)` for one bijection
`f`, and `f` turns out to be a ring automorphism. -/

omit [IsLocalRing R] [Invertible (2 : R)] in
/-- Push a commutation `A * B = B * A` through `φ` when `φ` fixes `B`. -/
private theorem coe_commute_of_map_eq_self (φ : AutSL3 R) {A B : SL3 R} (hB : φ B = B) (h : A * B = B * A) :
    ((φ A : SL3 R) : Matrix (Fin 3) (Fin 3) R) * ((B : SL3 R) : Matrix (Fin 3) (Fin 3) R)
      = ((B : SL3 R) : Matrix (Fin 3) (Fin 3) R)
        * ((φ A : SL3 R) : Matrix (Fin 3) (Fin 3) R) := by
  have h1 := congrArg φ h
  rw [map_mul, map_mul, hB] at h1
  have h2 : ((φ A * B : SL3 R) : Matrix (Fin 3) (Fin 3) R)
      = ((B * φ A : SL3 R) : Matrix (Fin 3) (Fin 3) R) := by rw [h1]
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul] at h2
  exact h2

omit [IsLocalRing R] [Invertible (2 : R)] in
/-- Step 4a: the image of `x₁₂(u)` is `a·I + b·E₀₁` with `a` a unit. -/
private theorem coe_map_xij01_form (φ : AutSL3 R)
    (hall : ∀ i j : Fin 3, ∀ hij : i ≠ j, φ (xijSL R i j hij 1) = xijSL R i j hij 1)
    (u : R) :
    ∃ a b : R, IsUnit a ∧
      ((φ (xijSL R 0 1 (by decide) u) : SL3 R) : Matrix (Fin 3) (Fin 3) R)
        = !![a, b, 0; 0, a, 0; 0, 0, a] := by
  set Y : Matrix (Fin 3) (Fin 3) R :=
    ((φ (xijSL R 0 1 (by decide) u) : SL3 R) : Matrix (Fin 3) (Fin 3) R) with hYdef
  have h1 : Y * ((xijSL R 0 1 (by decide) 1 : SL3 R) : Matrix (Fin 3) (Fin 3) R)
      = ((xijSL R 0 1 (by decide) 1 : SL3 R) : Matrix (Fin 3) (Fin 3) R) * Y :=
    coe_commute_of_map_eq_self R φ (hall 0 1 (by decide))
      (by rw [xijSL_mul, xijSL_mul, add_comm])
  have h2 : Y * ((xijSL R 0 2 (by decide) 1 : SL3 R) : Matrix (Fin 3) (Fin 3) R)
      = ((xijSL R 0 2 (by decide) 1 : SL3 R) : Matrix (Fin 3) (Fin 3) R) * Y :=
    coe_commute_of_map_eq_self R φ (hall 0 2 (by decide)) (xij01_commute_xij02 R u)
  have h3 : Y * ((xijSL R 2 1 (by decide) 1 : SL3 R) : Matrix (Fin 3) (Fin 3) R)
      = ((xijSL R 2 1 (by decide) 1 : SL3 R) : Matrix (Fin 3) (Fin 3) R) * Y :=
    coe_commute_of_map_eq_self R φ (hall 2 1 (by decide)) (xij01_commute_xij21 R u)
  have e10 := congr_fun (congr_fun h1 0) 0
  have e00 := congr_fun (congr_fun h1 0) 1
  have e12 := congr_fun (congr_fun h1 0) 2
  have e20 := congr_fun (congr_fun h1 2) 1
  have e21 := congr_fun (congr_fun h2 0) 1
  have e22 := congr_fun (congr_fun h2 0) 2
  have e02 := congr_fun (congr_fun h3 0) 1
  simp [xijSL, Matrix.transvection, Matrix.single, Matrix.mul_apply,
    Fin.sum_univ_three] at e10 e00 e12 e20 e21 e22 e02
  have ha11 : Y 1 1 = Y 0 0 := by linear_combination -e00
  have ha22 : Y 2 2 = Y 0 0 := by linear_combination -e22
  have hshape : Y = !![Y 0 0, Y 0 1, 0; 0, Y 0 0, 0; 0, 0, Y 0 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [e10, e12, e20, e21, e02, ha11, ha22]
  have hdet : Y.det = 1 := (φ (xijSL R 0 1 (by decide) u)).property
  rw [hshape, Matrix.det_fin_three] at hdet
  simp at hdet
  refine ⟨Y 0 0, Y 0 1, ?_, hshape⟩
  exact ⟨⟨Y 0 0, Y 0 0 * Y 0 0, by linear_combination hdet,
    by linear_combination hdet⟩, rfl⟩

omit [IsLocalRing R] [Invertible (2 : R)] in
/-- `[x₁₂(u), x₂₃(-1)] = x₁₃(-u)`, in product form. -/
private theorem xij01_mul_xij12_neg_one (u : R) :
    xijSL R 0 1 (by decide) u * xijSL R 1 2 (by decide) (-1)
      = xijSL R 0 2 (by decide) (-u) * xijSL R 1 2 (by decide) (-1)
        * xijSL R 0 1 (by decide) u := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [xijSL, Matrix.transvection, Matrix.single, Matrix.mul_apply, Fin.sum_univ_three]

omit [IsLocalRing R] [Invertible (2 : R)] in
/-- `x₂₃(-1)` as an explicit matrix literal. -/
private theorem coe_xij12_neg_one :
    ((xijSL R 1 2 (by decide) (-1) : SL3 R) : Matrix (Fin 3) (Fin 3) R)
      = !![1, 0, 0; 0, 1, -1; 0, 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [xijSL, Matrix.transvection, Matrix.single]

omit [IsLocalRing R] [Invertible (2 : R)] in
/-- Step 4b: the image of `x₁₂(u)` is exactly `x₁₂(b)`. -/
private theorem coe_map_xij01_eq (φ : AutSL3 R)
    (hall : ∀ i j : Fin 3, ∀ hij : i ≠ j, φ (xijSL R i j hij 1) = xijSL R i j hij 1)
    (hw2 : φ (w2SL R) = w2SL R) (u : R) :
    ∃ b : R, ((φ (xijSL R 0 1 (by decide) u) : SL3 R) : Matrix (Fin 3) (Fin 3) R)
        = !![1, b, 0; 0, 1, 0; 0, 0, 1] := by
  obtain ⟨a, b, ha, hY⟩ := coe_map_xij01_form R φ hall u
  -- φ(x₁₃(-u)) = a·I - b·E₀₂
  have hZsl : w2SL R * φ (xijSL R 0 1 (by decide) u)
      = φ (xijSL R 0 2 (by decide) (-u)) * w2SL R := by
    have h := congrArg φ (w2SL_mul_xij01 R u)
    rw [map_mul, map_mul, hw2] at h
    exact h
  have hZm : (w2 R) * ((φ (xijSL R 0 1 (by decide) u) : SL3 R) : Matrix (Fin 3) (Fin 3) R)
      = ((φ (xijSL R 0 2 (by decide) (-u)) : SL3 R) : Matrix (Fin 3) (Fin 3) R) * (w2 R) := by
    have h : ((w2SL R * φ (xijSL R 0 1 (by decide) u) : SL3 R) :
          Matrix (Fin 3) (Fin 3) R)
        = ((φ (xijSL R 0 2 (by decide) (-u)) * w2SL R : SL3 R) :
          Matrix (Fin 3) (Fin 3) R) := by rw [hZsl]
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul] at h
    exact h
  have hZ : ((φ (xijSL R 0 2 (by decide) (-u)) : SL3 R) : Matrix (Fin 3) (Fin 3) R)
      = !![a, 0, -b; 0, a, 0; 0, 0, a] := by
    have h := congrArg (fun M : Matrix (Fin 3) (Fin 3) R => M * (w2 R)ᵀ) hZm.symm
    simp only [Matrix.mul_assoc, w2_mul_transpose_self, Matrix.mul_one] at h
    rw [h, hY, w2_transpose]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [w2, Matrix.mul_apply, Fin.sum_univ_three]
  -- the commutator relation
  have hx23n := map_xijSL_neg_one_eq_self R φ 1 2 (by decide) (hall 1 2 (by decide))
  have hrel : ((φ (xijSL R 0 1 (by decide) u) : SL3 R) : Matrix (Fin 3) (Fin 3) R)
        * ((xijSL R 1 2 (by decide) (-1) : SL3 R) : Matrix (Fin 3) (Fin 3) R)
      = ((φ (xijSL R 0 2 (by decide) (-u)) : SL3 R) : Matrix (Fin 3) (Fin 3) R)
        * ((xijSL R 1 2 (by decide) (-1) : SL3 R) : Matrix (Fin 3) (Fin 3) R)
        * ((φ (xijSL R 0 1 (by decide) u) : SL3 R) : Matrix (Fin 3) (Fin 3) R) := by
    have h := congrArg φ (xij01_mul_xij12_neg_one R u)
    rw [map_mul, map_mul, map_mul, hx23n] at h
    have h2 : ((φ (xijSL R 0 1 (by decide) u) * xijSL R 1 2 (by decide) (-1) : SL3 R) :
          Matrix (Fin 3) (Fin 3) R)
        = ((φ (xijSL R 0 2 (by decide) (-u)) * xijSL R 1 2 (by decide) (-1)
            * φ (xijSL R 0 1 (by decide) u) : SL3 R) : Matrix (Fin 3) (Fin 3) R) := by rw [h]
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_mul] at h2
    exact h2
  rw [hY, hZ, coe_xij12_neg_one] at hrel
  have haa := congr_fun (congr_fun hrel 0) 0
  simp [Matrix.mul_apply, Fin.sum_univ_three] at haa
  have ha1 : a = 1 := by
    refine ha.mul_left_cancel ?_
    rw [mul_one]
    linear_combination -haa
  exact ⟨b, by rw [hY, ha1]⟩

omit [IsLocalRing R] [Invertible (2 : R)] in
/-- `xᵢⱼ(c)` as a literal at `(0,1)`. -/
private theorem coe_xij01 (c : R) :
    ((xijSL R 0 1 (by decide) c : SL3 R) : Matrix (Fin 3) (Fin 3) R)
      = !![1, c, 0; 0, 1, 0; 0, 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [xijSL, Matrix.transvection, Matrix.single]

omit [IsLocalRing R] [Invertible (2 : R)] in
/-- The parametrisation `c ↦ xᵢⱼ(c)` is injective. -/
private theorem xijSL_inj {i j : Fin 3} (hij : i ≠ j) {c d : R}
    (h : xijSL R i j hij c = xijSL R i j hij d) : c = d := by
  have h1 := congrArg (fun M : SL3 R => (M : Matrix (Fin 3) (Fin 3) R) i j) h
  simpa [xijSL, Matrix.transvection, Matrix.single, Matrix.one_apply, hij] using h1

omit [IsLocalRing R] [Invertible (2 : R)] in
/-- Step 4, packaged at the group level. -/
private theorem exists_map_xij01_eq (φ : AutSL3 R)
    (hall : ∀ i j : Fin 3, ∀ hij : i ≠ j, φ (xijSL R i j hij 1) = xijSL R i j hij 1)
    (hw2 : φ (w2SL R) = w2SL R) (u : R) :
    ∃ b : R, φ (xijSL R 0 1 (by decide) u) = xijSL R 0 1 (by decide) b := by
  obtain ⟨b, hb⟩ := coe_map_xij01_eq R φ hall hw2 u
  exact ⟨b, Subtype.ext (by rw [hb, coe_xij01])⟩

omit [IsLocalRing R] [Invertible (2 : R)] in
/-- Transfer a family `φ (xᵢⱼ c) = xᵢⱼ (f c)` along `w · xᵢⱼ(c) = x_kl(-c) · w`. -/
private theorem map_xijSL_eq_of_conj (φ : AutSL3 R) {w : SL3 R} (hw : φ w = w)
    {i j k l : Fin 3} {hij : i ≠ j} {hkl : k ≠ l} {f : R → R}
    (hconj : ∀ c : R, w * xijSL R i j hij c = xijSL R k l hkl (-c) * w)
    (hsrc : ∀ c : R, φ (xijSL R i j hij c) = xijSL R i j hij (f c))
    (hfneg : ∀ c : R, f (-c) = - f c) :
    ∀ c : R, φ (xijSL R k l hkl c) = xijSL R k l hkl (f c) := by
  intro c
  have h1 := hconj (-c)
  rw [neg_neg] at h1
  have h2 := congrArg φ h1
  rw [map_mul, map_mul, hw, hsrc, hfneg] at h2
  have h3 := hconj (- f c)
  rw [neg_neg] at h3
  rw [h3] at h2
  exact mul_right_cancel h2.symm

omit [IsLocalRing R] [Invertible (2 : R)] in
/-- Step 5 (partial): `f` exists on every index pair and is additive. -/
private theorem exists_ringHom_of_map_xijSL_one (φ : AutSL3 R)
    (hall : ∀ i j : Fin 3, ∀ hij : i ≠ j, φ (xijSL R i j hij 1) = xijSL R i j hij 1)
    (hw1 : φ (w1SL R) = w1SL R) (hw2 : φ (w2SL R) = w2SL R) :
    ∃ f : R → R, f 0 = 0 ∧ f 1 = 1 ∧ (∀ u v, f (u + v) = f u + f v) ∧
      (∀ u v, f (u * v) = f u * f v) ∧
      (∀ i j : Fin 3, ∀ hij : i ≠ j, ∀ c : R,
        φ (xijSL R i j hij c) = xijSL R i j hij (f c)) := by
  choose f hf using exists_map_xij01_eq R φ hall hw2
  -- f 0 = 0
  have hf0 : f 0 = 0 := by
    have h2 := hf 0
    rw [xijSL_zero, map_one] at h2
    refine xijSL_inj R (show (0 : Fin 3) ≠ 1 by decide) ?_
    rw [← h2, xijSL_zero]
  -- f 1 = 1
  have hf1 : f 1 = 1 := by
    refine xijSL_inj R (show (0 : Fin 3) ≠ 1 by decide) ?_
    rw [← hf 1, hall 0 1 (by decide)]
  -- additivity
  have hadd : ∀ u v : R, f (u + v) = f u + f v := by
    intro u v
    refine xijSL_inj R (show (0 : Fin 3) ≠ 1 by decide) ?_
    rw [← hf (u + v), ← xijSL_mul, map_mul, hf u, hf v, xijSL_mul]
  have hfneg : ∀ c : R, f (-c) = - f c := by
    intro c
    have h := hadd c (-c)
    rw [add_neg_cancel, hf0] at h
    linear_combination -h
  -- transfer to the other five index pairs
  have hf13 := map_xijSL_eq_of_conj R φ hw2 (w2SL_mul_xij01 R) hf hfneg
  have hf23 := map_xijSL_eq_of_conj R φ hw1 (w1SL_mul_xij02 R) hf13 hfneg
  have hf21 := map_xijSL_eq_of_conj R φ hw1 (w1SL_mul_xij01 R) hf hfneg
  have hf31 := map_xijSL_eq_of_conj R φ hw2 (w2SL_mul_xij10 R) hf21 hfneg
  have hf32 := map_xijSL_eq_of_conj R φ hw1 (w1SL_mul_xij20 R) hf31 hfneg
  -- multiplicativity, from the commutator relation
  have hmul : ∀ u v : R, f (u * v) = f u * f v := by
    intro u v
    refine xijSL_inj R (show (0 : Fin 3) ≠ 2 by decide) ?_
    have h := congrArg φ (xij01_mul_xij12 R u v)
    rw [map_mul, map_mul, map_mul, hf, hf23, hf13] at h
    have h2 := h.symm.trans (xij01_mul_xij12 R (f u) (f v))
    exact mul_right_cancel (mul_right_cancel h2)
  refine ⟨f, hf0, hf1, hadd, hmul, ?_⟩
  intro i j hij c
  fin_cases i <;> fin_cases j <;> first
    | exact absurd rfl hij
    | apply hf
    | apply hf13
    | apply hf23
    | apply hf21
    | apply hf31
    | apply hf32

omit [IsLocalRing R] [Invertible (2 : R)] in
/-- Applying a ring automorphism entrywise to a transvection. -/
private theorem xijSL_map (σ : R ≃+* R) {i j : Fin 3} (hij : i ≠ j) (c : R) :
    (xijSL R i j hij c).map (σ : R →+* R) = xijSL R i j hij (σ c) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply]
  ext x y
  simp only [Matrix.map_apply, xijSL, Matrix.transvection, Matrix.single,
    Matrix.add_apply, Matrix.of_apply, map_add]
  congr 1
  · by_cases h : x = y <;> simp [Matrix.one_apply, h]
  · by_cases h : i = x ∧ j = y <;> simp [h]

omit [IsLocalRing R] [Invertible (2 : R)] in
/-- Sorry #2: the automorphism acts on transvections by one ring automorphism. -/
private theorem exists_ringEquiv_of_map_xijSL_one (φ : AutSL3 R)
    (hall : ∀ i j : Fin 3, ∀ hij : i ≠ j, φ (xijSL R i j hij 1) = xijSL R i j hij 1)
    (hw1 : φ (w1SL R) = w1SL R) (hw2 : φ (w2SL R) = w2SL R) :
    ∃ σ : R ≃+* R, ∀ E : SL3 R, IsTransvectionSL3 R E → φ E = E.map σ := by
  obtain ⟨f, hf0, hf1, hadd, hmul, hfam⟩ := exists_ringHom_of_map_xijSL_one R φ hall hw1 hw2
  have hinj : Function.Injective f := by
    intro a b hab
    have h : φ (xijSL R 0 1 (by decide) a) = φ (xijSL R 0 1 (by decide) b) := by
      rw [hfam 0 1 (by decide) a, hfam 0 1 (by decide) b, hab]
    exact xijSL_inj R (by decide) (φ.injective h)
  have hsurj : Function.Surjective f := by
    have hall' : ∀ i j : Fin 3, ∀ hij : i ≠ j,
        φ.symm (xijSL R i j hij 1) = xijSL R i j hij 1 := by
      intro i j hij
      apply φ.injective
      rw [MulEquiv.apply_symm_apply]
      exact (hall i j hij).symm
    have hw1' : φ.symm (w1SL R) = w1SL R := by
      apply φ.injective
      rw [MulEquiv.apply_symm_apply]
      exact hw1.symm
    have hw2' : φ.symm (w2SL R) = w2SL R := by
      apply φ.injective
      rw [MulEquiv.apply_symm_apply]
      exact hw2.symm
    obtain ⟨g, _, _, _, _, hg⟩ := exists_ringHom_of_map_xijSL_one R φ.symm hall' hw1' hw2'
    intro v
    refine ⟨g v, ?_⟩
    have h2 := congrArg φ (hg 0 1 (by decide) v)
    rw [MulEquiv.apply_symm_apply, hfam 0 1 (by decide) (g v)] at h2
    exact (xijSL_inj R (by decide) h2).symm
  let fHom : R →+* R :=
    { toFun := f, map_one' := hf1, map_mul' := hmul,
      map_zero' := hf0, map_add' := hadd }
  refine ⟨RingEquiv.ofBijective fHom ⟨hinj, hsurj⟩, ?_⟩
  intro E hE
  rcases hE with ⟨i, j, hij, c, rfl⟩
  rw [hfam i j hij c, xijSL_map]
  rfl

/--
Ring-level conclusion used at the end of Block 4.  If the six basic generators
are fixed, then the automorphism acts on every elementary transvection by one
ring automorphism of `R`.

This is the local-ring analogue of the final transvection step in Part 3.
-/
theorem ring_aut_from_fixed_basic_generators
    (φ : AutSL3 R) (hfixed : BasicGeneratorsFixed R φ) :
    ∃ σ : R ≃+* R,
      ∀ E : SL3 R, IsTransvectionSL3 R E →
        φ E = E.map σ := by
  obtain ⟨hd1, hd2, hd3, hw1, hw2, hx12⟩ := hfixed
  have hmod : SL3FixedModJ R φ (x12SL R) := by
    intro i j
    rw [hx12]
    simp
  have hall := transvections_one_preserved_after_local_normalization R φ
    ⟨hd1, hd2, hd3, hw1, hw2⟩ hmod
  exact exists_ringEquiv_of_map_xijSL_one R φ hall hw1 hw2

/--
A standard form without the graph automorphism.  This is the normalized output
of Block 4.
-/
def IsStandardSL3AutNoGraph (φ : AutSL3 R) : Prop :=
  ∃ (σ : R ≃+* R) (g : GL3 R),
    ∀ x : SL3 R,
      φ x = innerAutSL3byGL3 g (x.map σ)

/--
The standard form used for the final theorem: inner automorphism, entrywise ring
automorphism, and possibly the graph automorphism.
-/
def IsStandardSL3Aut (φ : AutSL3 R) : Prop :=
  ∃ (σ : R ≃+* R) (ε : Bool) (g : GL3 R),
    ∀ x : SL3 R,
      φ x =
          innerAutSL3byGL3 g
            ((graphChoiceSL3 ε) (x.map σ))

/-! ### Putting the normalisations together

The point of `congr_modJ_of_conj` is that conjugating by something congruent to `1`
modulo `J` does not disturb a congruence modulo `J`, so the hypotheses on `w₁`, `w₂`
and `x₁₂(1)` survive both changes of basis. -/

omit [Invertible (2 : R)] in
/-- Entrywise reduction of a matrix congruent to `1` modulo `J`. -/
private theorem map_residue_eq_one_of_one_modJ (g : GL3 R) (hg : GL3IsOneModJ R g) :
    ((g : Matrix (Fin 3) (Fin 3) R)).map (IsLocalRing.residue R) = 1 := by
  ext i j
  have h2 : IsLocalRing.residue R ((g : Matrix (Fin 3) (Fin 3) R) i j)
      = IsLocalRing.residue R (((1 : GL3 R) : Matrix (Fin 3) (Fin 3) R) i j) :=
    (Ideal.Quotient.eq (I := J R)).2 (hg i j)
  have h1 : ((1 : GL3 R) : Matrix (Fin 3) (Fin 3) R) = 1 := Units.val_one
  simp only [Matrix.map_apply]
  rw [h2, h1]
  simp only [Matrix.one_apply]
  split_ifs
  · exact map_one _
  · exact map_zero _

omit [Invertible (2 : R)] in
/-- The inverse of a `GL₃` element congruent to `1` also reduces to `1`. -/
private theorem map_residue_inv_eq_one_of_one_modJ (g : GL3 R) (hg : GL3IsOneModJ R g) :
    (((g⁻¹ : GL3 R) : Matrix (Fin 3) (Fin 3) R)).map (IsLocalRing.residue R) = 1 := by
  have hmul : ((g : Matrix (Fin 3) (Fin 3) R)) * ((g⁻¹ : GL3 R) : Matrix (Fin 3) (Fin 3) R)
      = 1 := Units.mul_inv g
  have h : (((g : Matrix (Fin 3) (Fin 3) R)
        * ((g⁻¹ : GL3 R) : Matrix (Fin 3) (Fin 3) R))).map (IsLocalRing.residue R)
      = (1 : Matrix (Fin 3) (Fin 3) R).map (IsLocalRing.residue R) := by rw [hmul]
  rw [Matrix.map_mul, map_residue_eq_one_of_one_modJ R g hg, Matrix.one_mul] at h
  rw [h]
  ext i j
  simp only [Matrix.map_apply, Matrix.one_apply]
  split_ifs
  · exact map_one _
  · exact map_zero _

omit [Invertible (2 : R)] in
/-- Component A: conjugating by a `GL₃` element congruent to `1` mod `J`
does not change a congruence mod `J`. -/
private theorem congr_modJ_of_conj (g : GL3 R) (hg : GL3IsOneModJ R g) {A B : SL3 R}
    (h : SLCongruentModJ R A B) :
    SLCongruentModJ R (innerAutSL3byGL3 g A) B := by
  have hAB : ((A : SL3 R) : Matrix (Fin 3) (Fin 3) R).map (IsLocalRing.residue R)
      = ((B : SL3 R) : Matrix (Fin 3) (Fin 3) R).map (IsLocalRing.residue R) := by
    ext i j
    simp only [Matrix.map_apply]
    exact (Ideal.Quotient.eq (I := J R)).2 (h i j)
  have key : (((innerAutSL3byGL3 g A : SL3 R) : Matrix (Fin 3) (Fin 3) R)).map
        (IsLocalRing.residue R)
      = ((B : SL3 R) : Matrix (Fin 3) (Fin 3) R).map (IsLocalRing.residue R) := by
    show (((g : Matrix (Fin 3) (Fin 3) R) * (A : Matrix (Fin 3) (Fin 3) R)
      * ((g⁻¹ : GL3 R) : Matrix (Fin 3) (Fin 3) R))).map (IsLocalRing.residue R) = _
    rw [Matrix.map_mul, Matrix.map_mul, map_residue_eq_one_of_one_modJ R g hg,
      map_residue_inv_eq_one_of_one_modJ R g hg, Matrix.one_mul, Matrix.mul_one, hAB]
  intro i j
  exact (Ideal.Quotient.eq (I := J R)).1 (congr_fun (congr_fun key i) j)

omit [IsLocalRing R] [Invertible (2 : R)] in
/-- Conjugations compose. -/
private theorem innerAutSL3byGL3_comp_apply (a b : GL3 R) (x : SL3 R) :
    innerAutSL3byGL3 a (innerAutSL3byGL3 b x) = innerAutSL3byGL3 (a * b) x := by
  apply Subtype.ext
  show (a : Matrix (Fin 3) (Fin 3) R)
      * ((b : Matrix (Fin 3) (Fin 3) R) * (x : Matrix (Fin 3) (Fin 3) R)
        * ((b⁻¹ : GL3 R) : Matrix (Fin 3) (Fin 3) R))
      * ((a⁻¹ : GL3 R) : Matrix (Fin 3) (Fin 3) R)
    = ((a * b : GL3 R) : Matrix (Fin 3) (Fin 3) R) * (x : Matrix (Fin 3) (Fin 3) R)
      * (((a * b)⁻¹ : GL3 R) : Matrix (Fin 3) (Fin 3) R)
  simp [Units.val_mul, mul_assoc]

omit [IsLocalRing R] [Invertible (2 : R)] in
/-- Conjugating by `g` then by `g⁻¹` is the identity. -/
private theorem innerAutSL3byGL3_inv_apply (a : GL3 R) (x : SL3 R) :
    innerAutSL3byGL3 a⁻¹ (innerAutSL3byGL3 a x) = x := by
  rw [innerAutSL3byGL3_comp_apply]
  apply Subtype.ext
  show (((a⁻¹ * a : GL3 R)) : Matrix (Fin 3) (Fin 3) R) * (x : Matrix (Fin 3) (Fin 3) R)
      * ((((a⁻¹ * a : GL3 R))⁻¹ : GL3 R) : Matrix (Fin 3) (Fin 3) R)
    = (x : Matrix (Fin 3) (Fin 3) R)
  simp

omit [IsLocalRing R] [Invertible (2 : R)] in
/-- The two transvection predicates agree. -/
private theorem isTransvectionSL3_of_cong {x : SL3 R}
    (h : CongruenceSubgroup.IsTransvectionSL3 x) : IsTransvectionSL3 R x := by
  obtain ⟨i, j, c, hij, hx⟩ := h
  exact ⟨i, j, hij, c, hx⟩

/--
Theorem 3 / Block 4, normalized local-ring statement.

If the automorphism is congruent to the identity on
`d₁,d₂,d₃,w₁,w₂,x₁₂(1)`, then it is standard with no graph part.
-/
theorem local_class_no_graph
    (φ : AutSL3 R) (hmod : BasicGeneratorsFixedModJ R φ) :
    IsStandardSL3AutNoGraph R φ := by
  obtain ⟨hd1m, hd2m, hd3m, hw1m, hw2m, hx12m⟩ := hmod
  obtain ⟨g₁, hg1one, h1d1, h1d2, h1d3⟩ :=
    diagonal_preserved_after_local_change_of_basis R φ ⟨hd1m, hd2m, hd3m⟩
  set φ₁ : AutSL3 R := φ.trans (innerAutSL3byGL3 g₁) with hφ1
  have e1w1 : SL3FixedModJ R φ₁ (w1SL R) := congr_modJ_of_conj R g₁ hg1one hw1m
  have e1w2 : SL3FixedModJ R φ₁ (w2SL R) := congr_modJ_of_conj R g₁ hg1one hw2m
  have e1x12 : SL3FixedModJ R φ₁ (x12SL R) := congr_modJ_of_conj R g₁ hg1one hx12m
  obtain ⟨g₂, hg2one, h2d1, h2d2, h2d3, h2w1, h2w2⟩ :=
    signed_transpositions_preserved_after_local_change_of_basis R φ₁
      ⟨h1d1, h1d2, h1d3⟩ ⟨e1w1, e1w2⟩
  set φ₂ : AutSL3 R := φ₁.trans (innerAutSL3byGL3 g₂) with hφ2
  have e2x12 : SL3FixedModJ R φ₂ (x12SL R) := congr_modJ_of_conj R g₂ hg2one e1x12
  have hall := transvections_one_preserved_after_local_normalization R φ₂
    ⟨h2d1, h2d2, h2d3, h2w1, h2w2⟩ e2x12
  have hx12exact : φ₂ (x12SL R) = x12SL R := by
    have h := hall 0 1 (by decide)
    rwa [xij01_eq_x12SL] at h
  obtain ⟨σ, hσ⟩ := ring_aut_from_fixed_basic_generators R φ₂
    ⟨h2d1, h2d2, h2d3, h2w1, h2w2, hx12exact⟩
  -- extend from transvections to all of SL₃(R)
  have hagree : ∀ x : SL3 R, φ₂ x = x.map (σ : R →+* R) := by
    have hEq : Set.EqOn (φ₂ : SL3 R →* SL3 R)
        (Matrix.SpecialLinearGroup.map (σ : R →+* R))
        (CongruenceSubgroup.TransvectionSetSL3 R) := by
      intro E hE
      exact hσ E (isTransvectionSL3_of_cong R hE)
    have h3 := MonoidHom.eqOn_closure hEq
    have h4 : Subgroup.closure (CongruenceSubgroup.TransvectionSetSL3 R) = ⊤ :=
      CongruenceSubgroup.SL3_generated_by_transvections R
    rw [h4] at h3
    intro x
    exact h3 (by simp)
  refine ⟨σ, (g₂ * g₁)⁻¹, ?_⟩
  intro x
  have h5 : innerAutSL3byGL3 (g₂ * g₁) (φ x) = x.map (σ : R →+* R) := by
    rw [← innerAutSL3byGL3_comp_apply]
    exact hagree x
  calc φ x = innerAutSL3byGL3 (g₂ * g₁)⁻¹ (innerAutSL3byGL3 (g₂ * g₁) (φ x)) :=
        (innerAutSL3byGL3_inv_apply R _ _).symm
    _ = innerAutSL3byGL3 (g₂ * g₁)⁻¹ (x.map (σ : R →+* R)) := by rw [h5]

/--
The same normalized local theorem, packaged in the final standard-form predicate
by choosing `ε = false`.
-/
theorem local_class
    (φ : AutSL3 R) (hmod : BasicGeneratorsFixedModJ R φ) :
    IsStandardSL3Aut R φ := by
  rcases local_class_no_graph R φ hmod with ⟨σ, g, hσg⟩
  refine ⟨σ, false, g, ?_⟩
  intro x
  simpa [IsStandardSL3AutNoGraph, IsStandardSL3Aut,
    graphChoiceSL3] using hσg x

end LocalAutomorphisms

end
