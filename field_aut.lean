import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.RingTheory.LocalRing.Defs
import Mathlib.RingTheory.LocalRing.ResidueField.Defs
import Mathlib.Tactic.LinearCombination


import cong_subgroup

open Matrix BigOperators
open scoped MatrixGroups
open CongruenceSubgroup (
    TransvectionSL3
    IsTransvectionSL3
    TransvectionSetSL3
    SL3_generated_by_transvections
    )
noncomputable section



abbrev GL3 (A : Type*) [CommRing A] : Type _ :=
  GL (Fin 3) A



variable (R : Type*) [CommRing R] [Invertible (2 : R)]



abbrev AutSL3 : Type _ :=
  SL3 R ≃* SL3 R



def innerAutSL3byGL3 {R : Type*} [CommRing R] (g : GL3 R) : AutSL3 R where
  toFun := fun x => ⟨g * Matrix.SpecialLinearGroup.toGL x * g⁻¹, by
    simp [Matrix.det_mul,  Ring.mul_inverse_cancel]⟩
  invFun := fun x =>⟨g⁻¹ * Matrix.SpecialLinearGroup.toGL x * g, by
    simp [Matrix.det_mul, Ring.inverse_mul_cancel]⟩

  left_inv := by
    intro x
    simp [mul_assoc]

  right_inv := by
    intro x
    simp [mul_assoc]

  map_mul' := by
    intro x y
    apply Subtype.ext
    simp [mul_assoc]

def invTransposeMap {R : Type*} [CommRing R] (x : SL3 R) : SL3 R :=
  ⟨(((x⁻¹ : SL3 R) : Matrix (Fin 3) (Fin 3) R).transpose), by
    rw [Matrix.det_transpose]
    exact (x⁻¹ : SL3 R).property⟩


def invTransposeAutSL3 {R : Type*} [CommRing R] : AutSL3 R where
  toFun := invTransposeMap
  invFun := invTransposeMap

  left_inv := by
    intro x
    apply Subtype.ext
    simp only [
    invTransposeMap,
    Matrix.SpecialLinearGroup.coe_mk,
    Matrix.SpecialLinearGroup.coe_inv
    ]
    rw [← Matrix.adjugate_transpose]
    simp
    rw [Matrix.adjugate_adjugate _ (by decide)]
    simp [x.property]

  right_inv := by
    intro x
    apply Subtype.ext
    simp only [
    invTransposeMap,
    Matrix.SpecialLinearGroup.coe_mk,
    Matrix.SpecialLinearGroup.coe_inv
    ]
    rw [← Matrix.adjugate_transpose]
    simp

    rw [Matrix.adjugate_adjugate _ (by decide)]
    simp [x.property]

  map_mul' := by
    intro x y
    apply Subtype.ext
    simp [invTransposeMap, Matrix.transpose_mul]





theorem zero_iff_eq_neg_self {R : Type*} [Ring R] [Invertible (2 : R)] {x : R}:
  0 = x ↔ x = -x := by
  constructor
  · intro h
    rw [← h, neg_zero]
  · intro h
    rw [← one_mul x, ← invOf_mul_self (2 : R), mul_assoc, two_mul, add_eq_zero_iff_eq_neg.mpr h,
        mul_zero]

namespace FieldAutomorpisms


variable (F : Type*) [Field F] [Invertible (2 : F)]





def d1 : Matrix (Fin 3) (Fin 3) (R) :=
  Matrix.diagonal ![1, -1, -1]

def d2 : Matrix (Fin 3) (Fin 3) (R) :=
  Matrix.diagonal ![-1, 1, -1]

def d3 : Matrix (Fin 3) (Fin 3) (R) :=
  Matrix.diagonal ![-1, -1, 1]

def d1SL : SL3 R :=
  ⟨d1 R, by
    simp [d1, Matrix.det_diagonal, Fin.prod_univ_three]
  ⟩

def d2SL : SL3 R :=
  ⟨d2 R, by
    simp [d2, Matrix.det_diagonal, Fin.prod_univ_three]
  ⟩

def d3SL : SL3 R :=
  ⟨d3 R, by
    simp [d3, Matrix.det_diagonal, Fin.prod_univ_three]
  ⟩

omit [Invertible (2 : F)] in
/-- d1 is an involution. -/
theorem d1_mul_d1 : d1SL F * d1SL F = 1 := by
  apply Subtype.ext
  show d1 F * d1 F = (1 : Matrix (Fin 3) (Fin 3) F)
  unfold d1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.diagonal_apply]

omit [Invertible (2 : F)] in
/-- d2 is an involution. -/
theorem d2_mul_d2 : d2SL F * d2SL F = 1 := by
  apply Subtype.ext
  show d2 F * d2 F = (1 : Matrix (Fin 3) (Fin 3) F)
  unfold d2
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.diagonal_apply]

omit [Invertible (2 : F)] in
/-- d3 is an involution. -/
theorem d3_mul_d3 : d3SL F * d3SL F = 1 := by
  apply Subtype.ext
  show d3 F * d3 F = (1 : Matrix (Fin 3) (Fin 3) F)
  unfold d3
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.diagonal_apply]

omit [Invertible (2 : F)] in
/-- d1 and d2 commute. -/
theorem d1_mul_d2_comm : d1SL F * d2SL F = d2SL F * d1SL F := by
  apply Subtype.ext
  show d1 F * d2 F = d2 F * d1 F
  unfold d1 d2
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.diagonal_apply]

omit [Invertible (2 : F)] in
/-- d1 * d2 = d3. -/
theorem d1_mul_d2_eq_d3 : d1SL F * d2SL F = d3SL F := by
  apply Subtype.ext
  show d1 F * d2 F = d3 F
  unfold d1 d2 d3
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.diagonal_apply]
/-- d1 is nontrivial. -/
theorem d1SL_ne_one : d1SL F ≠ 1 := by
  intro h
  have h11 : (d1 F) 1 1 = (1 : Matrix (Fin 3) (Fin 3) F) 1 1 :=
    congrArg (fun A : SL3 F => (A : Matrix (Fin 3) (Fin 3) F) 1 1) h
  simp [d1] at h11
  -- h11 : (-1 : F) = 1
  have step : (-1 : F) + 1 = 1 + 1 := congrArg (· + 1) h11
  have lhs0 : (-1 : F) + 1 = 0 := by ring
  have rhs2 : (1 : F) + 1 = 2 := by ring
  rw [lhs0, rhs2] at step
  exact (Invertible.ne_zero (2 : F)) step.symm

  /-- d2 is nontrivial. -/
  theorem d2SL_ne_one : d2SL F ≠ 1 := by
  intro h
  have h00 : (d2 F) 0 0 = (1 : Matrix (Fin 3) (Fin 3) F) 0 0 :=
    congrArg (fun A : SL3 F => (A : Matrix (Fin 3) (Fin 3) F) 0 0) h
  simp [d2] at h00
  have step : (-1 : F) + 1 = 1 + 1 := congrArg (· + 1) h00
  have lhs0 : (-1 : F) + 1 = 0 := by ring
  have rhs2 : (1 : F) + 1 = 2 := by ring
  rw [lhs0, rhs2] at step
  exact (Invertible.ne_zero (2 : F)) step.symm

 /-- d3 is nontrivial. -/
theorem d3SL_ne_one : d3SL F ≠ 1 := by
  intro h
  have h00 : (d3 F) 0 0 = (1 : Matrix (Fin 3) (Fin 3) F) 0 0 :=
    congrArg (fun A : SL3 F => (A : Matrix (Fin 3) (Fin 3) F) 0 0) h
  simp [d3] at h00
  have step : (-1 : F) + 1 = 1 + 1 := congrArg (· + 1) h00
  have lhs0 : (-1 : F) + 1 = 0 := by ring
  have rhs2 : (1 : F) + 1 = 2 := by ring
  rw [lhs0, rhs2] at step
  exact (Invertible.ne_zero (2 : F)) step.symm


omit [Invertible (2 : F)] in
theorem phi_d1_mul_self (φ : AutSL3 F) :
    φ (d1SL F) * φ (d1SL F) = 1 := by
  rw [← map_mul, d1_mul_d1, map_one]

omit [Invertible (2 : F)] in
theorem phi_d2_mul_self (φ : AutSL3 F) :
    φ (d2SL F) * φ (d2SL F) = 1 := by
  rw [← map_mul, d2_mul_d2, map_one]

omit [Invertible (2 : F)] in
theorem phi_d3_mul_self (φ : AutSL3 F) :
    φ (d3SL F) * φ (d3SL F) = 1 := by
  rw [← map_mul, d3_mul_d3, map_one]

theorem phi_d1_ne_one (φ : AutSL3 F) :
    φ (d1SL F) ≠ 1 := by
  intro h
  exact d1SL_ne_one F (φ.injective (h.trans (map_one φ).symm))

theorem phi_d2_ne_one (φ : AutSL3 F) :
    φ (d2SL F) ≠ 1 := by
  intro h
  exact d2SL_ne_one F (φ.injective (h.trans (map_one φ).symm))

theorem phi_d3_ne_one (φ : AutSL3 F) :
    φ (d3SL F) ≠ 1 := by
  intro h
  exact d3SL_ne_one F (φ.injective (h.trans (map_one φ).symm))

omit [Invertible (2 : F)] in
theorem phi_d1_d2_comm (φ : AutSL3 F) :
    φ (d1SL F) * φ (d2SL F) = φ (d2SL F) * φ (d1SL F) := by
  rw [← map_mul, ← map_mul, d1_mul_d2_comm]

omit [Invertible (2 : F)] in
theorem phi_d1_d2_eq_d3 (φ : AutSL3 F) :
    φ (d1SL F) * φ (d2SL F) = φ (d3SL F) := by
  rw [← map_mul, d1_mul_d2_eq_d3]


omit [Invertible (2 : F)] in
/-- The matrix-level version of `phi_d1_mul_self`. -/
theorem tau1_mul_self (φ : AutSL3 F) :
    (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F) *
      (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F) = 1 := by
  have h := phi_d1_mul_self F φ
  have hcoe := congrArg (fun A : SL3 F => (A : Matrix (Fin 3) (Fin 3) F)) h
  simpa using hcoe

theorem tau1_ne_neg_one (φ : AutSL3 F) :
    (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F) ≠ -1 := by
  intro h
  have hdet : (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F).det = 1 :=
    Matrix.SpecialLinearGroup.det_coe (φ (d1SL F))
  rw [h, show (-1 : Matrix (Fin 3) (Fin 3) F) = (-1 : F) • (1 : Matrix (Fin 3) (Fin 3) F) from
    (neg_one_smul F (1 : Matrix (Fin 3) (Fin 3) F)).symm,
    Matrix.det_smul, Matrix.det_one, mul_one] at hdet
  have h3 : ((-1 : F)) ^ (Fintype.card (Fin 3)) = -1 := Odd.neg_one_pow (by decide)
  rw [h3] at hdet
  -- hdet : (-1 : F) = 1
  have step : (-1 : F) + 1 = 1 + 1 := congrArg (· + 1) hdet
  have lhs0 : (-1 : F) + 1 = 0 := by ring
  have rhs2 : (1 : F) + 1 = 2 := by ring
  rw [lhs0, rhs2] at step
  exact (Invertible.ne_zero (2 : F)) step.symm

theorem tau1_ne_one (φ : AutSL3 F) :
    (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F) ≠ 1 := by
  intro h
  apply phi_d1_ne_one F φ
  apply Subtype.ext
  simpa using h

omit [Invertible (2 : F)] in
/-- Standard basis vectors of `Fin 3 → F`. Used much later to read off the columns of
the change-of-basis matrix `g` (see `gMatrix`). -/
def e1 : Fin 3 → F := ![1, 0, 0]

omit [Invertible (2 : F)] in
def e2 : Fin 3 → F := ![0, 1, 0]

omit [Invertible (2 : F)] in
def e3 : Fin 3 → F := ![0, 0, 1]

/-! ### Idempotent decomposition for an arbitrary involution `τ`

If `τ * τ = 1` and `char F ≠ 2`, then `p = (1+τ)/2` and `q = (1-τ)/2` are complementary
idempotents (`p+q=1`, `pq=qp=0`, `p²=p`, `q²=q`) whose ranges are exactly the `+1` and
`-1` eigenspaces of `τ`. We build this *once* for a generic matrix `τ`, instead of
repeating it separately for `τ1 = φ(d1)`, `τ2 = φ(d2)`, `τ3 = φ(d3)`, and specialize
three times below (`finrank_range_pIdemLin_tau3_eq_one`, etc.). -/

noncomputable def pIdem (τ : Matrix (Fin 3) (Fin 3) F) : Matrix (Fin 3) (Fin 3) F :=
  (2 : F)⁻¹ • (1 + τ)

noncomputable def qIdem (τ : Matrix (Fin 3) (Fin 3) F) : Matrix (Fin 3) (Fin 3) F :=
  (2 : F)⁻¹ • (1 - τ)

theorem pIdem_idem (τ : Matrix (Fin 3) (Fin 3) F) (hτ2 : τ * τ = 1) :
    pIdem F τ * pIdem F τ = pIdem F τ := by
  have key : (1 + τ) * (1 + τ) = (2 : F) • (1 + τ) := by
    rw [mul_add, add_mul, add_mul]
    simp only [one_mul, mul_one, hτ2]
    rw [two_smul]
    abel
  unfold pIdem
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, key, smul_smul]
  congr 1
  field_simp

theorem qIdem_idem (τ : Matrix (Fin 3) (Fin 3) F) (hτ2 : τ * τ = 1) :
    qIdem F τ * qIdem F τ = qIdem F τ := by
  have key : (1 - τ) * (1 - τ) = (2 : F) • (1 - τ) := by
    rw [mul_sub, sub_mul, sub_mul]
    simp only [one_mul, mul_one, hτ2]
    rw [two_smul]
    abel
  unfold qIdem
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, key, smul_smul]
  congr 1
  field_simp

theorem pIdem_add_qIdem (τ : Matrix (Fin 3) (Fin 3) F) :
    pIdem F τ + qIdem F τ = 1 := by
  unfold pIdem qIdem
  rw [← smul_add]
  have hsum : (1 + τ) + (1 - τ) = (2 : F) • (1 : Matrix (Fin 3) (Fin 3) F) := by
    rw [two_smul]; abel
  rw [hsum, smul_smul, inv_mul_cancel₀ (Invertible.ne_zero (2 : F)), one_smul]

omit [Invertible (2 : F)] in
theorem pIdem_mul_qIdem (τ : Matrix (Fin 3) (Fin 3) F) (hτ2 : τ * τ = 1) :
    pIdem F τ * qIdem F τ = 0 := by
  have key : (1 + τ) * (1 - τ) = 0 := by
    rw [mul_sub, add_mul, add_mul]
    simp only [one_mul, mul_one, hτ2]
    abel
  unfold pIdem qIdem
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, key, smul_zero]

omit [Invertible (2 : F)] in
theorem qIdem_mul_pIdem (τ : Matrix (Fin 3) (Fin 3) F) (hτ2 : τ * τ = 1) :
    qIdem F τ * pIdem F τ = 0 := by
  have key : (1 - τ) * (1 + τ) = 0 := by
    rw [sub_mul, mul_add, mul_add]
    simp only [one_mul, mul_one, hτ2]
    abel
  unfold qIdem pIdem
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, key, smul_zero]

theorem pIdem_sub_qIdem (τ : Matrix (Fin 3) (Fin 3) F) :
    pIdem F τ - qIdem F τ = τ := by
  unfold pIdem qIdem
  rw [← smul_sub]
  have key : (1 + τ) - (1 - τ) = (2 : F) • τ := by
    rw [two_smul]; abel
  rw [key, smul_smul, inv_mul_cancel₀ (Invertible.ne_zero (2 : F)), one_smul]

noncomputable def pIdemLin (τ : Matrix (Fin 3) (Fin 3) F) : Module.End F (Fin 3 → F) :=
  Matrix.toLinAlgEquiv' (pIdem F τ)

noncomputable def qIdemLin (τ : Matrix (Fin 3) (Fin 3) F) : Module.End F (Fin 3 → F) :=
  Matrix.toLinAlgEquiv' (qIdem F τ)

noncomputable def tauLin (τ : Matrix (Fin 3) (Fin 3) F) : Module.End F (Fin 3 → F) :=
  Matrix.toLinAlgEquiv' τ

theorem pIdemLin_idem (τ : Matrix (Fin 3) (Fin 3) F) (hτ2 : τ * τ = 1) :
    IsIdempotentElem (pIdemLin F τ) := by
  show pIdemLin F τ * pIdemLin F τ = pIdemLin F τ
  unfold pIdemLin
  rw [← map_mul, pIdem_idem F τ hτ2]

theorem qIdemLin_idem (τ : Matrix (Fin 3) (Fin 3) F) (hτ2 : τ * τ = 1) :
    IsIdempotentElem (qIdemLin F τ) := by
  show qIdemLin F τ * qIdemLin F τ = qIdemLin F τ
  unfold qIdemLin
  rw [← map_mul, qIdem_idem F τ hτ2]

theorem pIdemLin_add_qIdemLin (τ : Matrix (Fin 3) (Fin 3) F) :
    pIdemLin F τ + qIdemLin F τ = 1 := by
  unfold pIdemLin qIdemLin
  rw [← map_add, pIdem_add_qIdem, Matrix.toLinAlgEquiv'_one]
  rfl

omit [Invertible (2 : F)] in
theorem pIdemLin_mul_qIdemLin (τ : Matrix (Fin 3) (Fin 3) F) (hτ2 : τ * τ = 1) :
    pIdemLin F τ * qIdemLin F τ = 0 := by
  show pIdemLin F τ * qIdemLin F τ = 0
  unfold pIdemLin qIdemLin
  rw [← map_mul, pIdem_mul_qIdem F τ hτ2, map_zero]

theorem pIdemLin_sub_qIdemLin (τ : Matrix (Fin 3) (Fin 3) F) :
    pIdemLin F τ - qIdemLin F τ = tauLin F τ := by
  unfold pIdemLin qIdemLin tauLin
  rw [← map_sub, pIdem_sub_qIdem]

theorem tauLin_mul_qIdemLin (τ : Matrix (Fin 3) (Fin 3) F) (hτ2 : τ * τ = 1) :
    tauLin F τ * qIdemLin F τ = -qIdemLin F τ := by
  rw [← pIdemLin_sub_qIdemLin, sub_mul, pIdemLin_mul_qIdemLin F τ hτ2, qIdemLin_idem F τ hτ2,
    zero_sub]

theorem ker_pIdemLin_eq_range_qIdemLin (τ : Matrix (Fin 3) (Fin 3) F) (hτ2 : τ * τ = 1) :
    LinearMap.ker (pIdemLin F τ) = LinearMap.range (qIdemLin F τ) := by
  have hq : qIdemLin F τ = 1 - pIdemLin F τ := by
    have h := pIdemLin_add_qIdemLin F τ
    have := congrArg (fun x => x - pIdemLin F τ) h
    simpa using this
  rw [hq]
  exact LinearMap.IsIdempotentElem.ker_eq_range_one_sub (pIdemLin_idem F τ hτ2)

theorem isCompl_range_pIdemLin_range_qIdemLin (τ : Matrix (Fin 3) (Fin 3) F) (hτ2 : τ * τ = 1) :
    IsCompl (LinearMap.range (pIdemLin F τ)) (LinearMap.range (qIdemLin F τ)) := by
  rw [← ker_pIdemLin_eq_range_qIdemLin F τ hτ2]
  exact LinearMap.IsIdempotentElem.isCompl (pIdemLin_idem F τ hτ2)

theorem finrank_range_pIdemLin_add_finrank_range_qIdemLin
    (τ : Matrix (Fin 3) (Fin 3) F) (hτ2 : τ * τ = 1) :
    Module.finrank F (LinearMap.range (pIdemLin F τ)) +
      Module.finrank F (LinearMap.range (qIdemLin F τ)) = 3 := by
  rw [Submodule.finrank_add_eq_of_isCompl (isCompl_range_pIdemLin_range_qIdemLin F τ hτ2),
    Module.finrank_fin_fun]

theorem tau_ne_neg_one_of_det (τ : Matrix (Fin 3) (Fin 3) F) (hdet : τ.det = 1) :
    τ ≠ -1 := by
  intro h
  rw [h, show (-1 : Matrix (Fin 3) (Fin 3) F) = (-1 : F) • (1 : Matrix (Fin 3) (Fin 3) F) from
    (neg_one_smul F (1 : Matrix (Fin 3) (Fin 3) F)).symm,
    Matrix.det_smul, Matrix.det_one, mul_one] at hdet
  have h3 : ((-1 : F)) ^ (Fintype.card (Fin 3)) = -1 := Odd.neg_one_pow (by decide)
  rw [h3] at hdet
  have step : (-1 : F) + 1 = 1 + 1 := congrArg (· + 1) hdet
  have lhs0 : (-1 : F) + 1 = 0 := by ring
  have rhs0 : (1 : F) + 1 = 2 := by ring
  rw [lhs0, rhs0] at step
  exact (Invertible.ne_zero (2 : F)) step.symm

theorem pIdem_ne_zero (τ : Matrix (Fin 3) (Fin 3) F) (hdet : τ.det = 1) :
    pIdem F τ ≠ 0 := by
  intro h
  unfold pIdem at h
  rcases smul_eq_zero.mp h with h2 | h2
  · exact (inv_ne_zero (Invertible.ne_zero (2 : F))) h2
  · exact tau_ne_neg_one_of_det F τ hdet (eq_neg_of_add_eq_zero_right h2)

theorem qIdem_ne_zero (τ : Matrix (Fin 3) (Fin 3) F) (hτ1 : τ ≠ 1) :
    qIdem F τ ≠ 0 := by
  intro h
  unfold qIdem at h
  rcases smul_eq_zero.mp h with h2 | h2
  · exact (inv_ne_zero (Invertible.ne_zero (2 : F))) h2
  · exact hτ1 (sub_eq_zero.mp h2).symm

theorem pIdemLin_ne_zero (τ : Matrix (Fin 3) (Fin 3) F) (hdet : τ.det = 1) :
    pIdemLin F τ ≠ 0 := by
  unfold pIdemLin
  intro h
  apply pIdem_ne_zero F τ hdet
  apply Matrix.toLinAlgEquiv'.injective
  rw [h, map_zero]

theorem qIdemLin_ne_zero (τ : Matrix (Fin 3) (Fin 3) F) (hτ1 : τ ≠ 1) :
    qIdemLin F τ ≠ 0 := by
  unfold qIdemLin
  intro h
  apply qIdem_ne_zero F τ hτ1
  apply Matrix.toLinAlgEquiv'.injective
  rw [h, map_zero]

theorem range_pIdemLin_ne_bot (τ : Matrix (Fin 3) (Fin 3) F) (hdet : τ.det = 1) :
    LinearMap.range (pIdemLin F τ) ≠ ⊥ := by
  rw [Ne, LinearMap.range_eq_bot]; exact pIdemLin_ne_zero F τ hdet

theorem range_qIdemLin_ne_bot (τ : Matrix (Fin 3) (Fin 3) F) (hτ1 : τ ≠ 1) :
    LinearMap.range (qIdemLin F τ) ≠ ⊥ := by
  rw [Ne, LinearMap.range_eq_bot]; exact qIdemLin_ne_zero F τ hτ1

theorem finrank_range_pIdemLin_pos (τ : Matrix (Fin 3) (Fin 3) F) (hdet : τ.det = 1) :
    0 < Module.finrank F (LinearMap.range (pIdemLin F τ)) := by
  rw [Module.finrank_pos_iff, Submodule.nontrivial_iff_ne_bot]
  exact range_pIdemLin_ne_bot F τ hdet

theorem finrank_range_qIdemLin_pos (τ : Matrix (Fin 3) (Fin 3) F) (hτ1 : τ ≠ 1) :
    0 < Module.finrank F (LinearMap.range (qIdemLin F τ)) := by
  rw [Module.finrank_pos_iff, Submodule.nontrivial_iff_ne_bot]
  exact range_qIdemLin_ne_bot F τ hτ1

theorem range_qIdemLin_invariant (τ : Matrix (Fin 3) (Fin 3) F) (hτ2 : τ * τ = 1) :
    LinearMap.range (qIdemLin F τ) ≤ (LinearMap.range (qIdemLin F τ)).comap (tauLin F τ) := by
  rintro x ⟨y, rfl⟩
  show tauLin F τ (qIdemLin F τ y) ∈ LinearMap.range (qIdemLin F τ)
  have heq : tauLin F τ (qIdemLin F τ y) = -qIdemLin F τ y :=
    LinearMap.congr_fun (tauLin_mul_qIdemLin F τ hτ2) y
  rw [heq]
  exact ⟨-y, by rw [map_neg]⟩

theorem tauLin_eq_one_sub_two_smul_qIdemLin (τ : Matrix (Fin 3) (Fin 3) F) :
    tauLin F τ = 1 - (2 : F) • qIdemLin F τ := by
  rw [← pIdemLin_sub_qIdemLin]
  have hp1 : pIdemLin F τ = 1 - qIdemLin F τ := by
    have h := pIdemLin_add_qIdemLin F τ
    have := congrArg (fun x => x - qIdemLin F τ) h
    simpa using this
  rw [hp1, two_smul]
  abel

theorem range_qIdemLin_mapQ_eq_id (τ : Matrix (Fin 3) (Fin 3) F) (hτ2 : τ * τ = 1) :
    (LinearMap.range (qIdemLin F τ)).mapQ (LinearMap.range (qIdemLin F τ)) (tauLin F τ)
      (range_qIdemLin_invariant F τ hτ2) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  refine Submodule.Quotient.induction_on _ x (fun y => ?_)
  simp only [Submodule.mapQ_apply, LinearMap.id_apply, Submodule.Quotient.eq]
  have hy : tauLin F τ y = y - (2 : F) • qIdemLin F τ y := by
    rw [tauLin_eq_one_sub_two_smul_qIdemLin]; rfl
  have hdiff : tauLin F τ y - y = -((2 : F) • qIdemLin F τ y) := by
    rw [hy]; abel
  rw [hdiff]
  exact Submodule.neg_mem _ (Submodule.smul_mem _ _ ⟨y, rfl⟩)

theorem tauLin_restrict_eq_neg_one (τ : Matrix (Fin 3) (Fin 3) F) (hτ2 : τ * τ = 1)
    (he : ∀ x ∈ LinearMap.range (qIdemLin F τ), tauLin F τ x ∈ LinearMap.range (qIdemLin F τ)) :
    (tauLin F τ).restrict he = -1 := by
  apply LinearMap.ext
  rintro ⟨x, y, rfl⟩
  apply Subtype.ext
  show tauLin F τ (qIdemLin F τ y) = -(qIdemLin F τ y)
  exact LinearMap.congr_fun (tauLin_mul_qIdemLin F τ hτ2) y

omit [Invertible (2 : F)] in
theorem det_neg_one_end_range_qIdemLin (τ : Matrix (Fin 3) (Fin 3) F) :
    LinearMap.det (-1 : Module.End F (LinearMap.range (qIdemLin F τ))) =
      (-1 : F) ^ Module.finrank F (LinearMap.range (qIdemLin F τ)) := by
  have hrw : (-1 : Module.End F (LinearMap.range (qIdemLin F τ))) =
      (-1 : F) • (1 : Module.End F (LinearMap.range (qIdemLin F τ))) :=
    (neg_one_smul F (1 : Module.End F (LinearMap.range (qIdemLin F τ)))).symm
  have hone : LinearMap.det (1 : Module.End F (LinearMap.range (qIdemLin F τ))) = 1 := by
    rw [show (1 : Module.End F (LinearMap.range (qIdemLin F τ))) = LinearMap.id from rfl,
      LinearMap.det_id]
  rw [hrw, LinearMap.det_smul, hone, mul_one]

theorem det_tauLin_eq (τ : Matrix (Fin 3) (Fin 3) F) (hτ2 : τ * τ = 1) :
    LinearMap.det (tauLin F τ) =
      (-1 : F) ^ Module.finrank F (LinearMap.range (qIdemLin F τ)) := by
  rw [LinearMap.det_eq_det_mul_det (LinearMap.range (qIdemLin F τ)) (tauLin F τ)
      (range_qIdemLin_invariant F τ hτ2),
    tauLin_restrict_eq_neg_one F τ hτ2, det_neg_one_end_range_qIdemLin,
    range_qIdemLin_mapQ_eq_id F τ hτ2, LinearMap.det_id, mul_one]

omit [Invertible (2 : F)] in
theorem toLinAlgEquiv'_eq_toLin' (M : Matrix (Fin 3) (Fin 3) F) :
    (Matrix.toLinAlgEquiv' M : Module.End F (Fin 3 → F)) = Matrix.toLin' M := by
  apply LinearMap.ext
  intro v
  rw [Matrix.toLinAlgEquiv'_apply, Matrix.toLin'_apply]

omit [Invertible (2 : F)] in
theorem det_tauLin_eq_det (τ : Matrix (Fin 3) (Fin 3) F) :
    LinearMap.det (tauLin F τ) = τ.det := by
  unfold tauLin
  rw [toLinAlgEquiv'_eq_toLin', LinearMap.det_toLin']

theorem finrank_range_qIdemLin_eq_two
    (τ : Matrix (Fin 3) (Fin 3) F) (hτ2 : τ * τ = 1) (hτ1 : τ ≠ 1) (hdet : τ.det = 1) :
    Module.finrank F (LinearMap.range (qIdemLin F τ)) = 2 := by
  have h1 := det_tauLin_eq F τ hτ2
  have h2 := det_tauLin_eq_det F τ
  rw [h2, hdet] at h1
  have hle : Module.finrank F (LinearMap.range (qIdemLin F τ)) ≤ 2 := by
    have hsum := finrank_range_pIdemLin_add_finrank_range_qIdemLin F τ hτ2
    have hpos := finrank_range_pIdemLin_pos F τ hdet
    omega
  have hpos := finrank_range_qIdemLin_pos F τ hτ1
  have hcases : Module.finrank F (LinearMap.range (qIdemLin F τ)) = 1 ∨
      Module.finrank F (LinearMap.range (qIdemLin F τ)) = 2 := by omega
  rcases hcases with h | h
  · rw [h] at h1
    simp at h1
    have step : (1 : F) + 1 = (-1 : F) + 1 := congrArg (· + 1) h1
    have lhs2 : (1 : F) + 1 = 2 := by ring
    have rhs0 : (-1 : F) + 1 = 0 := by ring
    rw [lhs2, rhs0] at step
    exact absurd step (Invertible.ne_zero (2 : F))
  · exact h

theorem finrank_range_pIdemLin_eq_one
    (τ : Matrix (Fin 3) (Fin 3) F) (hτ2 : τ * τ = 1) (hτ1 : τ ≠ 1) (hdet : τ.det = 1) :
    Module.finrank F (LinearMap.range (pIdemLin F τ)) = 1 := by
  have hsum := finrank_range_pIdemLin_add_finrank_range_qIdemLin F τ hτ2
  have h2 := finrank_range_qIdemLin_eq_two F τ hτ2 hτ1 hdet
  omega

omit [Invertible (2 : F)] in
/-! ### Specializing the generic `τ`-machinery to `τ1 = φ(d1)`, `τ2 = φ(d2)`, `τ3 = φ(d3)`

`tau1_mul_self`/`tau1_ne_one`/`tau1_ne_neg_one` (defined earlier, specific to `d1`)
already give the three hypotheses the generic lemmas need. `sl3_mul_self_matrix` and
`sl3_ne_one_matrix` lift the analogous group-level facts for `d2`, `d3` down to the
matrix level, so we get `finrank(range pIdemLin τᵢ) = 1` and `= 2` for the `-1`-side,
for all three `i = 1, 2, 3`, essentially for free. -/

omit [Invertible (2 : F)] in
theorem sl3_mul_self_matrix {A : SL3 F} (h : A * A = 1) :
    (A : Matrix (Fin 3) (Fin 3) F) * (A : Matrix (Fin 3) (Fin 3) F) = 1 := by
  have hcoe := congrArg (fun B : SL3 F => (B : Matrix (Fin 3) (Fin 3) F)) h
  simpa using hcoe

omit [Invertible (2 : F)] in
theorem sl3_ne_one_matrix {A : SL3 F} (h : A ≠ 1) :
    (A : Matrix (Fin 3) (Fin 3) F) ≠ 1 := by
  intro hc
  exact h (Subtype.ext (by simpa using hc))

omit [Invertible (2 : F)] in
theorem tau2_mul_self (φ : AutSL3 F) :
    (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F) * (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F) = 1 :=
  sl3_mul_self_matrix F (phi_d2_mul_self F φ)

omit [Invertible (2 : F)] in
theorem tau3_mul_self (φ : AutSL3 F) :
    (φ (d3SL F) : Matrix (Fin 3) (Fin 3) F) * (φ (d3SL F) : Matrix (Fin 3) (Fin 3) F) = 1 :=
  sl3_mul_self_matrix F (phi_d3_mul_self F φ)

theorem tau2_ne_one (φ : AutSL3 F) :
    (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F) ≠ 1 :=
  sl3_ne_one_matrix F (phi_d2_ne_one F φ)

theorem tau3_ne_one (φ : AutSL3 F) :
    (φ (d3SL F) : Matrix (Fin 3) (Fin 3) F) ≠ 1 :=
  sl3_ne_one_matrix F (phi_d3_ne_one F φ)

theorem finrank_range_pIdemLin_tau3_eq_one (φ : AutSL3 F) :
    Module.finrank F (LinearMap.range (pIdemLin F (φ (d3SL F) : Matrix (Fin 3) (Fin 3) F))) = 1 :=
  finrank_range_pIdemLin_eq_one F _ (tau3_mul_self F φ) (tau3_ne_one F φ)
    (Matrix.SpecialLinearGroup.det_coe (φ (d3SL F)))

theorem finrank_range_qIdemLin_tau3_eq_two (φ : AutSL3 F) :
    Module.finrank F (LinearMap.range (qIdemLin F (φ (d3SL F) : Matrix (Fin 3) (Fin 3) F))) = 2 :=
  finrank_range_qIdemLin_eq_two F _ (tau3_mul_self F φ) (tau3_ne_one F φ)
    (Matrix.SpecialLinearGroup.det_coe (φ (d3SL F)))


/-! ### `τ1` and `τ2` commute, hence preserve each other's eigenspaces

This is the part that lets us go beyond "`τ1` alone is diagonalizable": since
`φ(d1)` and `φ(d2)` commute, each of `range(pIdemLin τ1)`, `range(qIdemLin τ1)` is
invariant under `τ2` (and under `pIdemLin τ2`/`qIdemLin τ2` individually). -/

omit [Invertible (2 : F)] in
theorem tau1_mul_tau2_comm (φ : AutSL3 F) :
    (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F) * (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F) =
      (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F) * (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F) := by
  have h := phi_d1_d2_comm F φ
  have hcoe := congrArg (fun A : SL3 F => (A : Matrix (Fin 3) (Fin 3) F)) h
  simpa using hcoe

omit [Invertible (2 : F)] in
theorem pIdem_tau1_mul_tau2_comm (φ : AutSL3 F) :
    pIdem F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F) * (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F) =
      (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F) * pIdem F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F) := by
  unfold pIdem
  rw [Matrix.smul_mul, Matrix.mul_smul]
  congr 1
  rw [add_mul, mul_add, one_mul, mul_one, tau1_mul_tau2_comm]

omit [Invertible (2 : F)] in
theorem qIdem_tau1_mul_tau2_comm (φ : AutSL3 F) :
    qIdem F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F) * (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F) =
      (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F) * qIdem F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F) := by
  unfold qIdem
  rw [Matrix.smul_mul, Matrix.mul_smul]
  congr 1
  rw [sub_mul, mul_sub, one_mul, mul_one, tau1_mul_tau2_comm]

omit [Invertible (2 : F)] in
theorem pIdemLin_tau1_mul_tau2Lin_comm (φ : AutSL3 F) :
    pIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F) *
        tauLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F) =
      tauLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F) *
        pIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F) := by
  show pIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F) *
        tauLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F) =
      tauLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F) *
        pIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)
  unfold pIdemLin tauLin
  rw [← map_mul, ← map_mul, pIdem_tau1_mul_tau2_comm]

omit [Invertible (2 : F)] in
theorem qIdemLin_tau1_mul_tau2Lin_comm (φ : AutSL3 F) :
    qIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F) *
        tauLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F) =
      tauLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F) *
        qIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F) := by
  show qIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F) *
        tauLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F) =
      tauLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F) *
        qIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)
  unfold qIdemLin tauLin
  rw [← map_mul, ← map_mul, qIdem_tau1_mul_tau2_comm]

omit [Invertible (2 : F)] in
theorem range_pIdemLin_tau1_invariant_tau2 (φ : AutSL3 F) :
    ∀ x ∈ LinearMap.range (pIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)),
      tauLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F) x ∈
        LinearMap.range (pIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)) := by
  rintro x ⟨y, rfl⟩
  exact ⟨tauLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F) y,
    LinearMap.congr_fun (pIdemLin_tau1_mul_tau2Lin_comm F φ) y⟩

omit [Invertible (2 : F)] in
theorem range_qIdemLin_tau1_invariant_tau2 (φ : AutSL3 F) :
    ∀ x ∈ LinearMap.range (qIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)),
      tauLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F) x ∈
        LinearMap.range (qIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)) := by
  rintro x ⟨y, rfl⟩
  exact ⟨tauLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F) y,
    LinearMap.congr_fun (qIdemLin_tau1_mul_tau2Lin_comm F φ) y⟩


omit [Invertible (2 : F)] in
theorem pIdemLin_apply_eq (τ : Matrix (Fin 3) (Fin 3) F) (x : Fin 3 → F) :
    pIdemLin F τ x = (2 : F)⁻¹ • (x + tauLin F τ x) := by
  unfold pIdemLin pIdem tauLin
  rw [map_smul, map_add, Matrix.toLinAlgEquiv'_one]
  rfl

omit [Invertible (2 : F)] in
theorem qIdemLin_apply_eq (τ : Matrix (Fin 3) (Fin 3) F) (x : Fin 3 → F) :
    qIdemLin F τ x = (2 : F)⁻¹ • (x - tauLin F τ x) := by
  unfold qIdemLin qIdem tauLin
  rw [map_smul, map_sub, Matrix.toLinAlgEquiv'_one]
  rfl

omit [Invertible (2 : F)] in
theorem range_pIdemLin_tau1_invariant_pIdemLin_tau2 (φ : AutSL3 F) :
    ∀ x ∈ LinearMap.range (pIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)),
      pIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F) x ∈
        LinearMap.range (pIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)) := by
  intro x hx
  rw [pIdemLin_apply_eq]
  exact Submodule.smul_mem _ _ (Submodule.add_mem _ hx
    (range_pIdemLin_tau1_invariant_tau2 F φ x hx))

omit [Invertible (2 : F)] in
theorem range_pIdemLin_tau1_invariant_qIdemLin_tau2 (φ : AutSL3 F) :
    ∀ x ∈ LinearMap.range (pIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)),
      qIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F) x ∈
        LinearMap.range (pIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)) := by
  intro x hx
  rw [qIdemLin_apply_eq]
  exact Submodule.smul_mem _ _ (Submodule.sub_mem _ hx
    (range_pIdemLin_tau1_invariant_tau2 F φ x hx))

theorem range_pIdemLin_tau1_le_sup (φ : AutSL3 F) :
    LinearMap.range (pIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)) ≤
      (LinearMap.range (pIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)) ⊓
          LinearMap.range (pIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F))) ⊔
        (LinearMap.range (pIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)) ⊓
          LinearMap.range (qIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F))) := by
  intro x hx
  have hsum : pIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F) x +
      qIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F) x = x :=
    LinearMap.congr_fun (pIdemLin_add_qIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F)) x
  have h1 : pIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F) x ∈
      LinearMap.range (pIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)) ⊓
        LinearMap.range (pIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F)) :=
    ⟨range_pIdemLin_tau1_invariant_pIdemLin_tau2 F φ x hx, ⟨x, rfl⟩⟩
  have h2 : qIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F) x ∈
      LinearMap.range (pIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)) ⊓
        LinearMap.range (qIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F)) :=
    ⟨range_pIdemLin_tau1_invariant_qIdemLin_tau2 F φ x hx, ⟨x, rfl⟩⟩
  rw [← hsum]
  exact Submodule.add_mem_sup h1 h2

omit [Invertible (2 : F)] in
theorem tau1_mul_tau2_eq_tau3 (φ : AutSL3 F) :
    (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F) * (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F) =
      (φ (d3SL F) : Matrix (Fin 3) (Fin 3) F) := by
  have h := phi_d1_d2_eq_d3 F φ
  have hcoe := congrArg (fun A : SL3 F => (A : Matrix (Fin 3) (Fin 3) F)) h
  simpa using hcoe

omit [Invertible (2 : F)] in
theorem tauLin_tau3_eq_mul (φ : AutSL3 F) :
    tauLin F (φ (d3SL F) : Matrix (Fin 3) (Fin 3) F) =
      tauLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F) *
        tauLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F) := by
  unfold tauLin
  rw [← map_mul, tau1_mul_tau2_eq_tau3]

omit [Invertible (2 : F)] in
theorem qIdemLin_mul_pIdemLin (τ : Matrix (Fin 3) (Fin 3) F) (hτ2 : τ * τ = 1) :
    qIdemLin F τ * pIdemLin F τ = 0 := by
  show qIdemLin F τ * pIdemLin F τ = 0
  unfold qIdemLin pIdemLin
  rw [← map_mul, qIdem_mul_pIdem F τ hτ2, map_zero]

theorem tauLin_mul_pIdemLin (τ : Matrix (Fin 3) (Fin 3) F) (hτ2 : τ * τ = 1) :
    tauLin F τ * pIdemLin F τ = pIdemLin F τ := by
  rw [← pIdemLin_sub_qIdemLin, sub_mul, pIdemLin_idem F τ hτ2, qIdemLin_mul_pIdemLin F τ hτ2,
    sub_zero]

theorem mem_range_pIdemLin_iff_eigen (τ : Matrix (Fin 3) (Fin 3) F) (hτ2 : τ * τ = 1) (v : Fin 3 → F) :
    v ∈ LinearMap.range (pIdemLin F τ) → tauLin F τ v = v := by
  rintro ⟨y, rfl⟩
  exact LinearMap.congr_fun (tauLin_mul_pIdemLin F τ hτ2) y

theorem mem_range_qIdemLin_iff_eigen (τ : Matrix (Fin 3) (Fin 3) F) (hτ2 : τ * τ = 1) (v : Fin 3 → F) :
    v ∈ LinearMap.range (qIdemLin F τ) → tauLin F τ v = -v := by
  rintro ⟨y, rfl⟩
  exact LinearMap.congr_fun (tauLin_mul_qIdemLin F τ hτ2) y

/-! ### Pinning down all four pairwise intersections via `τ3 = τ1 τ2`

We want `range(pIdemLin τ1) ⊓ range(pIdemLin τ2) = 0`, and the other three pairwise
intersections to each be 1-dimensional (these are exactly the lines spanned by
`v1, v2, v3` below). Redoing the idempotent argument *inside* a 2-dimensional
subspace would need the whole machinery above generalized to an arbitrary subspace.
Instead, we use `τ3 = τ1 τ2`, whose own `±1`-eigenspaces we already know the
dimensions of (1 and 2, from the previous section) as a referee: every pairwise
intersection embeds into a `±1`-eigenspace of `τ3`, which bounds its dimension, and a
short linear system on the four dimensions (`a+b=1`, `c+d=2`, `d≤1`, ...) pins each
one down exactly, without ever touching a genuine subspace-of-a-subspace argument. -/

theorem inf_q1_q2_le_p3 (φ : AutSL3 F) :
    LinearMap.range (qIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)) ⊓
        LinearMap.range (qIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F)) ≤
      LinearMap.range (pIdemLin F (φ (d3SL F) : Matrix (Fin 3) (Fin 3) F)) := by
  intro v hv
  have h1 : tauLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F) v = -v :=
    mem_range_qIdemLin_iff_eigen F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F) (tau1_mul_self F φ) v hv.1
  have h2 : tauLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F) v = -v :=
    mem_range_qIdemLin_iff_eigen F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F) (tau2_mul_self F φ) v hv.2
  have h3 : tauLin F (φ (d3SL F) : Matrix (Fin 3) (Fin 3) F) v = v := by
    rw [tauLin_tau3_eq_mul]
    show tauLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)
      (tauLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F) v) = v
    rw [h2, map_neg, h1, neg_neg]
  refine ⟨v, ?_⟩
  rw [pIdemLin_apply_eq, h3]
  rw [show v + v = (2 : F) • v from (two_smul F v).symm, smul_smul,
    inv_mul_cancel₀ (Invertible.ne_zero (2 : F)), one_smul]

omit [Invertible (2 : F)] in
theorem range_qIdemLin_tau1_invariant_pIdemLin_tau2 (φ : AutSL3 F) :
    ∀ x ∈ LinearMap.range (qIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)),
      pIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F) x ∈
        LinearMap.range (qIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)) := by
  intro x hx
  rw [pIdemLin_apply_eq]
  exact Submodule.smul_mem _ _ (Submodule.add_mem _ hx
    (range_qIdemLin_tau1_invariant_tau2 F φ x hx))

omit [Invertible (2 : F)] in
theorem range_qIdemLin_tau1_invariant_qIdemLin_tau2 (φ : AutSL3 F) :
    ∀ x ∈ LinearMap.range (qIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)),
      qIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F) x ∈
        LinearMap.range (qIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)) := by
  intro x hx
  rw [qIdemLin_apply_eq]
  exact Submodule.smul_mem _ _ (Submodule.sub_mem _ hx
    (range_qIdemLin_tau1_invariant_tau2 F φ x hx))

theorem range_qIdemLin_tau1_le_sup (φ : AutSL3 F) :
    LinearMap.range (qIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)) ≤
      (LinearMap.range (qIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)) ⊓
          LinearMap.range (pIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F))) ⊔
        (LinearMap.range (qIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)) ⊓
          LinearMap.range (qIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F))) := by
  intro x hx
  have hsum : pIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F) x +
      qIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F) x = x :=
    LinearMap.congr_fun (pIdemLin_add_qIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F)) x
  have h1 : pIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F) x ∈
      LinearMap.range (qIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)) ⊓
        LinearMap.range (pIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F)) :=
    ⟨range_qIdemLin_tau1_invariant_pIdemLin_tau2 F φ x hx, ⟨x, rfl⟩⟩
  have h2 : qIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F) x ∈
      LinearMap.range (qIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)) ⊓
        LinearMap.range (qIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F)) :=
    ⟨range_qIdemLin_tau1_invariant_qIdemLin_tau2 F φ x hx, ⟨x, rfl⟩⟩
  rw [← hsum]
  exact Submodule.add_mem_sup h1 h2

theorem finrank_inf_add_finrank_inf_p1 (φ : AutSL3 F) :
    Module.finrank F ↥(LinearMap.range (pIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)) ⊓
        LinearMap.range (pIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F))) +
      Module.finrank F ↥(LinearMap.range (pIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)) ⊓
        LinearMap.range (qIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F))) = 1 := by
  have hsup : (LinearMap.range (pIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)) ⊓
        LinearMap.range (pIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F))) ⊔
      (LinearMap.range (pIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)) ⊓
        LinearMap.range (qIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F))) =
      LinearMap.range (pIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)) := by
    apply le_antisymm
    · exact sup_le inf_le_left inf_le_left
    · exact range_pIdemLin_tau1_le_sup F φ
  have hdisj : Disjoint
      (LinearMap.range (pIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)) ⊓
        LinearMap.range (pIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F)))
      (LinearMap.range (pIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)) ⊓
        LinearMap.range (qIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F))) := by
    apply Disjoint.mono inf_le_right inf_le_right
    exact (isCompl_range_pIdemLin_range_qIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F)
      (tau2_mul_self F φ)).disjoint
  have h := Submodule.finrank_sup_add_finrank_inf_eq
    (LinearMap.range (pIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)) ⊓
      LinearMap.range (pIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F)))
    (LinearMap.range (pIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)) ⊓
      LinearMap.range (qIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F)))
  have hP1 := finrank_range_pIdemLin_eq_one F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)
    (tau1_mul_self F φ) (tau1_ne_one F φ) (Matrix.SpecialLinearGroup.det_coe (φ (d1SL F)))
  rw [hsup, hdisj.eq_bot, finrank_bot, hP1] at h
  omega

theorem finrank_inf_add_finrank_inf_q1 (φ : AutSL3 F) :
    Module.finrank F ↥(LinearMap.range (qIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)) ⊓
        LinearMap.range (pIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F))) +
      Module.finrank F ↥(LinearMap.range (qIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)) ⊓
        LinearMap.range (qIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F))) = 2 := by
  have hsup : (LinearMap.range (qIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)) ⊓
        LinearMap.range (pIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F))) ⊔
      (LinearMap.range (qIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)) ⊓
        LinearMap.range (qIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F))) =
      LinearMap.range (qIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)) := by
    apply le_antisymm
    · exact sup_le inf_le_left inf_le_left
    · exact range_qIdemLin_tau1_le_sup F φ
  have hdisj : Disjoint
      (LinearMap.range (qIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)) ⊓
        LinearMap.range (pIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F)))
      (LinearMap.range (qIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)) ⊓
        LinearMap.range (qIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F))) := by
    apply Disjoint.mono inf_le_right inf_le_right
    exact (isCompl_range_pIdemLin_range_qIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F)
      (tau2_mul_self F φ)).disjoint
  have h := Submodule.finrank_sup_add_finrank_inf_eq
    (LinearMap.range (qIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)) ⊓
      LinearMap.range (pIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F)))
    (LinearMap.range (qIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)) ⊓
      LinearMap.range (qIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F)))
  have hQ1 := finrank_range_qIdemLin_eq_two F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)
    (tau1_mul_self F φ) (tau1_ne_one F φ) (Matrix.SpecialLinearGroup.det_coe (φ (d1SL F)))
  rw [hsup, hdisj.eq_bot, finrank_bot, hQ1] at h
  omega

theorem finrank_inf_q1_q2_le_one (φ : AutSL3 F) :
    Module.finrank F ↥(LinearMap.range (qIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)) ⊓
        LinearMap.range (qIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F))) ≤ 1 := by
  have h := Submodule.finrank_mono (inf_q1_q2_le_p3 F φ)
  rwa [finrank_range_pIdemLin_eq_one F (φ (d3SL F) : Matrix (Fin 3) (Fin 3) F)
    (tau3_mul_self F φ) (tau3_ne_one F φ) (Matrix.SpecialLinearGroup.det_coe (φ (d3SL F)))] at h

theorem finrank_inf_q1_p2_le_one (φ : AutSL3 F) :
    Module.finrank F ↥(LinearMap.range (qIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)) ⊓
        LinearMap.range (pIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F))) ≤ 1 := by
  have h := Submodule.finrank_mono (inf_le_right :
    LinearMap.range (qIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)) ⊓
        LinearMap.range (pIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F)) ≤
      LinearMap.range (pIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F)))
  rwa [finrank_range_pIdemLin_eq_one F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F)
    (tau2_mul_self F φ) (tau2_ne_one F φ) (Matrix.SpecialLinearGroup.det_coe (φ (d2SL F)))] at h

theorem finrank_inf_q1_p2_eq_one (φ : AutSL3 F) :
    Module.finrank F ↥(LinearMap.range (qIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)) ⊓
        LinearMap.range (pIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F))) = 1 := by
  have hsum := finrank_inf_add_finrank_inf_q1 F φ
  have hle1 := finrank_inf_q1_p2_le_one F φ
  have hle2 := finrank_inf_q1_q2_le_one F φ
  omega

theorem finrank_inf_q1_q2_eq_one (φ : AutSL3 F) :
    Module.finrank F ↥(LinearMap.range (qIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)) ⊓
        LinearMap.range (qIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F))) = 1 := by
  have hsum := finrank_inf_add_finrank_inf_q1 F φ
  have hc := finrank_inf_q1_p2_eq_one F φ
  omega

theorem range_qIdemLin_inf_pIdemLin_eq_p2 (φ : AutSL3 F) :
    LinearMap.range (qIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)) ⊓
        LinearMap.range (pIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F)) =
      LinearMap.range (pIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F)) := by
  apply Submodule.eq_of_le_of_finrank_eq inf_le_right
  rw [finrank_inf_q1_p2_eq_one F φ,
    finrank_range_pIdemLin_eq_one F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F)
      (tau2_mul_self F φ) (tau2_ne_one F φ) (Matrix.SpecialLinearGroup.det_coe (φ (d2SL F)))]

theorem range_pIdemLin_inf_pIdemLin_eq_bot (φ : AutSL3 F) :
    LinearMap.range (pIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)) ⊓
        LinearMap.range (pIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F)) = ⊥ := by
  have hP2_eq : LinearMap.range (pIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F)) =
      LinearMap.range (qIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)) ⊓
        LinearMap.range (pIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F)) :=
    (range_qIdemLin_inf_pIdemLin_eq_p2 F φ).symm
  rw [hP2_eq, ← inf_assoc]
  have hbot : LinearMap.range (pIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)) ⊓
      LinearMap.range (qIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)) = ⊥ :=
    (isCompl_range_pIdemLin_range_qIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)
      (tau1_mul_self F φ)).disjoint.eq_bot
  rw [hbot, bot_inf_eq]

theorem finrank_inf_p1_p2_eq_zero (φ : AutSL3 F) :
    Module.finrank F ↥(LinearMap.range (pIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)) ⊓
        LinearMap.range (pIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F))) = 0 := by
  rw [range_pIdemLin_inf_pIdemLin_eq_bot F φ, finrank_bot]

theorem finrank_inf_p1_q2_eq_one (φ : AutSL3 F) :
    Module.finrank F ↥(LinearMap.range (pIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)) ⊓
        LinearMap.range (qIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F))) = 1 := by
  have hsum := finrank_inf_add_finrank_inf_p1 F φ
  have ha := finrank_inf_p1_p2_eq_zero F φ
  omega

theorem inf_p1_q2_ne_bot (φ : AutSL3 F) :
    LinearMap.range (pIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)) ⊓
        LinearMap.range (qIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F)) ≠ ⊥ := by
  intro h
  have h1 := finrank_inf_p1_q2_eq_one F φ
  rw [h, finrank_bot] at h1
  exact absurd h1 (by norm_num)

theorem inf_q1_p2_ne_bot (φ : AutSL3 F) :
    LinearMap.range (qIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)) ⊓
        LinearMap.range (pIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F)) ≠ ⊥ := by
  intro h
  have h1 := finrank_inf_q1_p2_eq_one F φ
  rw [h, finrank_bot] at h1
  exact absurd h1 (by norm_num)

theorem inf_q1_q2_ne_bot (φ : AutSL3 F) :
    LinearMap.range (qIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)) ⊓
        LinearMap.range (qIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F)) ≠ ⊥ := by
  intro h
  have h1 := finrank_inf_q1_q2_eq_one F φ
  rw [h, finrank_bot] at h1
  exact absurd h1 (by norm_num)

/-! ### Extracting basis vectors `v1, v2, v3` and checking they are independent

`v1` spans `P1 ⊓ Q2` (`τ1 = +1`, `τ2 = -1`), `v2` spans `Q1 ⊓ P2`, `v3` spans `Q1 ⊓ Q2` —
each is exactly 1-dimensional by the previous section, hence nonzero and unique up to
scalar. `linearIndependent_v1_v2_v3` checks that any vanishing combination of the three
forces all three coefficients to vanish (using that `τ1`, `τ2` act by different sign
patterns on each `vᵢ`). -/

theorem exists_v1 (φ : AutSL3 F) :
    ∃ v : Fin 3 → F, v ∈ LinearMap.range (pIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)) ⊓
        LinearMap.range (qIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F)) ∧ v ≠ 0 :=
  Submodule.exists_mem_ne_zero_of_ne_bot (inf_p1_q2_ne_bot F φ)

theorem exists_v2 (φ : AutSL3 F) :
    ∃ v : Fin 3 → F, v ∈ LinearMap.range (qIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)) ⊓
        LinearMap.range (pIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F)) ∧ v ≠ 0 :=
  Submodule.exists_mem_ne_zero_of_ne_bot (inf_q1_p2_ne_bot F φ)

theorem exists_v3 (φ : AutSL3 F) :
    ∃ v : Fin 3 → F, v ∈ LinearMap.range (qIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)) ⊓
        LinearMap.range (qIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F)) ∧ v ≠ 0 :=
  Submodule.exists_mem_ne_zero_of_ne_bot (inf_q1_q2_ne_bot F φ)

theorem linearIndependent_v1_v2_v3 (φ : AutSL3 F)
    {v1 v2 v3 : Fin 3 → F}
    (hv1 : v1 ∈ LinearMap.range (pIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)) ⊓
        LinearMap.range (qIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F)))
    (hv2 : v2 ∈ LinearMap.range (qIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)) ⊓
        LinearMap.range (pIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F)))
    (hv3 : v3 ∈ LinearMap.range (qIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)) ⊓
        LinearMap.range (qIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F)))
    (hv1' : v1 ≠ 0) (hv2' : v2 ≠ 0) (hv3' : v3 ≠ 0)
    (a b c : F) (h : a • v1 + b • v2 + c • v3 = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 := by
  have e1_1 : tauLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F) v1 = v1 :=
    mem_range_pIdemLin_iff_eigen F _ (tau1_mul_self F φ) v1 hv1.1
  have e1_2 : tauLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F) v1 = -v1 :=
    mem_range_qIdemLin_iff_eigen F _ (tau2_mul_self F φ) v1 hv1.2
  have e2_1 : tauLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F) v2 = -v2 :=
    mem_range_qIdemLin_iff_eigen F _ (tau1_mul_self F φ) v2 hv2.1
  have e2_2 : tauLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F) v2 = v2 :=
    mem_range_pIdemLin_iff_eigen F _ (tau2_mul_self F φ) v2 hv2.2
  have e3_1 : tauLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F) v3 = -v3 :=
    mem_range_qIdemLin_iff_eigen F _ (tau1_mul_self F φ) v3 hv3.1
  have e3_2 : tauLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F) v3 = -v3 :=
    mem_range_qIdemLin_iff_eigen F _ (tau2_mul_self F φ) v3 hv3.2
  have h1 : a • v1 + -(b • v2) + -(c • v3) = 0 := by
    have hh := congrArg (tauLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)) h
    rw [map_zero, map_add, map_add, map_smul, map_smul, map_smul, e1_1, e2_1, e3_1,
      smul_neg, smul_neg] at hh
    exact hh
  have hadd : a • v1 + a • v1 = 0 := by
    have heq : (a • v1 + b • v2 + c • v3) + (a • v1 + -(b • v2) + -(c • v3)) =
        a • v1 + a • v1 := by abel
    rw [h, h1] at heq
    simpa using heq.symm
  have ha : a = 0 := by
    have h2 : (2 : F) • (a • v1) = 0 := by rw [two_smul]; exact hadd
    rw [smul_smul] at h2
    rcases smul_eq_zero.mp h2 with h2a | hv
    · rcases mul_eq_zero.mp h2a with h20 | ha0
      · exact absurd h20 (Invertible.ne_zero (2 : F))
      · exact ha0
    · exact absurd hv hv1'
  have hbc : b • v2 + c • v3 = 0 := by
    rw [ha] at h
    simpa using h
  have h2 : b • v2 + -(c • v3) = 0 := by
    have hh := congrArg (tauLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F)) hbc
    rw [map_zero, map_add, map_smul, map_smul, e2_2, e3_2, smul_neg] at hh
    exact hh
  have hbadd : b • v2 + b • v2 = 0 := by
    have heq : (b • v2 + c • v3) + (b • v2 + -(c • v3)) = b • v2 + b • v2 := by abel
    rw [hbc, h2] at heq
    simpa using heq.symm
  have hb : b = 0 := by
    have h2' : (2 : F) • (b • v2) = 0 := by rw [two_smul]; exact hbadd
    rw [smul_smul] at h2'
    rcases smul_eq_zero.mp h2' with h2b | hv
    · rcases mul_eq_zero.mp h2b with h20 | hb0
      · exact absurd h20 (Invertible.ne_zero (2 : F))
      · exact hb0
    · exact absurd hv hv2'
  have hc : c = 0 := by
    rw [hb] at hbc
    simp only [zero_smul, zero_add] at hbc
    rcases smul_eq_zero.mp hbc with hc0 | hv
    · exact hc0
    · exact absurd hv hv3'
  exact ⟨ha, hb, hc⟩

theorem linearIndependent_fin3 (φ : AutSL3 F)
    (v1 v2 v3 : Fin 3 → F)
    (hv1 : v1 ∈ LinearMap.range (pIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)) ⊓
        LinearMap.range (qIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F)))
    (hv2 : v2 ∈ LinearMap.range (qIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)) ⊓
        LinearMap.range (pIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F)))
    (hv3 : v3 ∈ LinearMap.range (qIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)) ⊓
        LinearMap.range (qIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F)))
    (hv1' : v1 ≠ 0) (hv2' : v2 ≠ 0) (hv3' : v3 ≠ 0) :
    LinearIndependent F ![v1, v2, v3] := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have key := linearIndependent_v1_v2_v3 F φ hv1 hv2 hv3 hv1' hv2' hv3' (g 0) (g 1) (g 2) (by
    have : ∑ j : Fin 3, g j • (![v1, v2, v3] j) = g 0 • v1 + g 1 • v2 + g 2 • v3 := by
      simp [Fin.sum_univ_three]
    rw [← this]; exact hg)
  fin_cases i
  · exact key.1
  · exact key.2.1
  · exact key.2.2

noncomputable def basisV123 (φ : AutSL3 F)
    (v1 v2 v3 : Fin 3 → F)
    (hv1 : v1 ∈ LinearMap.range (pIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)) ⊓
        LinearMap.range (qIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F)))
    (hv2 : v2 ∈ LinearMap.range (qIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)) ⊓
        LinearMap.range (pIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F)))
    (hv3 : v3 ∈ LinearMap.range (qIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)) ⊓
        LinearMap.range (qIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F)))
    (hv1' : v1 ≠ 0) (hv2' : v2 ≠ 0) (hv3' : v3 ≠ 0) :
    Module.Basis (Fin 3) F (Fin 3 → F) :=
  basisOfLinearIndependentOfCardEqFinrank
    (linearIndependent_fin3 F φ v1 v2 v3 hv1 hv2 hv3 hv1' hv2' hv3')
    (by simp)

/-! ### Building the change-of-basis matrix `g`

`gMatrix v1 v2 v3` is the matrix whose columns are `v1, v2, v3`. We check it sends the
standard basis vectors to `v1, v2, v3` (`gMatrix_mulVec_e1/e2/e3`), that it is injective
(hence invertible, via `linearIndependent_v1_v2_v3`), and finally that
`τᵢ · g = g · dᵢ` for `i = 1, 2, 3` by comparing both sides column by column
(`tau1_mul_gMatrix_eq`, `tau2_mul_gMatrix_eq`, and `g_inv_mul_tau3_mul_g` via
`τ3 = τ1 τ2`, `d3 = d1 d2`). -/

noncomputable def gMatrix (v1 v2 v3 : Fin 3 → F) : Matrix (Fin 3) (Fin 3) F :=
  fun i j => ![v1, v2, v3] j i

omit [Invertible (2 : F)] in
theorem gMatrix_mulVec_e1 (v1 v2 v3 : Fin 3 → F) :
    (gMatrix F v1 v2 v3).mulVec (e1 F) = v1 := by
  ext i
  simp [gMatrix, Matrix.mulVec, e1]

omit [Invertible (2 : F)] in
theorem gMatrix_mulVec_e2 (v1 v2 v3 : Fin 3 → F) :
    (gMatrix F v1 v2 v3).mulVec (e2 F) = v2 := by
  ext i
  simp [gMatrix, Matrix.mulVec, e2]

omit [Invertible (2 : F)] in
theorem gMatrix_mulVec_e3 (v1 v2 v3 : Fin 3 → F) :
    (gMatrix F v1 v2 v3).mulVec (e3 F) = v3 := by
  ext i
  simp [gMatrix, Matrix.mulVec, e3]


omit [Invertible (2 : F)] in
theorem gMatrix_mulVec_general (v1 v2 v3 : Fin 3 → F) (x : Fin 3 → F) :
    (gMatrix F v1 v2 v3).mulVec x = x 0 • v1 + x 1 • v2 + x 2 • v3 := by
  funext i
  show ∑ j, gMatrix F v1 v2 v3 i j * x j = (x 0 • v1 + x 1 • v2 + x 2 • v3) i
  rw [Fin.sum_univ_three]
  simp [gMatrix]
  ring

theorem gMatrix_injective (φ : AutSL3 F)
    (v1 v2 v3 : Fin 3 → F)
    (hv1 : v1 ∈ LinearMap.range (pIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)) ⊓
        LinearMap.range (qIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F)))
    (hv2 : v2 ∈ LinearMap.range (qIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)) ⊓
        LinearMap.range (pIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F)))
    (hv3 : v3 ∈ LinearMap.range (qIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)) ⊓
        LinearMap.range (qIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F)))
    (hv1' : v1 ≠ 0) (hv2' : v2 ≠ 0) (hv3' : v3 ≠ 0) :
    Function.Injective (gMatrix F v1 v2 v3).mulVec := by
  intro x y hxy
  rw [gMatrix_mulVec_general, gMatrix_mulVec_general] at hxy
  have heq : (x 0 - y 0) • v1 + (x 1 - y 1) • v2 + (x 2 - y 2) • v3 = 0 := by
    rw [sub_smul, sub_smul, sub_smul]
    rw [show x 0 • v1 - y 0 • v1 + (x 1 • v2 - y 1 • v2) + (x 2 • v3 - y 2 • v3) =
      (x 0 • v1 + x 1 • v2 + x 2 • v3) - (y 0 • v1 + y 1 • v2 + y 2 • v3) from by abel]
    rw [hxy, sub_self]
  have key := linearIndependent_v1_v2_v3 F φ hv1 hv2 hv3 hv1' hv2' hv3'
    (x 0 - y 0) (x 1 - y 1) (x 2 - y 2) heq
  funext j
  fin_cases j
  · exact sub_eq_zero.mp key.1
  · exact sub_eq_zero.mp key.2.1
  · exact sub_eq_zero.mp key.2.2

omit [Invertible (2 : F)] in
theorem gMatrix_det_ne_zero (v1 v2 v3 : Fin 3 → F)
    (hinj : Function.Injective (gMatrix F v1 v2 v3).mulVec) :
    (gMatrix F v1 v2 v3).det ≠ 0 := by
  intro hdet
  obtain ⟨v, hv_ne, hv_zero⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  apply hv_ne
  have h0 : (gMatrix F v1 v2 v3).mulVec 0 = 0 := Matrix.mulVec_zero _
  exact hinj (hv_zero.trans h0.symm)

omit [Invertible (2 : F)] in
theorem gMatrix_isUnit (v1 v2 v3 : Fin 3 → F)
    (hinj : Function.Injective (gMatrix F v1 v2 v3).mulVec) :
    IsUnit (gMatrix F v1 v2 v3) :=
  (Matrix.isUnit_iff_isUnit_det _).mpr (Ne.isUnit (gMatrix_det_ne_zero F v1 v2 v3 hinj))

omit [Invertible (2 : F)] in
theorem tauLin_apply_eq_mulVec (τ : Matrix (Fin 3) (Fin 3) F) (x : Fin 3 → F) :
    tauLin F τ x = τ.mulVec x := by
  unfold tauLin
  rw [Matrix.toLinAlgEquiv'_apply]

omit [Invertible (2 : F)] in
theorem d1_mulVec_e1 : (d1 F).mulVec (e1 F) = e1 F := by
  funext i
  show ∑ j, (d1 F) i j * (e1 F) j = (e1 F) i
  rw [Fin.sum_univ_three]
  fin_cases i <;> simp [d1, e1, Matrix.diagonal]

omit [Invertible (2 : F)] in
theorem d1_mulVec_e2 : (d1 F).mulVec (e2 F) = -(e2 F) := by
  funext i
  show ∑ j, (d1 F) i j * (e2 F) j = -(e2 F) i
  rw [Fin.sum_univ_three]
  fin_cases i <;> simp [d1, e2, Matrix.diagonal]

omit [Invertible (2 : F)] in
theorem d1_mulVec_e3 : (d1 F).mulVec (e3 F) = -(e3 F) := by
  funext i
  show ∑ j, (d1 F) i j * (e3 F) j = -(e3 F) i
  rw [Fin.sum_univ_three]
  fin_cases i <;> simp [d1, e3, Matrix.diagonal]

omit [Invertible (2 : F)] in
theorem d2_mulVec_e1 : (d2 F).mulVec (e1 F) = -(e1 F) := by
  funext i
  show ∑ j, (d2 F) i j * (e1 F) j = -(e1 F) i
  rw [Fin.sum_univ_three]
  fin_cases i <;> simp [d2, e1, Matrix.diagonal]

omit [Invertible (2 : F)] in
theorem d2_mulVec_e2 : (d2 F).mulVec (e2 F) = e2 F := by
  funext i
  show ∑ j, (d2 F) i j * (e2 F) j = (e2 F) i
  rw [Fin.sum_univ_three]
  fin_cases i <;> simp [d2, e2, Matrix.diagonal]

omit [Invertible (2 : F)] in
theorem d2_mulVec_e3 : (d2 F).mulVec (e3 F) = -(e3 F) := by
  funext i
  show ∑ j, (d2 F) i j * (e3 F) j = -(e3 F) i
  rw [Fin.sum_univ_three]
  fin_cases i <;> simp [d2, e3, Matrix.diagonal]

omit [Invertible (2 : F)] in
theorem mulVec_e1_eq_col0 (M : Matrix (Fin 3) (Fin 3) F) :
    M.mulVec (e1 F) = fun i => M i 0 := by
  funext i
  show ∑ j, M i j * (e1 F) j = M i 0
  rw [Fin.sum_univ_three]
  simp [e1]

omit [Invertible (2 : F)] in
theorem mulVec_e2_eq_col1 (M : Matrix (Fin 3) (Fin 3) F) :
    M.mulVec (e2 F) = fun i => M i 1 := by
  funext i
  show ∑ j, M i j * (e2 F) j = M i 1
  rw [Fin.sum_univ_three]
  simp [e2]

omit [Invertible (2 : F)] in
theorem mulVec_e3_eq_col2 (M : Matrix (Fin 3) (Fin 3) F) :
    M.mulVec (e3 F) = fun i => M i 2 := by
  funext i
  show ∑ j, M i j * (e3 F) j = M i 2
  rw [Fin.sum_univ_three]
  simp [e3]

omit [Invertible (2 : F)] in
theorem matrix_ext_of_mulVec_e (M N : Matrix (Fin 3) (Fin 3) F)
    (h1 : M.mulVec (e1 F) = N.mulVec (e1 F))
    (h2 : M.mulVec (e2 F) = N.mulVec (e2 F))
    (h3 : M.mulVec (e3 F) = N.mulVec (e3 F)) : M = N := by
  rw [mulVec_e1_eq_col0, mulVec_e1_eq_col0] at h1
  rw [mulVec_e2_eq_col1, mulVec_e2_eq_col1] at h2
  rw [mulVec_e3_eq_col2, mulVec_e3_eq_col2] at h3
  ext i j
  fin_cases j
  · exact congrFun h1 i
  · exact congrFun h2 i
  · exact congrFun h3 i

theorem tau1_mul_gMatrix_eq (φ : AutSL3 F)
    (v1 v2 v3 : Fin 3 → F)
    (hv1 : v1 ∈ LinearMap.range (pIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)) ⊓
        LinearMap.range (qIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F)))
    (hv2 : v2 ∈ LinearMap.range (qIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)) ⊓
        LinearMap.range (pIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F)))
    (hv3 : v3 ∈ LinearMap.range (qIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)) ⊓
        LinearMap.range (qIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F))) :
    (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F) * gMatrix F v1 v2 v3 =
      gMatrix F v1 v2 v3 * d1 F := by
  apply matrix_ext_of_mulVec_e
  · rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, d1_mulVec_e1, gMatrix_mulVec_e1,
      ← tauLin_apply_eq_mulVec]
    exact mem_range_pIdemLin_iff_eigen F _ (tau1_mul_self F φ) v1 hv1.1
  · rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, d1_mulVec_e2, Matrix.mulVec_neg,
      gMatrix_mulVec_e2, ← tauLin_apply_eq_mulVec]
    exact mem_range_qIdemLin_iff_eigen F _ (tau1_mul_self F φ) v2 hv2.1
  · rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, d1_mulVec_e3, Matrix.mulVec_neg,
      gMatrix_mulVec_e3, ← tauLin_apply_eq_mulVec]
    exact mem_range_qIdemLin_iff_eigen F _ (tau1_mul_self F φ) v3 hv3.1

theorem tau2_mul_gMatrix_eq (φ : AutSL3 F)
    (v1 v2 v3 : Fin 3 → F)
    (hv1 : v1 ∈ LinearMap.range (pIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)) ⊓
        LinearMap.range (qIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F)))
    (hv2 : v2 ∈ LinearMap.range (qIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)) ⊓
        LinearMap.range (pIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F)))
    (hv3 : v3 ∈ LinearMap.range (qIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)) ⊓
        LinearMap.range (qIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F))) :
    (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F) * gMatrix F v1 v2 v3 =
      gMatrix F v1 v2 v3 * d2 F := by
  apply matrix_ext_of_mulVec_e
  · rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, d2_mulVec_e1, Matrix.mulVec_neg,
      gMatrix_mulVec_e1, ← tauLin_apply_eq_mulVec]
    exact mem_range_qIdemLin_iff_eigen F _ (tau2_mul_self F φ) v1 hv1.2
  · rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, d2_mulVec_e2, gMatrix_mulVec_e2,
      ← tauLin_apply_eq_mulVec]
    exact mem_range_pIdemLin_iff_eigen F _ (tau2_mul_self F φ) v2 hv2.2
  · rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, d2_mulVec_e3, Matrix.mulVec_neg,
      gMatrix_mulVec_e3, ← tauLin_apply_eq_mulVec]
    exact mem_range_qIdemLin_iff_eigen F _ (tau2_mul_self F φ) v3 hv3.2

theorem g_inv_mul_tau1_mul_g (φ : AutSL3 F)
    (v1 v2 v3 : Fin 3 → F)
    (hv1 : v1 ∈ LinearMap.range (pIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)) ⊓
        LinearMap.range (qIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F)))
    (hv2 : v2 ∈ LinearMap.range (qIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)) ⊓
        LinearMap.range (pIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F)))
    (hv3 : v3 ∈ LinearMap.range (qIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)) ⊓
        LinearMap.range (qIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F)))
    (hinj : Function.Injective (gMatrix F v1 v2 v3).mulVec) :
    (gMatrix F v1 v2 v3)⁻¹ * (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F) * gMatrix F v1 v2 v3 =
      d1 F := by
  have heq := tau1_mul_gMatrix_eq F φ v1 v2 v3 hv1 hv2 hv3
  have hnonsing : (gMatrix F v1 v2 v3)⁻¹ * gMatrix F v1 v2 v3 = 1 :=
    Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp (gMatrix_isUnit F v1 v2 v3 hinj))
  rw [mul_assoc, heq, ← mul_assoc, hnonsing, one_mul]

theorem g_inv_mul_tau2_mul_g (φ : AutSL3 F)
    (v1 v2 v3 : Fin 3 → F)
    (hv1 : v1 ∈ LinearMap.range (pIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)) ⊓
        LinearMap.range (qIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F)))
    (hv2 : v2 ∈ LinearMap.range (qIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)) ⊓
        LinearMap.range (pIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F)))
    (hv3 : v3 ∈ LinearMap.range (qIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)) ⊓
        LinearMap.range (qIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F)))
    (hinj : Function.Injective (gMatrix F v1 v2 v3).mulVec) :
    (gMatrix F v1 v2 v3)⁻¹ * (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F) * gMatrix F v1 v2 v3 =
      d2 F := by
  have heq := tau2_mul_gMatrix_eq F φ v1 v2 v3 hv1 hv2 hv3
  have hnonsing : (gMatrix F v1 v2 v3)⁻¹ * gMatrix F v1 v2 v3 = 1 :=
    Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp (gMatrix_isUnit F v1 v2 v3 hinj))
  rw [mul_assoc, heq, ← mul_assoc, hnonsing, one_mul]

omit [Invertible (2 : F)] in
theorem conj_mul_eq (g A B : Matrix (Fin 3) (Fin 3) F) (hg_mul : g * g⁻¹ = 1) :
    g⁻¹ * (A * B) * g = (g⁻¹ * A * g) * (g⁻¹ * B * g) := by
  have step : (g⁻¹ * A * g) * (g⁻¹ * B * g) = g⁻¹ * A * (g * g⁻¹) * B * g := by
    simp only [mul_assoc]
  rw [step, hg_mul, mul_one]
  simp only [mul_assoc]

theorem g_inv_mul_tau3_mul_g (φ : AutSL3 F)
    (v1 v2 v3 : Fin 3 → F)
    (hv1 : v1 ∈ LinearMap.range (pIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)) ⊓
        LinearMap.range (qIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F)))
    (hv2 : v2 ∈ LinearMap.range (qIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)) ⊓
        LinearMap.range (pIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F)))
    (hv3 : v3 ∈ LinearMap.range (qIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)) ⊓
        LinearMap.range (qIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F)))
    (hinj : Function.Injective (gMatrix F v1 v2 v3).mulVec) :
    (gMatrix F v1 v2 v3)⁻¹ * (φ (d3SL F) : Matrix (Fin 3) (Fin 3) F) * gMatrix F v1 v2 v3 =
      d3 F := by
  have hg_mul : gMatrix F v1 v2 v3 * (gMatrix F v1 v2 v3)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp (gMatrix_isUnit F v1 v2 v3 hinj))
  have h3 : (φ (d3SL F) : Matrix (Fin 3) (Fin 3) F) =
      (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F) * (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F) :=
    (tau1_mul_tau2_eq_tau3 F φ).symm
  have hd3 : d3 F = d1 F * d2 F := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [d1, d2, d3, Matrix.diagonal, Matrix.mul_apply, Fin.sum_univ_three]
  rw [h3, hd3, conj_mul_eq F (gMatrix F v1 v2 v3) _ _ hg_mul,
    g_inv_mul_tau1_mul_g F φ v1 v2 v3 hv1 hv2 hv3 hinj,
    g_inv_mul_tau2_mul_g F φ v1 v2 v3 hv1 hv2 hv3 hinj]


/-! ### Final assembly

Package `(gMatrix v1 v2 v3)⁻¹` directly as a `Units` (val/inv given explicitly, so the
two coercions `↑g` and `↑g⁻¹` are the relevant matrices *by definition*, no extra
rewriting needed), and discharge the three conjugation identities via
`g_inv_mul_tauᵢ_mul_g`. -/

theorem diag_preserved_after_change_of_basis
    (φ : AutSL3 F) :
    ∃ g : GL3 F,
      innerAutSL3byGL3 g (φ (d1SL F)) = d1SL F ∧
      innerAutSL3byGL3 g (φ (d2SL F)) = d2SL F ∧
      innerAutSL3byGL3 g (φ (d3SL F)) = d3SL F := by
  obtain ⟨v1, hv1, hv1'⟩ := exists_v1 F φ
  obtain ⟨v2, hv2, hv2'⟩ := exists_v2 F φ
  obtain ⟨v3, hv3, hv3'⟩ := exists_v3 F φ
  have hinj := gMatrix_injective F φ v1 v2 v3 hv1 hv2 hv3 hv1' hv2' hv3'
  have hdetu : IsUnit (gMatrix F v1 v2 v3).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (gMatrix_isUnit F v1 v2 v3 hinj)
  have hvi : (gMatrix F v1 v2 v3)⁻¹ * gMatrix F v1 v2 v3 = 1 :=
    Matrix.nonsing_inv_mul _ hdetu
  have hiv : gMatrix F v1 v2 v3 * (gMatrix F v1 v2 v3)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ hdetu
  refine ⟨⟨(gMatrix F v1 v2 v3)⁻¹, gMatrix F v1 v2 v3, hvi, hiv⟩, ?_, ?_, ?_⟩
  · apply Subtype.ext
    show (gMatrix F v1 v2 v3)⁻¹ * (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F) *
        gMatrix F v1 v2 v3 = d1 F
    exact g_inv_mul_tau1_mul_g F φ v1 v2 v3 hv1 hv2 hv3 hinj
  · apply Subtype.ext
    show (gMatrix F v1 v2 v3)⁻¹ * (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F) *
        gMatrix F v1 v2 v3 = d2 F
    exact g_inv_mul_tau2_mul_g F φ v1 v2 v3 hv1 hv2 hv3 hinj
  · apply Subtype.ext
    show (gMatrix F v1 v2 v3)⁻¹ * (φ (d3SL F) : Matrix (Fin 3) (Fin 3) F) *
        gMatrix F v1 v2 v3 = d3 F
    exact g_inv_mul_tau3_mul_g F φ v1 v2 v3 hv1 hv2 hv3 hinj

def w1 : Matrix (Fin 3) (Fin 3) (R) :=
    !![0, 1, 0;
     -1, 0, 0;
     0, 0, 1]

def w2 : Matrix (Fin 3) (Fin 3) (R) :=
    !![1, 0, 0;
     0, 0, 1;
     0, -1, 0]

def w1SL : SL3 R :=
  ⟨w1 R, by
    simp [w1, Matrix.det_fin_three]
  ⟩

def w2SL : SL3 R :=
  ⟨w2 R, by
    simp [w2, Matrix.det_fin_three]
  ⟩

theorem w_preserved
    (φ : AutSL3 F) :
    ∃ g : GL3 F,
      innerAutSL3byGL3 g (φ (d1SL F)) = d1SL F ∧
      innerAutSL3byGL3 g (φ (d2SL F)) = d2SL F ∧
      innerAutSL3byGL3 g (φ (d3SL F)) = d3SL F ∧
      innerAutSL3byGL3 g (φ (w1SL F)) = w1SL F ∧
      innerAutSL3byGL3 g (φ (w2SL F)) = w2SL F := by
  rcases diag_preserved_after_change_of_basis F φ with ⟨g, hd1, hd2, hd3⟩
  let v1 := (innerAutSL3byGL3 g (φ (w1SL F))).val
  let v2 := (innerAutSL3byGL3 g (φ (w2SL F))).val
  have hv1: ∃ l : F, IsUnit l ∧ v1 =
    !![0,    l, 0;
       -l⁻¹, 0, 0;
       0,    0, 1] := by
    use v1 0 1
    have first_rep:
          !![v1 0 0, v1 0 1, 0;
             v1 1 0, v1 1 1, 0;
             0,      0,      v1 2 2] = v1 := by
      have (i : Fin 3) (j : Fin 3):
           !![v1 0 0,  v1 0 1,  -v1 0 2;
              v1 1 0,  v1 1 1,  -v1 1 2;
              -v1 2 0, -v1 2 1, v1 2 2] i j = v1 i j := by
        have: (d3 F) * v1 * (d3 F) = v1 := by
          have: (innerAutSL3byGL3 g (φ ((d3SL F) * (w1SL F) * (d3SL F)))) =
                 innerAutSL3byGL3 g (φ (w1SL F)) := by
            have: (d3SL F) * (w1SL F) * (d3SL F) = w1SL F := by
              have: (d3 F) * (w1 F) * (d3 F) = w1 F := by
                rw [w1, d3, diagonal_fin_three, mul_fin_three, mul_fin_three]
                simp
              apply Subtype.ext this
            rw [this]
          rw [map_mul, map_mul, map_mul, map_mul, hd3] at this
          simp only [v1]
          nth_rw 2 [← this]
          exact ext fun i => congrFun rfl
        rw [d3, diagonal_fin_three] at this
        nth_rw 10 [← this, eta_fin_three v1]
        simp
      ext i j
      fin_cases i <;> fin_cases j <;> simp
      · exact zero_iff_eq_neg_self.mpr (this 0 2).symm
      · exact zero_iff_eq_neg_self.mpr (this 1 2).symm
      · exact zero_iff_eq_neg_self.mpr (this 2 0).symm
      · exact zero_iff_eq_neg_self.mpr (this 2 1).symm
    have second_rep:
          !![0,      v1 0 1, 0;
             v1 1 0, 0,      0;
             0,      0,      v1 2 2] = v1 := by
      have: v1 * (d1 F) = (d2 F) * v1 := by
        have: v1 * (d1SL F) = (d2SL F) * v1 := by
          have: (innerAutSL3byGL3 g (φ ((w1SL F) * (d1SL F)))) =
                innerAutSL3byGL3 g (φ ((d2SL F) * (w1SL F))) := by
            have: (w1SL F) * (d1SL F) = (d2SL F) * (w1SL F) := by
              have: (w1 F) * (d1 F) = (d2 F) * (w1 F) := by
                rw [w1, d1, d2, diagonal_fin_three, diagonal_fin_three]
                simp
              apply Subtype.ext this
            rw [this]
          rw [map_mul, map_mul, map_mul, map_mul, hd2, hd1] at this
          rw [← SpecialLinearGroup.coe_mul, this]
          rfl
        exact this
      rw [d1, d2, diagonal_fin_three, diagonal_fin_three, ← first_rep] at this
      simp at this
      nth_rw 4 [← first_rep]
      ext i j
      fin_cases i <;> fin_cases j <;> simp
      · exact zero_iff_eq_neg_self.mpr this.left
      · exact zero_iff_eq_neg_self.mpr this.right.symm
    have det_v1: det v1 = 1 := by
      rw [SpecialLinearGroup.det_coe]
    have not_zero_v101: IsUnit (v1 0 1) := by
      apply IsUnit.mk0
      by_contra
      rw [← second_rep, this, det_fin_three] at det_v1
      simp at det_v1
    have third_rep:
          !![0,           v1 0 1, 0;
             -(v1 0 1)⁻¹, 0,      0;
             0,           0,      1] = v1 := by
      nth_rw 3 [← second_rep]
      have: v1 * v1 = d3 F := by
        have: (innerAutSL3byGL3 g (φ ((w1SL F) * (w1SL F)))) =
              innerAutSL3byGL3 g (φ (d3SL F)) := by
          have: (w1SL F) * (w1SL F) = (d3SL F) := by
            have: (w1 F) * (w1 F) = (d3 F) := by
              rw [w1, d3, diagonal_fin_three, mul_fin_three]
              simp
            apply Subtype.ext this
          rw [this]
        rw [map_mul, map_mul, hd3] at this
        simp only [v1]
        rw [← SpecialLinearGroup.coe_mul, this]
        rfl
      rw [← second_rep, d3, diagonal_fin_three] at this
      simp at this
      ext i j
      fin_cases i <;> fin_cases j <;> simp
      · rw [neg_eq_neg_one_mul, ← this.right.left, mul_assoc, not_zero_v101.mul_inv_cancel,
            mul_one]
      · have det_calc: 1 = -((v1 0 1) * (v1 1 0)) * (v1 2 2) := by
          nth_rw 1 [← det_v1, ← second_rep]
          rw [det_fin_three]
          simp
        rw [this.left, neg_neg, one_mul] at det_calc
        exact det_calc
    exact ⟨ not_zero_v101, third_rep.symm ⟩
  have hv2: ∃ l : F, IsUnit l ∧ v2 =
    !![1, 0,    0;
       0, 0,    l;
       0, -l⁻¹, 0] := by
    use v2 1 2
    have first_rep:
          !![v2 0 0, 0,      0;
             0,      v2 1 1, v2 1 2;
             0,      v2 2 1, v2 2 2] = v2 := by
      have (i : Fin 3) (j : Fin 3):
           !![v2 0 0,   -v2 0 1,  -v2 0 2;
              -v2 1 0,  v2 1 1,   v2 1 2;
              -v2 2 0,  v2 2 1,   v2 2 2] i j = v2 i j := by
        have: (d1 F) * v2 * (d1 F) = v2 := by
          have: (innerAutSL3byGL3 g (φ ((d1SL F) * (w2SL F) * (d1SL F)))) =
                 innerAutSL3byGL3 g (φ (w2SL F)) := by
            have: (d1SL F) * (w2SL F) * (d1SL F) = w2SL F := by
              have: (d1 F) * (w2 F) * (d1 F) = w2 F := by
                rw [w2, d1, diagonal_fin_three, mul_fin_three, mul_fin_three]
                simp
              apply Subtype.ext this
            rw [this]
          rw [map_mul, map_mul, map_mul, map_mul, hd1] at this
          simp only [v2]
          nth_rw 2 [← this]
          rfl
        rw [d1, diagonal_fin_three] at this
        nth_rw 10 [← this, eta_fin_three v2]
        simp
      ext i j
      fin_cases i <;> fin_cases j <;> simp
      · exact zero_iff_eq_neg_self.mpr (this 0 1).symm
      · exact zero_iff_eq_neg_self.mpr (this 0 2).symm
      · exact zero_iff_eq_neg_self.mpr (this 1 0).symm
      · exact zero_iff_eq_neg_self.mpr (this 2 0).symm
    have second_rep:
          !![v2 0 0, 0,      0;
             0,      0, v2 1 2;
             0,      v2 2 1, 0] = v2 := by
      have: v2 * (d3 F) = (d2 F) * v2 := by
        have: v2 * (d3SL F) = (d2SL F) * v2 := by
          have: (innerAutSL3byGL3 g (φ ((w2SL F) * (d3SL F)))) =
                innerAutSL3byGL3 g (φ ((d2SL F) * (w2SL F))) := by
            have: (w2SL F) * (d3SL F) = (d2SL F) * (w2SL F) := by
              have: (w2 F) * (d3 F) = (d2 F) * (w2 F) := by
                rw [w2, d3, d2, diagonal_fin_three, diagonal_fin_three]
                simp
              apply Subtype.ext this
            rw [this]
          rw [map_mul, map_mul, map_mul, map_mul, hd2, hd3] at this
          rw [← SpecialLinearGroup.coe_mul, this]
          rfl
        exact this
      rw [d3, d2, diagonal_fin_three, diagonal_fin_three, ← first_rep] at this
      simp at this
      nth_rw 4 [← first_rep]
      ext i j
      fin_cases i <;> fin_cases j <;> simp
      · exact zero_iff_eq_neg_self.mpr this.left.symm
      · exact zero_iff_eq_neg_self.mpr this.right
    have det_v2: det v2 = 1 := by
      rw [SpecialLinearGroup.det_coe]
    have not_zero_v212: IsUnit (v2 1 2) := by
      apply IsUnit.mk0
      by_contra
      rw [← second_rep, this, det_fin_three] at det_v2
      simp at det_v2
    have third_rep:
          !![1, 0,           0;
             0, 0,           v2 1 2;
             0, -(v2 1 2)⁻¹, 0] = v2 := by
      nth_rw 3 [← second_rep]
      have: v2 * v2 = d1 F := by
        have: (innerAutSL3byGL3 g (φ ((w2SL F) * (w2SL F)))) =
              innerAutSL3byGL3 g (φ (d1SL F)) := by
          have: (w2SL F) * (w2SL F) = (d1SL F) := by
            have: (w2 F) * (w2 F) = (d1 F) := by
              rw [w2, d1, diagonal_fin_three, mul_fin_three]
              simp
            apply Subtype.ext this
          rw [this]
        rw [map_mul, map_mul, hd1] at this
        simp only [v2]
        rw [← SpecialLinearGroup.coe_mul, this]
        rfl
      rw [← second_rep, d1, diagonal_fin_three] at this
      simp at this
      ext i j
      fin_cases i <;> fin_cases j <;> simp
      · have det_calc: 1 = - (v2 0 0) * (v2 1 2) * (v2 2 1) := by
          nth_rw 1 [← det_v2, ← second_rep]
          rw [det_fin_three]
          simp
        rw [mul_assoc, this.right.left, neg_mul_neg, mul_one] at det_calc
        exact det_calc
      · rw [neg_eq_neg_one_mul, ← this.right.right, mul_assoc, not_zero_v212.mul_inv_cancel,
            mul_one]
    exact ⟨ not_zero_v212, third_rep.symm ⟩
  rcases hv1 with ⟨l1, l1unit, hl1⟩
  rcases hv2 with ⟨l2, l2unit, hl2⟩
  use ⟨!![l1⁻¹, 0, 0;
          0,   1, 0;
          0,   0, l2] * g,
      g⁻¹ * !![l1, 0, 0;
                0,   1, 0;
                0,   0, l2⁻¹],
      by
        rw [mul_assoc, ← mul_assoc _ _ !![l1, 0, 0; 0, 1, 0; 0, 0, l2⁻¹], g.mul_inv, one_mul,
            mul_fin_three, l1unit.inv_mul_cancel, l2unit.mul_inv_cancel]
        simp only [zero_mul, add_zero, mul_zero, zero_add]
        rw [mul_one, one_fin_three],
      by
        rw [← mul_assoc, mul_assoc _ !![l1, 0, 0; 0, 1, 0; 0, 0, l2⁻¹], mul_fin_three,
            l1unit.mul_inv_cancel, l2unit.inv_mul_cancel]
        simp only [zero_mul, add_zero, mul_zero, zero_add]
        rw [mul_one, ← one_fin_three, mul_one, g.inv_mul]
      ⟩
  simp only [innerAutSL3byGL3, MulEquiv.coe_mk, Equiv.coe_fn_mk, Units.inv_mk]
  have diag_preserved:
    g * (φ (d1SL F)).toGL * g⁻¹ = d1 F ∧
    g * (φ (d2SL F)).toGL * g⁻¹ = d2 F ∧
    g * (φ (d3SL F)).toGL * g⁻¹ = d3 F :=
      ⟨ congrArg Subtype.val hd1, congrArg Subtype.val hd2, congrArg Subtype.val hd3 ⟩
  simp only [v1, innerAutSL3byGL3, MulEquiv.coe_mk, Equiv.coe_fn_mk] at hl1
  simp only [v2, innerAutSL3byGL3, MulEquiv.coe_mk, Equiv.coe_fn_mk] at hl2
  repeat' constructor
  all_goals congr
  all_goals rw [
      ← mul_assoc,
      mul_assoc !![l1⁻¹, 0, 0; 0, 1, 0; 0, 0, l2],
      mul_assoc !![l1⁻¹, 0, 0; 0, 1, 0; 0, 0, l2]
    ]
  any_goals simp only [diag_preserved, d1, d2, d3, diagonal_fin_three]
  · simp [l1unit.inv_mul_cancel, l2unit.mul_inv_cancel]
  · simp [l1unit.inv_mul_cancel, l2unit.mul_inv_cancel]
  · simp [l1unit.inv_mul_cancel, l2unit.mul_inv_cancel]
  · rw [mul_assoc !![l1⁻¹, 0, 0; 0, 1, 0; 0, 0, l2], hl1, w1, mul_fin_three, mul_fin_three]
    simp [zero_mul, add_zero, mul_zero, zero_add, l1unit.inv_mul_cancel, l2unit.mul_inv_cancel]
  · rw [mul_assoc !![l1⁻¹, 0, 0; 0, 1, 0; 0, 0, l2], hl2, w2, mul_fin_three, mul_fin_three]
    simp [zero_mul, add_zero, mul_zero, zero_add, l1unit.inv_mul_cancel, l2unit.mul_inv_cancel]



def x12 : Matrix (Fin 3) (Fin 3) R :=
  !![1, 1, 0;
     0, 1, 0;
     0, 0, 1]

def x12SL : SL3 R :=
  ⟨x12 R, by simp [x12, Matrix.det_fin_three]⟩

def x13 : Matrix (Fin 3) (Fin 3) R :=
  !![1, 0, 1;
     0, 1, 0;
     0, 0, 1]

def x13SL : SL3 R :=
  ⟨x13 R, by simp [x13, Matrix.det_fin_three]⟩

def x23 : Matrix (Fin 3) (Fin 3) R :=
  !![1, 0, 0;
     0, 1, 1;
     0, 0, 1]

def x23SL : SL3 R :=
  ⟨x23 R, by simp [x23, Matrix.det_fin_three]⟩

def x32 : Matrix (Fin 3) (Fin 3) R :=
  !![1, 0, 0;
     0, 1, 0;
     0, 1, 1]

def x32SL : SL3 R :=
  ⟨x32 R, by simp [x32, Matrix.det_fin_three]⟩

def x32' : Matrix (Fin 3) (Fin 3) R :=
  !![1, 0, 0;
     0, 1, 0;
     0, -1, 1]

def x32SL' : SL3 R :=
  ⟨x32' R, by simp [x32', Matrix.det_fin_three]⟩

def graphChoiceSL3 {R : Type*} [CommRing R] (ε : Bool) : AutSL3 R :=
  if ε then invTransposeAutSL3 else (1 : AutSL3 R)

/--
# Preservation of Standard Matrices under Contragredient
Proves that the contragredient automorphism `Λ(A) := (A⁻¹)ᵀ` (formally `invTransposeAutSL3`)
preserves the involutions `d₁`, `d₂`, `d₃` and the signed transpositions `w₁`, `w₂`.

## Mathematical Insight
Rather than calculating the explicit adjugate matrices or wrestling with matrix inverses directly,
this proof exploits the orthogonal and symmetric nature of the target matrices. For each of these
specific matrices `A`, we show that `Aᵀ * A = 1`. By the uniqueness of inverses, this implies
`A⁻¹ = Aᵀ`, which means `Λ(A) = (Aᵀ)ᵀ = A`.
-/
theorem invTranspose_preserves_d_w (F : Type*) [Field F] [Invertible (2 : F)] :
    invTransposeAutSL3 (d1SL F) = d1SL F ∧
    invTransposeAutSL3 (d2SL F) = d2SL F ∧
    invTransposeAutSL3 (d3SL F) = d3SL F ∧
    invTransposeAutSL3 (w1SL F) = w1SL F ∧
    invTransposeAutSL3 (w2SL F) = w2SL F := by

  -- We prove preservation for d₁ by demonstrating that d₁ᵀ * d₁ = 1.
  have hd1 : invTransposeAutSL3 (d1SL F) = d1SL F := by
    -- We explicitly construct the transpose of d₁ as an SL₃ element.
    let d1T_SL : SL3 F := ⟨(d1 F).transpose, by rw [Matrix.det_transpose]; exact (d1SL F).property⟩

    -- We evaluate the multiplication d₁ᵀ * d₁ = 1 explicitly on the underlying matrices.
    -- This establishes the left-inverse property required to find the true inverse.
    have h_mul : d1T_SL * d1SL F = 1 := by
      apply Subtype.ext
      change (d1 F).transpose * d1 F = 1
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp only [Matrix.mul_apply, Matrix.transpose_apply] <;>
        simp [d1, Matrix.diagonal_apply, cons_val, Fin.reduceFinMk]

    -- Now, Aᵀ * A = 1 implies A⁻¹ = Aᵀ.
    have h_inv : (d1SL F)⁻¹ = d1T_SL := mul_eq_one_iff_inv_eq'.mp h_mul

    -- We map the equality down to the matrix level to apply the contragredient transformation.
    apply Subtype.ext
    change (((d1SL F)⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F).transpose = d1 F

    -- Since A⁻¹ = Aᵀ, we substitute the inverse, and the double transpose cancels out: (Aᵀ)ᵀ = A.
    rw [h_inv]
    change ((d1 F).transpose).transpose = d1 F
    ext i j; rfl

  -- We apply the exact same inverse-transpose cancellation logic for d₂.
  have hd2 : invTransposeAutSL3 (d2SL F) = d2SL F := by
    let d2T_SL : SL3 F := ⟨(d2 F).transpose, by rw [Matrix.det_transpose]; exact (d2SL F).property⟩
    have h_mul : d2T_SL * d2SL F = 1 := by
      apply Subtype.ext
      change (d2 F).transpose * d2 F = 1
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp only [Matrix.mul_apply, Matrix.transpose_apply] <;>
        simp [d2, Matrix.diagonal_apply, cons_val, Fin.reduceFinMk]

    have h_inv : (d2SL F)⁻¹ = d2T_SL := mul_eq_one_iff_inv_eq'.mp h_mul
    apply Subtype.ext
    change (((d2SL F)⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F).transpose = d2 F
    rw [h_inv]
    change ((d2 F).transpose).transpose = d2 F
    ext i j; rfl

  -- We apply the exact same inverse-transpose cancellation logic for d₃.
  have hd3 : invTransposeAutSL3 (d3SL F) = d3SL F := by
    let d3T_SL : SL3 F := ⟨(d3 F).transpose, by rw [Matrix.det_transpose]; exact (d3SL F).property⟩
    have h_mul : d3T_SL * d3SL F = 1 := by
      apply Subtype.ext
      change (d3 F).transpose * d3 F = 1
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp only [Matrix.mul_apply, Matrix.transpose_apply] <;>
        simp [d3, Matrix.diagonal_apply, cons_val, Fin.reduceFinMk]

    have h_inv : (d3SL F)⁻¹ = d3T_SL := mul_eq_one_iff_inv_eq'.mp h_mul
    apply Subtype.ext
    change (((d3SL F)⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F).transpose = d3 F
    rw [h_inv]
    change ((d3 F).transpose).transpose = d3 F
    ext i j; rfl

  -- We apply the exact same inverse-transpose cancellation logic for the matrix w₁.
  have hw1 : invTransposeAutSL3 (w1SL F) = w1SL F := by
    let w1T_SL : SL3 F := ⟨(w1 F).transpose, by rw [Matrix.det_transpose]; exact (w1SL F).property⟩
    have h_mul : w1T_SL * w1SL F = 1 := by
      apply Subtype.ext
      change (w1 F).transpose * w1 F = 1
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp only [Matrix.mul_apply, Matrix.transpose_apply] <;>
        simp [w1, Fin.sum_univ_three, of_apply, cons_val, Fin.reduceFinMk]

    have h_inv : (w1SL F)⁻¹ = w1T_SL := mul_eq_one_iff_inv_eq'.mp h_mul
    apply Subtype.ext
    change (((w1SL F)⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F).transpose = w1 F
    rw [h_inv]
    change ((w1 F).transpose).transpose = w1 F
    ext i j; rfl

  -- We apply the exact same inverse-transpose cancellation logic for the matrix w₂.
  have hw2 : invTransposeAutSL3 (w2SL F) = w2SL F := by
    let w2T_SL : SL3 F := ⟨(w2 F).transpose, by rw [Matrix.det_transpose]; exact (w2SL F).property⟩
    have h_mul : w2T_SL * w2SL F = 1 := by
      apply Subtype.ext
      change (w2 F).transpose * w2 F = 1
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp only [Matrix.mul_apply, Matrix.transpose_apply] <;>
        simp [w2, Fin.sum_univ_three, of_apply, cons_val, Fin.reduceFinMk]

    have h_inv : (w2SL F)⁻¹ = w2T_SL := mul_eq_one_iff_inv_eq'.mp h_mul
    apply Subtype.ext
    change (((w2SL F)⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F).transpose = w2 F
    rw [h_inv]
    change ((w2 F).transpose).transpose = w2 F
    ext i j; rfl

  exact ⟨hd1, hd2, hd3, hw1, hw2⟩

/--
# Normalization of X₁₂ (Step 3)
Verifies **Step 3** of the main classification proof for automorphisms of `SL₃(F)`
(where `F` is a field of characteristic `≠ 2`). It proves that after prior diagonal
normalizations, we can successfully map the image of `x₁₂` to standard position.

## Proof Outline
From earlier steps, `X₁₂` is constrained to either `x₁₂(b)` or `x₂₁(c)`.
We evaluate the commutator relation `[X₁₂, X₂₃] = X₁₃` to restrict the constants:
1. **Case 1 (`X₁₂ = x₁₂(b)`):** Evaluating the commutator at entry `(0, 2)` forces `b² = b`.
   Since `F` is a field and `b ≠ 0`, `b = 1`. No further automorphisms are needed (`ε = false`).
2. **Case 2 (`X₁₂ = x₂₁(c)`):** Evaluating the commutator at entry `(2, 0)` forces `c² + c = 0`.
   Since `c ≠ 0`, `c = -1`. We then compose our map with the contragredient automorphism
   (`ε = true`), which preserves the base matrices (via `invTranspose_preserves_d_w`) and
   successfully flips `x₂₁(-1)` back to the standard `x₁₂(1)`.
-/
theorem x12_preserved (φ : AutSL3 F) : ∃ (g : GL3 F) (ε : Bool),
      graphChoiceSL3 ε (innerAutSL3byGL3 g (φ (d1SL F))) = d1SL F ∧
      graphChoiceSL3 ε (innerAutSL3byGL3 g (φ (d2SL F))) = d2SL F ∧
      graphChoiceSL3 ε (innerAutSL3byGL3 g (φ (d3SL F))) = d3SL F ∧
      graphChoiceSL3 ε (innerAutSL3byGL3 g (φ (w1SL F))) = w1SL F ∧
      graphChoiceSL3 ε (innerAutSL3byGL3 g (φ (w2SL F))) = w2SL F ∧
      graphChoiceSL3 ε (innerAutSL3byGL3 g (φ (x12SL F))) = x12SL F := by

  -- Get matrix g utilizing steps 1 and 2 for which the inner automorphism preserves
  -- d₁, ..., d₃, and w₁, ..., w₃. w₃ being preserved is given by w₁, and w₂ being
  -- preserved, so we don't assume anything about it.
  rcases w_preserved F φ with ⟨g, hd1, hd2, hd3, hw1, hw2⟩

  -- Define φ₂ as the inner automorphism by g.
  let φ2 : AutSL3 F := φ.trans (innerAutSL3byGL3 g)

  have hd1_φ2 : φ2 (d1SL F) = d1SL F := hd1
  have hd2_φ2 : φ2 (d2SL F) = d2SL F := hd2
  have hd3_φ2 : φ2 (d3SL F) = d3SL F := hd3
  have hw1_φ2 : φ2 (w1SL F) = w1SL F := hw1
  have hw2_φ2 : φ2 (w2SL F) = w2SL F := hw2

  -- Denote X₁₂ as the image of x₁₂ under the current automorphism.
  -- We also denote it as (bᵢⱼ).
  let X12 := (φ2 (x12SL F)).val

  -- We first prove that X₁₂ commutes with d₃.
  -- This holds for x₁₂ and d₃, and since d₃ is fixed this follows.
  have h_comm_d3_X12 : (d3 F) * X12 = X12 * (d3 F) := by
    have h_comm_in_images: (φ2 (d3SL F * x12SL F)) = (φ2 (x12SL F * d3SL F)) := by
      -- We first prove that x₁₂ and d₃ commute.
      have h_comm_orig : d3SL F * x12SL F = x12SL F * d3SL F := by
        have h_matrix_comm : d3 F * x12 F = x12 F * d3 F := by
          rw [d3, x12, diagonal_fin_three, mul_fin_three, mul_fin_three]
          simp
        apply Subtype.ext h_matrix_comm
      rw [h_comm_orig]
    simp only [map_mul] at h_comm_in_images
    -- Use the fact that d₃ is fixed.
    rw [hd3_φ2] at h_comm_in_images
    -- Extract a matrix equality from the SL₃(F) matrix equality at h_inv_in_images.
    exact congrArg Subtype.val h_comm_in_images

  -- Commutativity with d₃ forces X₁₂ to be block-diagonal, with a 2x2 and a 1x1 block.
  have hX12_02 : X12 0 2 = 0 := by
    -- Matrices are functions, so entry-wise equality can be yielded by basic function facts.
    have h_entry : ((d3 F) * X12) 0 2 = (X12 * (d3 F)) 0 2 :=
      congrFun (congrFun h_comm_d3_X12 0) 2
    simp [d3, Matrix.mul_apply, Matrix.diagonal_apply] at h_entry
    exact (zero_iff_eq_neg_self.mpr h_entry.symm).symm

  have hX12_12 : X12 1 2 = 0 := by
    have h_entry : ((d3 F) * X12) 1 2 = (X12 * (d3 F)) 1 2 :=
      congrFun (congrFun h_comm_d3_X12 1) 2
    simp [d3, Matrix.mul_apply, Matrix.diagonal_apply] at h_entry
    exact (zero_iff_eq_neg_self.mpr h_entry.symm).symm

  have hX12_20 : X12 2 0 = 0 := by
    have h_entry : ((d3 F) * X12) 2 0 = (X12 * (d3 F)) 2 0 :=
      congrFun (congrFun h_comm_d3_X12 2) 0
    simp [d3, Matrix.mul_apply, Matrix.diagonal_apply] at h_entry
    exact (zero_iff_eq_neg_self.mpr h_entry).symm

  have hX12_21 : X12 2 1 = 0 := by
    have h_entry : ((d3 F) * X12) 2 1 = (X12 * (d3 F)) 2 1 :=
      congrFun (congrFun h_comm_d3_X12 2) 1
    simp [d3, Matrix.mul_apply, Matrix.diagonal_apply] at h_entry
    exact (zero_iff_eq_neg_self.mpr h_entry).symm

  -- Similarly to before, we now prove that conjugation by d₁ of X₁₂ is its inverse.
  have h_inv_d1_X12 : (d1 F) * X12 * (d1 F) * X12 = 1 := by
    have h_inv_in_images : φ2 (d1SL F * x12SL F * d1SL F * x12SL F) = φ2 1 := by
      have h_inv_orig : d1SL F * x12SL F * d1SL F * x12SL F = 1 := by
        have h_matrix_inv : d1 F * x12 F * d1 F * x12 F = 1 := by
          rw [d1, x12, diagonal_fin_three, one_fin_three, mul_fin_three, mul_fin_three, mul_fin_three]
          simp
        apply Subtype.ext h_matrix_inv
      rw [h_inv_orig]
    simp at h_inv_in_images
    rw [hd1_φ2] at h_inv_in_images
    exact congrArg Subtype.val h_inv_in_images

  -- Extract equations on X₁₂ entries via the equality d₁ * X₁₂ * d₁ * X₁₂ = 1.
  -- We first show what d₁ * X₁₂ * d₁ * X₁₂ is equal to entry-wise.
  have h_X12_matrix_eval : !![X12 0 0 * X12 0 0 - X12 0 1 * X12 1 0, X12 0 0 * X12 0 1 - X12 0 1 * X12 1 1, 0;
                              -(X12 1 0 * X12 0 0) + X12 1 1 * X12 1 0, -(X12 0 1 * X12 1 0) + X12 1 1 * X12 1 1, 0;
                              0, 0, X12 2 2 * X12 2 2] = d1 F * X12 * d1 F * X12 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [Matrix.mul_apply, Fin.sum_univ_three] <;>
      simp [d1, of_apply, cons_val, Fin.reduceFinMk, hX12_02, hX12_12, hX12_20, hX12_21] <;>
      ring

  -- We now combine it with the fact that d₁ * X₁₂ * d₁ * X₁₂ = 1.
  have h_X12_eqs : !![X12 0 0 * X12 0 0 - X12 0 1 * X12 1 0, X12 0 0 * X12 0 1 - X12 0 1 * X12 1 1, 0;
                      -(X12 1 0 * X12 0 0) + X12 1 1 * X12 1 0, -(X12 0 1 * X12 1 0) + X12 1 1 * X12 1 1, 0;
                      0, 0, X12 2 2 * X12 2 2] = (1 : Matrix (Fin 3) (Fin 3) F) := by
    rw [h_X12_matrix_eval, h_inv_d1_X12]

  -- For future use, we extract these entry-equalities as theorems.
  have hX12_00 : X12 0 0 * X12 0 0 - X12 0 1 * X12 1 0 = 1 := congrFun (congrFun h_X12_eqs 0) 0
  have hX12_01 : X12 0 0 * X12 0 1 - X12 0 1 * X12 1 1 = 0 := congrFun (congrFun h_X12_eqs 0) 1
  have hX12_10 : -(X12 1 0 * X12 0 0) + X12 1 1 * X12 1 0 = 0 := congrFun (congrFun h_X12_eqs 1) 0
  have hX12_11 : -(X12 0 1 * X12 1 0) + X12 1 1 * X12 1 1 = 1 := congrFun (congrFun h_X12_eqs 1) 1
  have hX12_22 : X12 2 2 * X12 2 2 = 1 := congrFun (congrFun h_X12_eqs 2) 2

  -- We now prove b₁₁ = b₂₂.
  -- We first need the following helper lemma, which we will also need later in the proof.
  have h_diag_gives_contra : (X12 0 1 = 0 ∧ X12 1 0 = 0) → False := by
    rintro ⟨hb12_zero, hb21_zero⟩

    -- Substitute b₁₂ = 0 and b₂₁ = 0 back into our equations, yielding that b₁₁² = b₂₂² = 1.
    have hb11_sq : X12 0 0 * X12 0 0 = 1 := by
      calc X12 0 0 * X12 0 0
        _ = X12 0 0 * X12 0 0 - X12 0 1 * X12 1 0 := by rw [hb12_zero, zero_mul, sub_zero]
        _ = 1 := hX12_00

    have hb22_sq : X12 1 1 * X12 1 1 = 1 := by
      calc X12 1 1 * X12 1 1
        _ = - (X12 0 1 * X12 1 0) + X12 1 1 * X12 1 1 := by rw [hb12_zero, zero_mul, neg_zero, zero_add]
        _ = 1 := hX12_11

    -- We now have that X₁₂ is diagonal with entries whose squares are 1 on the diagonal.
    -- Hence it has order 2. To be more exact, we only need to show it becomes I when squared.
    -- Showing that this is true is done by a quick calculation.
    have h_X12_sq : X12 * X12 = 1 := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_three, hX12_02, hX12_12, hX12_20, hX12_21, hb12_zero, hb21_zero]
      · exact hb11_sq
      · exact hb22_sq
      · exact hX12_22

    -- Automorphisms preserve identities like a matrix having its square be 1, since 1 is preserved.
    have h_x12_sq_eq_1 : x12 F * x12 F = 1 := by
      have h_image_sq : φ2 (x12SL F) * φ2 (x12SL F) = 1 := Subtype.ext h_X12_sq
      rw [← map_mul, ← map_one φ2] at h_image_sq
      -- Since φ2 is an automorphism, it is injective, the inputs must be equal.
      have h_sl3_sq : x12SL F * x12SL F = 1 := EquivLike.injective φ2 h_image_sq
      -- Extract the raw matrices equality.
      exact congrArg Subtype.val h_sl3_sq

    -- Yield a contradiction since x₁₂ square is not 1.
    have h_two_eq_zero : (2 : F) = 0 := by
      have h_eval : (x12 F * x12 F) 0 1 = (1 : Matrix (Fin 3) (Fin 3) F) 0 1 :=
        congrFun (congrFun h_x12_sq_eq_1 0) 1
      simp [x12, Matrix.mul_apply, Fin.sum_univ_three] at h_eval
      -- h_eval reduces to 1+1 = 0
      linear_combination h_eval

    exact absurd h_two_eq_zero two_ne_zero

  -- We can now show b₁₁ = b₂₂.
  have hb11_eq_b22 : X12 0 0 = X12 1 1 := by
    -- Assume in contradiction this isn't the case.
    by_contra h_neq
    have h_diff_ne_zero : X12 0 0 - X12 1 1 ≠ 0 := sub_ne_zero.mpr h_neq
    have hX12_01_factored : X12 0 1 * (X12 0 0 - X12 1 1) = 0 := by linear_combination hX12_01

    -- F is a field, and in particular an integral domain.
    -- Therefore if a product is 0, and one of the multiplied elements is not 0, the other must be 0. Hence b₁₂ is 0.
    have hb12_zero : X12 0 1 = 0 := (mul_eq_zero.mp hX12_01_factored).resolve_right h_diff_ne_zero

    -- Similarly one shows that b₂₁ is 0.
    have hX12_10_factored : X12 1 0 * (X12 1 1 - X12 0 0) = 0 := by linear_combination hX12_10
    have h_diff2_ne_zero : X12 1 1 - X12 0 0 ≠ 0 := sub_ne_zero.mpr (Ne.symm h_neq)
    have hb21_zero : X12 1 0 = 0 := (mul_eq_zero.mp hX12_10_factored).resolve_right h_diff2_ne_zero

    -- We get a contradiction using our helper lemma.
    exact h_diag_gives_contra ⟨hb12_zero, hb21_zero⟩

  -- Using determinants, we can also get that b₃₃ is 1.
  have hb33_eq_1 : X12 2 2 = 1 := by
    have h_det : X12.det = 1 := (φ2 (x12SL F)).property
    -- Expand determinant.
    rw [Matrix.det_fin_three] at h_det
    -- Equalities on X₁₂'s entries allow us to simplify this determinant.
    simp [hX12_02, hX12_12, hX12_20, hX12_21] at h_det
    rw [← mul_sub_right_distrib, ← hb11_eq_b22, hX12_00, one_mul] at h_det
    exact h_det

  -- We now calculate the image of x₁₃ in terms of X₁₂.
  -- We first introduce X₁₃ as this image.
  let X13 := (φ2 (x13SL F)).val

  -- The proof of what X₁₃ looks like is divided into several parts.
  -- We first show some equation on x₁₃⁻¹ in terms of other matrices.
  -- We then apply Φ₂ on it, and use this to find explicitly the coordinates of X₁₃⁻¹ in terms of the coordinates of X₁₂.
  -- Finally we just take the inverse of that matrix to get the desired form of X₁₃.

  -- We first show that x₁₃ * w₂ * x₁₂ = w₂.
  have h_x13_w2_x12 : x13SL F * w2SL F * x12SL F = w2SL F := by
    -- It suffices to prove this for the underlying matrices. This is a simple product calculation.
    have h_mat : x13 F * w2 F * x12 F = w2 F := by
      rw [x13, w2, x12, mul_fin_three, mul_fin_three]
      simp
    apply Subtype.ext h_mat

  -- Getting the initial equality now follows from an elementary group calculation.
  have h_w2_x12_conj : w2SL F * x12SL F * (w2SL F)⁻¹ = (x13SL F)⁻¹ := by
    -- Move x₁₃ to the other side.
    apply mul_left_cancel (a := x13SL F)
    -- We now apply the fact that x₁₃ * w₂ * x₁₂ = w₂ to simplify the left-hand side.
    rw [← mul_assoc, ← mul_assoc, h_x13_w2_x12]
    simp

  -- We would like to now apply Φ₂ to this equation to calculate the terms of the inverse of X₁₃.
  -- We first need to calculate w₂'s inverse however, as it appears on the left-hand-side.
  have h_w2_inv : (w2SL F)⁻¹ = w2SL F * d1SL F := by
    -- Prove w₂ * (w₂ * d₁) = 1.
    have h_mul : w2SL F * (w2SL F * d1SL F) = 1 := by
      have h_mat : w2 F * (w2 F * d1 F) = 1 := by
        rw [w2, d1, diagonal_fin_three, one_fin_three, mul_fin_three, mul_fin_three]
        simp
      apply Subtype.ext h_mat
    rw [mul_eq_one_iff_inv_eq', inv_eq_iff_eq_inv] at h_mul
    exact h_mul.symm

  -- Let us now apply Φ₂ to get an equality on X₁₃⁻¹.
  let X13_inv := (φ2 (x13SL F)⁻¹).val

  have h_X13_inv_eq : X13_inv = w2 F * X12 * (w2 F * d1 F) := by
    -- Applying Φ₂ gives the following equality at first.
    have h_img : φ2 (x13SL F)⁻¹ = φ2 (w2SL F * x12SL F * (w2SL F)⁻¹) := congrArg φ2 h_w2_x12_conj.symm
    -- We may now simplify it.
    simp at h_img
    rw [← map_inv] at h_img
    rw [hw2_φ2, h_w2_inv] at h_img

    -- We now move this SL₃ matrices equality to matrix equality, and by simply substituting
    -- the elements in this equality by the notation for them, we are done.
    have h_img_mat := congrArg Subtype.val h_img

    calc X13_inv
      _ = (φ2 ((x13SL F)⁻¹)).val := rfl
      _ = (w2SL F * φ2 (x12SL F) * (w2SL F * d1SL F)).val := h_img_mat
      _ = (w2SL F * φ2 (x12SL F)).val * (w2SL F * d1SL F).val := by rw [SpecialLinearGroup.coe_mul]
      _ = (w2SL F).val * (φ2 (x12SL F)).val * ((w2SL F).val * (d1SL F).val) := by rw [SpecialLinearGroup.coe_mul, SpecialLinearGroup.coe_mul]
      _ = w2 F * X12 * (w2 F * d1 F) := rfl

  -- Using the established equality on X₁₃⁻¹,
  -- we can calculate all its entries in terms of those of X₁₂.
  have h_X13inv_mat : X13_inv =
      !![ X12 0 0, 0, -X12 0 1;
                0, 1,        0;
         -X12 1 0, 0,  X12 1 1] := by
    rw [h_X13_inv_eq]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [Matrix.mul_apply, Fin.sum_univ_three] <;>
      simp [w2, d1, of_apply, cons_val, Fin.reduceFinMk,
            hX12_02, hX12_12, hX12_20, hX12_21, hb33_eq_1]

  -- Let us now calculate the entries matrix X₁₃, which is the inverse of X₁₃⁻¹.
  -- We first show that the entries we want form an inverse matrix.
  -- We slightly rearrange elements for this.
  have h11_sub : X12 1 1 * X12 1 1 = 1 + X12 0 1 * X12 1 0 := by linear_combination hX12_11
  have h_X13_target_mul_inv : !![X12 0 0, 0, X12 0 1;
                                       0, 1,       0;
                                 X12 1 0, 0, X12 1 1] * X13_inv = 1 := by
    rw [h_X13inv_mat]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply] <;>
      simp [of_apply, cons_val, Fin.reduceFinMk, hb11_eq_b22, h11_sub] <;>
      ring

  -- We now establish that X₁₃⁻¹ * X₁₃ = 1 as well.
  -- This is entirely trivial, but since X13_inv isn't defined for this
  -- to be exactly immediate we need to do a small calculation.
  have h_inv_mul_X13 : X13_inv * X13 = 1 := by
    calc X13_inv * X13
      _ = (φ2 ((x13SL F)⁻¹)).val * (φ2 (x13SL F)).val := rfl
      _ = (φ2 ((x13SL F)⁻¹) * φ2 (x13SL F)).val := by rw [← SpecialLinearGroup.coe_mul]
      _ = (φ2 ((x13SL F)⁻¹ * x13SL F)).val := by rw [← map_mul]
      _ = (φ2 1).val := by rw [inv_mul_cancel]
      _ = (1 : SL3 F).val := by rw [map_one]
      _ = 1 := rfl

  -- We now get the desired equality for X₁₃.
  have h_X13_mat : X13 = !![X12 0 0, 0, X12 0 1;
                                  0, 1,       0;
                            X12 1 0, 0, X12 1 1] := by
    calc X13
      _ = 1 * X13 := by rw [Matrix.one_mul]
      _ = (!![X12 0 0, 0, X12 0 1; 0, 1, 0; X12 1 0, 0, X12 1 1] * X13_inv) * X13 := by
        rw [h_X13_target_mul_inv]
      _ = !![X12 0 0, 0, X12 0 1; 0, 1, 0; X12 1 0, 0, X12 1 1] * (X13_inv * X13) := by
        rw [Matrix.mul_assoc]
      _ = !![X12 0 0, 0, X12 0 1; 0, 1, 0; X12 1 0, 0, X12 1 1] * 1 := by rw [h_inv_mul_X13]
      _ = !![X12 0 0, 0, X12 0 1; 0, 1, 0; X12 1 0, 0, X12 1 1] := by rw [Matrix.mul_one]

  have hX13_00 : X13 0 0 = X12 0 0 := congrFun (congrFun h_X13_mat 0) 0
  have hX13_01 : X13 0 1 = 0       := congrFun (congrFun h_X13_mat 0) 1
  have hX13_02 : X13 0 2 = X12 0 1 := congrFun (congrFun h_X13_mat 0) 2
  have hX13_10 : X13 1 0 = 0       := congrFun (congrFun h_X13_mat 1) 0
  have hX13_11 : X13 1 1 = 1       := congrFun (congrFun h_X13_mat 1) 1
  have hX13_12 : X13 1 2 = 0       := congrFun (congrFun h_X13_mat 1) 2
  have hX13_20 : X13 2 0 = X12 1 0 := congrFun (congrFun h_X13_mat 2) 0
  have hX13_21 : X13 2 1 = 0       := congrFun (congrFun h_X13_mat 2) 1
  have hX13_22 : X13 2 2 = X12 1 1 := congrFun (congrFun h_X13_mat 2) 2

  -- The next step is now showing that X₁₂ and X₁₃ commute.
  -- This is as they are images of commuting matrices in a homomorphism.
  have h_x12_x13_comm_mat : x12 F * x13 F = x13 F * x12 F := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [Matrix.mul_apply, Fin.sum_univ_three] <;>
      simp [x12, x13, of_apply, cons_val, Fin.reduceFinMk]

  -- We have shown that x₁₂ and x₁₃ commute on a matrix level.
  -- Let us lift it to an SL₃ equality.
  have h_x12SL_x13SL_comm : x12SL F * x13SL F = x13SL F * x12SL F := Subtype.ext h_x12_x13_comm_mat

  -- Using the fact that X₁₂ and X₁₃ are images of commuting matrices we are done.
  have h_X12_X13_comm : X12 * X13 = X13 * X12 := by
    calc X12 * X13
      _ = (φ2 (x12SL F)).val * (φ2 (x13SL F)).val := rfl
      _ = (φ2 (x12SL F) * φ2 (x13SL F)).val := by rw [← SpecialLinearGroup.coe_mul]
      _ = (φ2 (x12SL F * x13SL F)).val := by rw [← map_mul]
      _ = (φ2 (x13SL F * x12SL F)).val := by rw [h_x12SL_x13SL_comm]
      _ = (φ2 (x13SL F) * φ2 (x12SL F)).val := by rw [map_mul]
      _ = (φ2 (x13SL F)).val * (φ2 (x12SL F)).val := by rw [SpecialLinearGroup.coe_mul]
      _ = X13 * X12 := rfl

  -- This means that the commutator X₁₂ * X₁₃ - X₁₃ * X₁₂ = 0.
  -- This is useful since explicitly calculating
  -- X₁₂ * X₁₃ - X₁₃ * X₁₂ yields more equations on the entries of X₁₂.
  have h_X12_X13_sub_eq_zero : X12 * X13 - X13 * X12 = 0 := by rw [h_X12_X13_comm, sub_self]

  -- We now evaluate the commutator X₁₂ * X₁₃ - X₁₃ * X₁₂ explicitly as a matrix.
  have h_comm_matrix_eval : !![0, X12 0 1 - X12 0 0 * X12 0 1, X12 0 0 * X12 0 1 - X12 0 1;
                               X12 1 0 * X12 0 0 - X12 1 0, 0, X12 1 0 * X12 0 1;
                               X12 1 0 - X12 1 0 * X12 0 0, -(X12 1 0 * X12 0 1), 0] =
                               X12 * X13 - X13 * X12 := by
    rw [h_X13_mat]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_three] <;>
      simp [of_apply, cons_val, Fin.reduceFinMk, hX12_02, hX12_12,
            hX12_20, hX12_21, hb33_eq_1, hb11_eq_b22]

  -- We have proved that the commutator is zero, yielding the following matrix equality.
  have h_comm_eqs : !![0, X12 0 1 - X12 0 0 * X12 0 1, X12 0 0 * X12 0 1 - X12 0 1;
                       X12 1 0 * X12 0 0 - X12 1 0, 0, X12 1 0 * X12 0 1;
                       X12 1 0 - X12 1 0 * X12 0 0, -(X12 1 0 * X12 0 1), 0] =
                       (0 : Matrix (Fin 3) (Fin 3) F) := by
    rw [h_comm_matrix_eval, h_X12_X13_sub_eq_zero]

  -- We hence get the following six equations.
  have h_comm_01 : X12 0 1 - X12 0 0 * X12 0 1 = 0 := congrFun (congrFun h_comm_eqs 0) 1
  have h_comm_02 : X12 0 0 * X12 0 1 - X12 0 1 = 0 := congrFun (congrFun h_comm_eqs 0) 2
  have h_comm_10 : X12 1 0 * X12 0 0 - X12 1 0 = 0 := congrFun (congrFun h_comm_eqs 1) 0
  have h_comm_12 : X12 1 0 * X12 0 1 = 0          := congrFun (congrFun h_comm_eqs 1) 2
  have h_comm_20 : X12 1 0 - X12 1 0 * X12 0 0 = 0 := congrFun (congrFun h_comm_eqs 2) 0
  have h_comm_21 : -(X12 1 0 * X12 0 1) = 0       := congrFun (congrFun h_comm_eqs 2) 1

  -- Using these equations, we get that b₁₁, b₂₂ = 1.
  -- We first need the following lemma, which as we will see is useful in its own right.
  have h_b12_zero_b21_nonzero_or_symm : (X12 0 1 = 0 ∧ X12 1 0 ≠ 0) ∨
                                        (X12 1 0 = 0 ∧ X12 0 1 ≠ 0) := by
    rcases mul_eq_zero.mp h_comm_12 with h21 | h12
    · right
      exact ⟨h21, fun h12_zero => h_diag_gives_contra ⟨h12_zero, h21⟩⟩
    · left
      exact ⟨h12, fun h21_zero => h_diag_gives_contra ⟨h12, h21_zero⟩⟩

  -- This allows us to prove the desired equality b₁₁ = 1.
  have h_b11_eq_1 : X12 0 0 = 1 := by
    rcases h_b12_zero_b21_nonzero_or_symm with ⟨_, h21_nonzero⟩ | ⟨_, h12_nonzero⟩
    · have h_sub : X12 1 0 * (X12 0 0 - 1) = 0 := by
        calc X12 1 0 * (X12 0 0 - 1)
          _ = X12 1 0 * X12 0 0 - X12 1 0 := by ring
          _ = 0 := h_comm_10
      -- Since b₂₁ ≠ 0, it must be that b₁₁ - 1 = 0.
      exact sub_eq_zero.mp ((mul_eq_zero.mp h_sub).resolve_left h21_nonzero)
    · have h_sub : (1 - X12 0 0) * X12 0 1 = 0 := by
        calc (1 - X12 0 0) * X12 0 1
          _ = X12 0 1 - X12 0 0 * X12 0 1 := by ring
          _ = 0 := h_comm_01
      have h_one_sub : 1 - X12 0 0 = 0 := (mul_eq_zero.mp h_sub).resolve_right h12_nonzero
      exact (sub_eq_zero.mp h_one_sub).symm

  -- We therefore are in one of two cases:
  -- Either X₁₂ is x₁₂(b) for nonzero b, or it is x₂₁(c) for nonzero c.
  have h_b22_eq_1 : X12 1 1 = 1 := by rw [← hb11_eq_b22, h_b11_eq_1]
  have h_X12_shape : X12 = !![      1, X12 0 1, 0;
                              X12 1 0,       1, 0;
                                    0,       0, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [h_b11_eq_1, h_b22_eq_1, hb33_eq_1, hX12_02, hX12_12, hX12_20, hX12_21]

  have h_X12_is_specific_transvection :
    (∃ b : F, b ≠ 0 ∧ X12 = !![1, b, 0; 0, 1, 0; 0, 0, 1]) ∨
    (∃ c : F, c ≠ 0 ∧ X12 = !![1, 0, 0; c, 1, 0; 0, 0, 1]) := by
    rcases h_b12_zero_b21_nonzero_or_symm with ⟨hb12_zero, hb21_nonzero⟩ | ⟨hb21_zero, hb12_nonzero⟩
    · right
      exact ⟨X12 1 0, hb21_nonzero, by rw [hb12_zero] at h_X12_shape; exact h_X12_shape⟩
    · left
      exact ⟨X12 0 1, hb12_nonzero, by rw [hb21_zero] at h_X12_shape; exact h_X12_shape⟩

  -- Before embarking on our division into cases,
  -- we first express the image X₂₃ in terms of that of X₁₃.
  -- To do that, first we prove the equality as a simple matrix multiplication (w₁ * x₂₃ = x₁₃ * w₁)
  have h_w1_x23 : w1SL F * x23SL F = x13SL F * w1SL F := by
    have h_mat : w1 F * x23 F = x13 F * w1 F := by
      rw [w1, x23, x13, mul_fin_three, mul_fin_three]
      simp
    apply Subtype.ext h_mat

  -- We now rearrange to get x₂₃ = w₁⁻¹ * x₁₃ * w₁ in SL₃(F).
  have h_w1_inv_x13_w1 : x23SL F = (w1SL F)⁻¹ * x13SL F * w1SL F := by
    calc x23SL F
      _ = (w1SL F)⁻¹ * (w1SL F * x23SL F) := by rw [inv_mul_cancel_left]
      _ = (w1SL F)⁻¹ * (x13SL F * w1SL F) := by rw [h_w1_x23]
      _ = (w1SL F)⁻¹ * x13SL F * w1SL F := by rw [mul_assoc]

  -- Before applying Φ₂ and getting an equality for X₂₃, we first want to realize what w₁⁻¹ is.
  have h_w1_inv : (w1SL F)⁻¹ = w1SL F * d3SL F := by
    have h_mul : w1SL F * (w1SL F * d3SL F) = 1 := by
      have h_mat : w1 F * (w1 F * d3 F) = 1 := by
        rw [w1, d3, diagonal_fin_three, one_fin_three, mul_fin_three, mul_fin_three]
        simp
      apply Subtype.ext h_mat
    rw [mul_eq_one_iff_inv_eq', inv_eq_iff_eq_inv] at h_mul
    exact h_mul.symm

  -- Define X₂₃ as the image under Φ₂.
  let X23 := (φ2 (x23SL F)).val

  -- Map the SL₃ equality through the homomorphism Φ₂ and then down to a matrix equality.
  have h_X23_eq : X23 = (w1 F * d3 F) * X13 * w1 F := by
    have h_img : φ2 (x23SL F) = (w1SL F * d3SL F) * φ2 (x13SL F) * w1SL F := by
      calc φ2 (x23SL F)
        _ = φ2 ((w1SL F)⁻¹ * x13SL F * w1SL F) := by rw [h_w1_inv_x13_w1]
        _ = φ2 ((w1SL F)⁻¹) * φ2 (x13SL F) * φ2 (w1SL F) := by rw [map_mul, map_mul]
        _ = (φ2 (w1SL F))⁻¹ * φ2 (x13SL F) * φ2 (w1SL F) := by rw [map_inv]
        _ = (w1SL F)⁻¹ * φ2 (x13SL F) * w1SL F := by rw [hw1_φ2]
        _ = (w1SL F * d3SL F) * φ2 (x13SL F) * w1SL F := by rw [h_w1_inv]

    have h_img_mat := congrArg Subtype.val h_img
    calc X23
      _ = (φ2 (x23SL F)).val := rfl
      _ = ((w1SL F * d3SL F) * φ2 (x13SL F) * w1SL F).val := h_img_mat
      _ = ((w1SL F * d3SL F) * φ2 (x13SL F)).val * (w1SL F).val := by
        rw [SpecialLinearGroup.coe_mul]
      _ = (w1SL F * d3SL F).val * (φ2 (x13SL F)).val * (w1SL F).val := by
        rw [SpecialLinearGroup.coe_mul]
      _ = ((w1SL F).val * (d3SL F).val) * X13 * (w1SL F).val := by
        rw [SpecialLinearGroup.coe_mul]
      _ = (w1 F * d3 F) * X13 * w1 F := rfl

  -- We can now explicitly calculate the right hand side of the above, yielding the following.
  have h_X23_mat : X23 = !![1,       0, 0;
                            0,       1, X12 0 1;
                            0, X12 1 0, 1] := by
    rw [h_X23_eq, h_X13_mat]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [Matrix.mul_apply, Fin.sum_univ_three] <;>
      simp [w1, d3, of_apply, cons_val, Fin.reduceFinMk, h_b11_eq_1, h_b22_eq_1]

  -- Extract entry equations from the above.
  have hX23_00 : X23 0 0 = 1       := congrFun (congrFun h_X23_mat 0) 0
  have hX23_01 : X23 0 1 = 0       := congrFun (congrFun h_X23_mat 0) 1
  have hX23_02 : X23 0 2 = 0       := congrFun (congrFun h_X23_mat 0) 2
  have hX23_10 : X23 1 0 = 0       := congrFun (congrFun h_X23_mat 1) 0
  have hX23_11 : X23 1 1 = 1       := congrFun (congrFun h_X23_mat 1) 1
  have hX23_12 : X23 1 2 = X12 0 1 := congrFun (congrFun h_X23_mat 1) 2
  have hX23_20 : X23 2 0 = 0       := congrFun (congrFun h_X23_mat 2) 0
  have hX23_21 : X23 2 1 = X12 1 0 := congrFun (congrFun h_X23_mat 2) 1
  have hX23_22 : X23 2 2 = 1       := congrFun (congrFun h_X23_mat 2) 2

  -- We would also like to, before starting the division into cases, show that [X₁₂, X₂₃] = X₁₃.
  -- More precisely, we show that a rearranging of this equation holds.
  -- We start with proving that [x₁₂(1), x₂₃(1)] = x₁₃(1),
  -- and again more precisely x₁₂ * x₂₃ = x₁₃ * x₂₃ * x₁₂.
  have h_x12_x23_comm_rel : x12SL F * x23SL F = x13SL F * x23SL F * x12SL F := by
    have h_mat : x12 F * x23 F = x13 F * x23 F * x12 F := by
      rw [x12, x23, x13, mul_fin_three, mul_fin_three, mul_fin_three]
      simp
    apply Subtype.ext h_mat

  -- We now push this relation through the homomorphism Φ₂ to get the result.
  have h_X12_X23_comm_rel : X12 * X23 = X13 * X23 * X12 := by
    have h_img : φ2 (x12SL F * x23SL F) = φ2 (x13SL F * x23SL F * x12SL F) :=
      congrArg φ2 h_x12_x23_comm_rel
    have h_LHS : (φ2 (x12SL F * x23SL F)).val = X12 * X23 := by
      rw [map_mul, SpecialLinearGroup.coe_mul]
    have h_RHS : (φ2 (x13SL F * x23SL F * x12SL F)).val = X13 * X23 * X12 := by
      rw [map_mul, map_mul, SpecialLinearGroup.coe_mul, SpecialLinearGroup.coe_mul]
    rw [← h_LHS, ← h_RHS, h_img]

  -- Finally, we may start the division into cases.
  rcases h_X12_is_specific_transvection with ⟨b, hb_neq_0, hX12_b⟩ | ⟨c, hc_neq_0, hX12_c⟩

  /-
  ======================================================================
    CASE 1: X₁₂ is x₁₂(b)
  ======================================================================
  In this branch, X₁₂ is already a transvection with the correct position.
  We evaluate the commutator relation X₁₂ * X₂₃ = X₁₃ * X₂₃ * X₁₂ in accordance.
  We evaluate specifically at the entry (0, 2) to extract the algebraic
  relation for b without expanding the full 3x3 matrices.
  -/
  · have h_entry_eq : (X12 * X23) 0 2 = (X13 * X23 * X12) 0 2 := congrFun
      (congrFun h_X12_X23_comm_rel 0) 2

    -- Evaluate the Left Hand Side of the above at (0, 2).
    have h_LHS_eval : (X12 * X23) 0 2 = b * b := by
      simp only [Matrix.mul_apply, Fin.sum_univ_three]
      simp [hX12_b, h_X23_mat, of_apply, cons_val]

    -- Evaluate the Right Hand Side of the above at (0, 2).
    have h_RHS_eval : (X13 * X23 * X12) 0 2 = b := by
      simp only [Matrix.mul_apply, Fin.sum_univ_three]
      simp [hX12_b, h_X13_mat, h_X23_mat, of_apply, cons_val]

    -- By combining these, we deduce the explicit relation b² = b.
    have h_b_sq_eq_b : b * b = b := by rw [← h_LHS_eval, h_entry_eq, h_RHS_eval]

    -- Since F is a field (and thus an integral domain) and b ≠ 0, b² = b uniquely forces b = 1.
    have hb_eq_1 : b = 1 := by
      have h_sub : b * (b - 1) = 0 := by
        calc b * (b - 1)
          _ = b * b - b := by ring
          _ = b - b := by rw [h_b_sq_eq_b]
          _ = 0 := by ring
      have hb_sub_1 : b - 1 = 0 := (mul_eq_zero.mp h_sub).resolve_left hb_neq_0
      exact sub_eq_zero.mp hb_sub_1

    -- Substitute b = 1 back into our shape for X₁₂ to definitively prove X₁₂ = x₁₂(1).
    have h_X12_eq_x12 : X12 = x12 F := by
      rw [hb_eq_1] at hX12_b
      rw [hX12_b, x12]

    -- Convert the matrix equality back to an SL₃ equality mapped by φ₂.
    have h_x12_preserved_φ2 : φ2 (x12SL F) = x12SL F := Subtype.ext h_X12_eq_x12

    -- To complete the existential goal for this case:
    -- X₁₂ is already mapped to itself, so we do not need the contragredient automorphism.
    -- Hence we provide `false` for ε, mapping to the identity automorphism.
    use g, false
    simp only [graphChoiceSL3]
    exact ⟨hd1_φ2, hd2_φ2, hd3_φ2, hw1_φ2, hw2_φ2, h_x12_preserved_φ2⟩

  /-
  ======================================================================
    CASE 2: X₁₂ is x₂₁(c)
  ======================================================================
  In this branch, the change of basis left X₁₂ on the lower diagonal.
  We must extract the constant c, verify c = -1, and deploy the
  contragredient automorphism (invTransposeMap) to restore standardness.
  -/
  · -- We evaluate the commutator relation X₁₂ * X₂₃ = X₁₃ * X₂₃ * X₁₂.
    -- We evaluate specifically at the entry (2, 0) to extract the algebraic relation for c.
    have h_entry_eq : (X12 * X23) 2 0 = (X13 * X23 * X12) 2 0 :=
      congrFun (congrFun h_X12_X23_comm_rel 2) 0

    -- Evaluate the Left Hand Side at (2, 0).
    have h_LHS_eval : (X12 * X23) 2 0 = 0 := by
      simp only [Matrix.mul_apply, Fin.sum_univ_three]
      simp [hX12_c, h_X23_mat, of_apply, cons_val]

    -- Evaluate the Right Hand Side at (2, 0).
    have h_RHS_eval : (X13 * X23 * X12) 2 0 = c * c + c := by
      simp only [Matrix.mul_apply, Fin.sum_univ_three]
      simp [hX12_c, h_X13_mat, h_X23_mat, of_apply, cons_val]
      ring

    -- By combining these, we deduce the relation c² + c = 0.
    have h_c_sq_add_c : c * c + c = 0 := by rw [← h_RHS_eval, ← h_entry_eq, h_LHS_eval]

    -- Since F is a field and c ≠ 0, factoring c(c + 1) = 0 forces c = -1.
    have hc_eq_neg_1 : c = -1 := by
      have h_sub : c * (c + 1) = 0 := by
        calc c * (c + 1)
          _ = c * c + c := by ring
          _ = 0 := h_c_sq_add_c
      have hc_add_1 : c + 1 = 0 := (mul_eq_zero.mp h_sub).resolve_left hc_neq_0
      calc c = c + 1 - 1 := by ring
           _ = 0 - 1 := by rw [hc_add_1]
           _ = -1 := by ring

    -- Substitute c = -1 back into our shape for X₁₂ to prove X₁₂ = x₂₁(-1).
    have h_X12_eq_x21_neg1 : X12 = !![ 1, 0, 0;
                                      -1, 1, 0;
                                       0, 0, 1] := by
      rw [hc_eq_neg_1] at hX12_c
      exact hX12_c

    -- Because X₁₂ = x₂₁(-1), x₁₂(1) does not natively map to itself.
    -- We must compose our current map with the contragredient transformation (Φ₃).
    -- We utilize our prior theorem to securely show that this map preserves d₁, d₂, d₃, w₁, and w₂.
    rcases invTranspose_preserves_d_w F with ⟨h_invT_d1, h_invT_d2, h_invT_d3, h_invT_w1, h_invT_w2⟩

    have h_phi3_d1 : graphChoiceSL3 true (φ2 (d1SL F)) = d1SL F := by rw [hd1_φ2]; exact h_invT_d1
    have h_phi3_d2 : graphChoiceSL3 true (φ2 (d2SL F)) = d2SL F := by rw [hd2_φ2]; exact h_invT_d2
    have h_phi3_d3 : graphChoiceSL3 true (φ2 (d3SL F)) = d3SL F := by rw [hd3_φ2]; exact h_invT_d3
    have h_phi3_w1 : graphChoiceSL3 true (φ2 (w1SL F)) = w1SL F := by rw [hw1_φ2]; exact h_invT_w1
    have h_phi3_w2 : graphChoiceSL3 true (φ2 (w2SL F)) = w2SL F := by rw [hw2_φ2]; exact h_invT_w2

    -- Finally, we apply the contragredient automorphism to X₁₂ = x₂₁(-1) to flip it to x₁₂(1).
    -- We isolate the explicit Matrix inversion away from the opaque SL₃ inversion.
    let x21_pos1_SL : SL3 F := ⟨!![1, 0, 0; 1, 1, 0; 0, 0, 1], by
      simp [Matrix.det_fin_three, of_apply, cons_val]⟩

    -- We prove that the above matrix is the inverse of X12.
    -- As its transpose is x₁₂(1), we will be done.
    have h_mat_mul : !![1, 0, 0; 1, 1, 0; 0, 0, 1] * X12 = 1 := by
      rw [h_X12_eq_x21_neg1]
      ext i j; fin_cases i <;> fin_cases j <;>
        simp only [Matrix.mul_apply] <;>
        simp [Fin.sum_univ_three, of_apply, cons_val, Fin.reduceFinMk]

    have hX12_mul_inv : x21_pos1_SL * φ2 (x12SL F) = 1 := Subtype.ext h_mat_mul
    have hX12_inv : (φ2 (x12SL F))⁻¹ = x21_pos1_SL := mul_eq_one_iff_inv_eq'.mp hX12_mul_inv

    -- We step the goal down to the matrix definitions, apply the known inverse,
    -- and let the transpose physically flip x₂₁(-1) to x₁₂(1).
    have h_phi3_x12 : graphChoiceSL3 true (φ2 (x12SL F)) = x12SL F := by
      change invTransposeMap (φ2 (x12SL F)) = x12SL F
      apply Subtype.ext
      change (((φ2 (x12SL F))⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F).transpose = x12 F
      rw [hX12_inv]
      change (!![1, 0, 0; 1, 1, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) F).transpose = x12 F
      ext i j; fin_cases i <;> fin_cases j <;>
        simp [x12, Matrix.transpose_apply, of_apply, cons_val, Fin.reduceFinMk]

    -- Provide the witness utilizing ε = true to deploy the contragredient automorphism mapping.
    use g, true
    exact ⟨h_phi3_d1, h_phi3_d2, h_phi3_d3, h_phi3_w1, h_phi3_w2, h_phi3_x12⟩


theorem all_xij1_preserved (φ : AutSL3 F) : ∃ (g : GL3 F) (ε : Bool),
      graphChoiceSL3 ε (innerAutSL3byGL3 g (φ (d1SL F))) = d1SL F ∧
      graphChoiceSL3 ε (innerAutSL3byGL3 g (φ (d2SL F))) = d2SL F ∧
      graphChoiceSL3 ε (innerAutSL3byGL3 g (φ (d3SL F))) = d3SL F ∧
      graphChoiceSL3 ε (innerAutSL3byGL3 g (φ (w1SL F))) = w1SL F ∧
      graphChoiceSL3 ε (innerAutSL3byGL3 g (φ (w2SL F))) = w2SL F ∧
      graphChoiceSL3 ε (innerAutSL3byGL3 g (φ (x12SL F))) = x12SL F ∧
      graphChoiceSL3 ε (innerAutSL3byGL3 g (φ (x13SL F))) = x13SL F ∧
      graphChoiceSL3 ε (innerAutSL3byGL3 g (φ (x23SL F))) = x23SL F ∧
      graphChoiceSL3 ε (innerAutSL3byGL3 g (φ (x32SL' F))) = x32SL' F := by
  rcases x12_preserved F φ with ⟨g, ε, ⟨hgd1, hgd2, hgd3, hgw1, hgw2, hgx12⟩⟩
  use g, ε
  have cong_x13 : x13SL F = (w2SL F)⁻¹ * x12SL F * w2SL F := by
    apply Subtype.ext
    simp [x12SL, x13SL, w2SL, x13, x12, w2]
  have cong_x23 : x23SL F = (w1SL F) * (w2SL F) * x12SL F * (w2SL F)⁻¹ * (w1SL F)⁻¹ := by
    apply Subtype.ext
    simp [x12SL, x23SL, w1SL, w2SL, x23, x12, w1, w2]
  have cong_x32 : x32SL' F = (w2SL F) * (w1SL F) * (w2SL F) * x12SL F * (w2SL F)⁻¹ * (w1SL F)⁻¹ * (w2SL F)⁻¹ := by
    apply Subtype.ext
    simp [x12SL, x32SL', w1SL, w2SL, x12, w1, w2]
    rfl
  simp [*]


theorem TransvectionSL3_inv (i j : Fin 3) (x : R) (h : i ≠ j) :
    (TransvectionSL3 i j x h)⁻¹ = TransvectionSL3 i j (-x) h := by
  have : (TransvectionSL3 i j x h) * (TransvectionSL3 i j (-x) h) = 1 := by
    apply Subtype.ext
    simp [TransvectionSL3]
    rw [transvection_mul_transvection_same]
    simp
    exact h
  exact inv_eq_of_mul_eq_one_right this


theorem TransvectionSL3_mul_TransvectionSL3_same {i j : Fin 3} {x y : R} {h : i ≠ j} :
    TransvectionSL3 i j (x+y) h = (TransvectionSL3 i j x h) * (TransvectionSL3 i j y h) := by
  apply Subtype.ext
  simp [TransvectionSL3, transvection_mul_transvection_same i j h]


theorem x12SL.eq_TransvectionSL3 : (x12SL R) = TransvectionSL3 0 1 1 (by simp) := by
  apply Subtype.ext
  simp [x12SL, x12, TransvectionSL3, transvection]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem x13SL.eq_TransvectionSL3 : (x13SL R) = TransvectionSL3 0 2 1 (by simp) := by
  apply Subtype.ext
  simp [x13SL, x13, TransvectionSL3, transvection]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem x23SL.eq_TransvectionSL3 : (x23SL R) = TransvectionSL3 1 2 1 (by simp) := by
  apply Subtype.ext
  simp [x23SL, x23, TransvectionSL3, transvection]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem x32SL.eq_TransvectionSL3 : (x32SL R) = TransvectionSL3 2 1 1 (by simp) := by
  apply Subtype.ext
  simp [x32SL, x32, TransvectionSL3, transvection]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem x32SL'.eq_TransvectionSL3 : (x32SL' R) = TransvectionSL3 2 1 (-1) (by simp) := by
  apply Subtype.ext
  simp [x32SL', x32', TransvectionSL3, transvection]
  ext i j
  fin_cases i <;> fin_cases j <;> simp


theorem transv_comm_transv'
    {R : Type*} [CommRing R]
    (i j k l : Fin 3) (a b : R)
    (hA : i ≠ j) (hB : k ≠ l)
    (h1 : i ≠ l) (h2 : j ≠ k) :
    transvection i j a * transvection k l b =
    transvection k l b * transvection i j a := by
  ext x y
  simp [mul_apply, transvection, single, Fin.sum_univ_three]
  have unequal_pair {u v : Fin 3} (h : u ≠ v) (t : Fin 3): ¬ ( u = t ∧ v = t) :=
      fun ⟨l, r⟩ => h (Eq.trans l r.symm)
  have abba : b * a = a * b := by ring
  have reorder  {a b: R} (i' j' k' l' : Fin 3) :
      (if k = k' ∧ l = l' then (if i = i' ∧ j = j' then a*b else 0) else 0) =
      (if i = i' ∧ j = j' then (if k = k' ∧ l = l' then a*b else 0) else 0)
      := by
    split_ifs
    all_goals simp
  have eliminate  {a b: R} (i' j' k' l' : Fin 3) (hor : i' = l' ∨ j' = k'):
      (if i = i' ∧ j = j' then (if k = k' ∧ l = l' then a*b else 0) else 0) = 0
      := by
    split_ifs <;> rcases hor with il | jk
    any_goals simp
    all_goals
      rename_i h h'
      exfalso
    rw [il] at h
    exact h1 (h.left.trans h'.right.symm)
    rw [jk] at h
    exact h2 (h.right.trans h'.left.symm)
  have eliminate.il  {a b: R} (i' j' k' l' : Fin 3) (hil : i' = l'):
      (if i = i' ∧ j = j' then (if k = k' ∧ l = l' then a*b else 0) else 0) = 0
    := eliminate i' j' k' l' (by left; exact hil)
  have eliminate.jk  {a b: R} (i' j' k' l' : Fin 3) (hjk : j' = k'):
      (if i = i' ∧ j = j' then (if k = k' ∧ l = l' then a*b else 0) else 0) = 0
    := eliminate i' j' k' l' (by right; exact hjk)
  -- Now we only have to normalize order and eliminate every case
  fin_cases x <;>
  fin_cases y <;>
    try simp [
      unequal_pair hA 0, unequal_pair hA 1, unequal_pair hA 2,
      unequal_pair hB 0, unequal_pair hB 1, unequal_pair hB 2,
      abba, zero_mul,
      reorder 0 1 1 0, reorder 0 1 1 2, reorder 0 2 2 0, reorder 0 2 2 1,
      reorder 1 0 0 1, reorder 1 0 0 2, reorder 1 2 2 0, reorder 1 2 2 1,
      reorder 2 0 0 1, reorder 2 0 0 2, reorder 2 1 1 0, reorder 2 1 1 2,
      eliminate.jk 0 1 1 0 rfl, eliminate.jk 0 1 1 2 rfl, eliminate.jk 0 2 2 0 rfl, eliminate.jk 0 2 2 1 rfl,
      eliminate.jk 1 0 0 1 rfl, eliminate.jk 1 0 0 2 rfl, eliminate.jk 1 2 2 0 rfl, eliminate.jk 1 2 2 1 rfl,
      eliminate.jk 2 0 0 1 rfl, eliminate.jk 2 0 0 2 rfl, eliminate.jk 2 1 1 0 rfl, eliminate.jk 2 1 1 2 rfl,
      eliminate.il 0 1 2 0 rfl, eliminate.il 0 2 1 0 rfl, eliminate.il 1 0 2 1 rfl, eliminate.il 1 2 0 1 rfl,
      eliminate.il 2 0 1 2 rfl, eliminate.il 2 1 0 2 rfl
    ]
  --
  all_goals split_ifs <;> rename_i hkl hij
  any_goals simp [one_apply, add_comm]
  --

theorem transv_comm_transv
    {R : Type*} [CommRing R]
    (i j k l : Fin 3) (a b : R)
    (H : i ≠ j ∧  k ≠ l ∧  i ≠ l ∧ j ≠ k) :
    transvection i j a * transvection k l b =
    transvection k l b * transvection i j a := by
  rcases H with ⟨A, B, P, Q⟩
  exact transv_comm_transv' i j k l a b A B P Q


theorem deep_comm {R : Type*} [CommRing R]
    {ε : Bool} {g : GL3 R} {φ : AutSL3 R} : ∀ a b : SL3 R,
    (graphChoiceSL3 ε) ((innerAutSL3byGL3 g) (φ (a * b))) =
    (graphChoiceSL3 ε) ((innerAutSL3byGL3 g) (φ a)) *
    (graphChoiceSL3 ε) ((innerAutSL3byGL3 g) (φ b)) := fun a b => by
  simp [map_mul]

theorem entries_gen {R : Type*} [CommRing R]
    {A B : SL3 R} (h : A = B) :
    ∀ i j : Fin 3, A i j = B i j :=
  have hval : A.val = B.val := by
    exact congr_arg Subtype.val h
  fun i j => congr_fun (congr_fun hval i) j

theorem _cong_comm_mat_helper
    {R : Type*} [CommRing R] [IsDomain R] {Y Z : SL3 R}
    (Y_comm_x12SL : Y * x12SL R = x12SL R * Y)
    (Y_comm_x13SL : Y * x13SL R = x13SL R * Y)
    (Y_comm_x32SL': Y * x32SL' R = x32SL' R * Y)
    (Z_as_cong : Z = (w2SL R)⁻¹ * Y * (w2SL R))
    (Z_as_comm : Z = (x23SL R)⁻¹ * Y * (x23SL R) * Y⁻¹)
    : ∃ (t : R),
      Y.val = !![1, t, 0; 0, 1, 0; 0, 0, 1] ∧
      Z.val = !![1, 0, t; 0, 1, 0; 0, 0, 1]
    := by
  have by_comm_with_E01 : Y 1 0 = 0 ∧ Y 2 0 = 0 ∧ Y 1 2 = 0 ∧ Y 1 1 = Y 0 0
      := by
    have entries := entries_gen Y_comm_x12SL
    have h00 := entries 0 0; have h01 := entries 0 1; have h02 := entries 0 2
    have h10 := entries 1 0; have h11 := entries 1 1; have h12 := entries 1 2
    have h20 := entries 2 0; have h21 := entries 2 1; have h22 := entries 2 2
    simp [x12SL, x12, Matrix.mul_apply, Fin.sum_univ_three] at *
    rw [add_comm] at h01
    have eq := add_left_cancel h01
    exact ⟨h11, h21, h02, eq.symm⟩
  have by_comm_with_E02 : Y 2 1 = 0 ∧ Y 2 2 = Y 0 0
      := by
    have entries := entries_gen Y_comm_x13SL
    have h00 := entries 0 0; have h01 := entries 0 1; have h02 := entries 0 2
    have h10 := entries 1 0; have h11 := entries 1 1; have h12 := entries 1 2
    have h20 := entries 2 0; have h21 := entries 2 1; have h22 := entries 2 2
    simp [x13SL, x13, Matrix.mul_apply, Fin.sum_univ_three] at *
    rw [add_comm] at h02
    have eq := add_left_cancel h02
    exact ⟨h01, eq.symm⟩
  have by_comm_with_E21 : Y 0 2 = 0
      := by
    have entries := entries_gen Y_comm_x32SL'
    have h00 := entries 0 0; have h01 := entries 0 1; have h02 := entries 0 2
    have h10 := entries 1 0; have h11 := entries 1 1; have h12 := entries 1 2
    have h20 := entries 2 0; have h21 := entries 2 1; have h22 := entries 2 2
    simp [x32SL', x32', Matrix.mul_apply, Fin.sum_univ_three] at *
    exact h01
  have h_w2_inv : (w2SL R)⁻¹ = w2SL R * d1SL R := by
    have h_mul : w2SL R * (w2SL R * d1SL R) = 1 := by
      have h_mat : w2 R * (w2 R * d1 R) = 1 := by
        rw [w2, d1, diagonal_fin_three, one_fin_three, mul_fin_three, mul_fin_three]
        simp
      apply Subtype.ext h_mat
    rw [mul_eq_one_iff_inv_eq', inv_eq_iff_eq_inv] at h_mul
    exact h_mul.symm
  have hY : Y.val = !![Y 0 0, Y 0 1, 0; 0, Y 0 0, 0; 0, 0, Y 0 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [by_comm_with_E01, by_comm_with_E02, by_comm_with_E21]
  have hZ : Z.val = !![Y 0 0, 0, Y 0 1; 0, Y 0 0, 0; 0, 0, Y 0 0] := by
    rw [h_w2_inv] at Z_as_cong
    have entries := entries_gen Z_as_cong
    have h00 := entries 0 0; have h01 := entries 0 1; have h02 := entries 0 2
    have h10 := entries 1 0; have h11 := entries 1 1; have h12 := entries 1 2
    have h20 := entries 2 0; have h21 := entries 2 1; have h22 := entries 2 2
    simp [w2SL, d1SL, w2, d1, diagonal, vecHead, vecTail, vecMul, dotProduct,
          by_comm_with_E01, by_comm_with_E02, by_comm_with_E21,
          Matrix.mul_apply, Fin.sum_univ_three] at *
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h00, h01, h02, h10, h11, h11, h12, h20, h21, h22]
  have two_sides := Z_as_cong.symm.trans Z_as_comm
  have diagonal_is_one : Y 0 0 = 1 := by
    have : x23SL R * Z * Y = Y * x23SL R := by
      rw [Z_as_comm]
      group
    have eq := congrArg Subtype.val this
    simp [x23SL, x23] at eq
    rw [hY, hZ] at eq
    simp at eq
    have hmul : Y 0 0 * (Y 0 0 - 1) = 0 := by
      have := eq.right
      ring_nf at this
      ring_nf
      simp [this]
    rcases mul_eq_zero.mp hmul with h | h
    exfalso
    have hdet := Y.2
    rw [hY] at hdet
    simp [Matrix.det_fin_three, h] at hdet
    exact sub_eq_zero.mp h
  rw [diagonal_is_one] at hY
  rw [diagonal_is_one] at hZ
  use Y 0 1


theorem transvection_12_preserved (φ : AutSL3 F) :
    ∃ (g : GL3 F) (ε : Bool),
      graphChoiceSL3 ε (innerAutSL3byGL3 g (φ (d1SL F))) = d1SL F ∧
      graphChoiceSL3 ε (innerAutSL3byGL3 g (φ (d2SL F))) = d2SL F ∧
      graphChoiceSL3 ε (innerAutSL3byGL3 g (φ (d3SL F))) = d3SL F ∧
      graphChoiceSL3 ε (innerAutSL3byGL3 g (φ (w1SL F))) = w1SL F ∧
      graphChoiceSL3 ε (innerAutSL3byGL3 g (φ (w2SL F))) = w2SL F ∧
      graphChoiceSL3 ε (innerAutSL3byGL3 g (φ (x12SL F))) = x12SL F ∧
      graphChoiceSL3 ε (innerAutSL3byGL3 g (φ (x13SL F))) = x13SL F ∧
      graphChoiceSL3 ε (innerAutSL3byGL3 g (φ (x23SL F))) = x23SL F ∧
      graphChoiceSL3 ε (innerAutSL3byGL3 g (φ (x32SL' F))) = x32SL' F ∧
    ∀ (u : F), ∃ (u' : F),
    (graphChoiceSL3 ε) ((innerAutSL3byGL3 g)
      (φ (TransvectionSL3 0 1 u (by simp)))) = (TransvectionSL3 0 1 u' (by simp))
    := by
  rcases all_xij1_preserved F φ with ⟨g, ε, ⟨hd1, hd2, hd3, hw1, hw2, hx12, hx13, hx23, hx32'⟩⟩
  use g, ε
  simp [*]
  intro u
  set Y := (graphChoiceSL3 ε) ((innerAutSL3byGL3 g) (φ (TransvectionSL3 0 1 u (by simp)))) with Y.def
  set Z := (graphChoiceSL3 ε) ((innerAutSL3byGL3 g) (φ (TransvectionSL3 0 2 u (by simp)))) with Z.def
  have Z_as_cong : Z = (w2SL F)⁻¹ * Y * (w2SL F) := by
    have pre_eq : (TransvectionSL3 0 2 u (by simp)) =
        (w2SL F)⁻¹ * (TransvectionSL3 0 1 u (by simp)) * (w2SL F) := by
      apply Subtype.ext
      simp [w2SL, w2, TransvectionSL3, transvection, single, mul_add, vecHead, vecTail]
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    simp only [Z, Y, pre_eq, deep_comm, map_inv, hw2]
  have Z_as_comm: Z = (x23SL F)⁻¹ * Y * (x23SL F) * Y⁻¹ := by
    have pre_eq : (TransvectionSL3 0 2 u (by simp)) =
        (x23SL F)⁻¹ * (TransvectionSL3 0 1 u (by simp)) * (x23SL F) * (TransvectionSL3 0 1 u (by simp))⁻¹
        := by
      simp only [x23SL.eq_TransvectionSL3, TransvectionSL3_inv]
      apply Subtype.ext
      simp [TransvectionSL3, transvection, single, mul_add]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [of_apply, add_apply, mul_apply, Fin.sum_univ_three]
    have := congr_arg (fun M => (graphChoiceSL3 ε) ((innerAutSL3byGL3 g) (φ M)) ) pre_eq
    simp at this
    rw [hx23] at this
    simp only [Z, Y]
    exact this
  have Y_comm_x12SL : Y * x12SL F = x12SL F * Y := by
    have pre_comm :
        (TransvectionSL3 0 1 u (by simp)) * x12SL F =
        x12SL F * (TransvectionSL3 0 1 u (by simp)) := by
      apply Subtype.ext
      simp [x12SL.eq_TransvectionSL3, TransvectionSL3]
      exact transv_comm_transv 0 1 0 1 u 1 (by simp)
    rw [<-hx12]
    simp [Y]
    rw [<-deep_comm, <-deep_comm, pre_comm]
  have Y_comm_x13SL : Y * x13SL F = x13SL F * Y := by
    have pre_comm :
        (TransvectionSL3 0 1 u (by simp)) * x13SL F =
        x13SL F * (TransvectionSL3 0 1 u (by simp)) := by
      apply Subtype.ext
      simp [x13SL.eq_TransvectionSL3, TransvectionSL3]
      exact transv_comm_transv 0 1 0 2 u 1 (by simp)
    rw [<-hx13]
    simp [Y]
    rw [<-deep_comm, <-deep_comm, pre_comm]
  have Y_comm_x32SL' : Y * (x32SL' F) = (x32SL' F) * Y := by
    have pre_comm :
        (TransvectionSL3 0 1 u (by simp)) * x32SL' F =
        x32SL' F * (TransvectionSL3 0 1 u (by simp)) := by
      apply Subtype.ext
      simp [x32SL'.eq_TransvectionSL3, TransvectionSL3]
      exact transv_comm_transv 0 1 2 1 u (-1) (by simp)
    rw [<-hx32']
    simp [Y]
    rw [<-deep_comm, <-deep_comm, pre_comm]
  rcases _cong_comm_mat_helper
      Y_comm_x12SL
      Y_comm_x13SL
      Y_comm_x32SL'
      Z_as_cong
      Z_as_comm
    with ⟨t, hY, hZ⟩
  use t
  apply Subtype.ext
  simp [TransvectionSL3, transvection, single]
  ext i j
  fin_cases i <;> fin_cases j <;> rw [hY] <;> simp


theorem transvection_12_preserved_unique_and_on (φ : AutSL3 F) :
    ∃ (g : GL3 F) (ε : Bool),
      graphChoiceSL3 ε (innerAutSL3byGL3 g (φ (d1SL F))) = d1SL F ∧
      graphChoiceSL3 ε (innerAutSL3byGL3 g (φ (d2SL F))) = d2SL F ∧
      graphChoiceSL3 ε (innerAutSL3byGL3 g (φ (d3SL F))) = d3SL F ∧
      graphChoiceSL3 ε (innerAutSL3byGL3 g (φ (w1SL F))) = w1SL F ∧
      graphChoiceSL3 ε (innerAutSL3byGL3 g (φ (w2SL F))) = w2SL F ∧
      graphChoiceSL3 ε (innerAutSL3byGL3 g (φ (x12SL F))) = x12SL F ∧
      graphChoiceSL3 ε (innerAutSL3byGL3 g (φ (x13SL F))) = x13SL F ∧
      graphChoiceSL3 ε (innerAutSL3byGL3 g (φ (x23SL F))) = x23SL F ∧
      graphChoiceSL3 ε (innerAutSL3byGL3 g (φ (x32SL' F))) = x32SL' F ∧
    (∀ (u : F), ∃! (u' : F),
    (graphChoiceSL3 ε) ((innerAutSL3byGL3 g)
      (φ (TransvectionSL3 0 1 u (by simp)))) = (TransvectionSL3 0 1 u' (by simp)))
    ∧ (∀ (u' : F), ∃! (u : F),
    (graphChoiceSL3 ε) ((innerAutSL3byGL3 g)
      (φ (TransvectionSL3 0 1 u (by simp)))) = (TransvectionSL3 0 1 u' (by simp)))
    := by
  rcases transvection_12_preserved F φ with
      ⟨g, ε, hd1, hd2, hd3, hw1, hw2, hx12, hx13, hx23, hx32', find⟩
  use g, ε
  simp [*]
  constructor
  -- u -> u'
  intro u
  rcases find u with ⟨u', hu'⟩
  use u'
  simp [hu']
  intro v' h
  have := congr_arg (fun M : SL3 F => (M : SL3 F) 0 1) h
  simp [TransvectionSL3, transvection] at this
  exact this.symm
  -- u' -> u
  intro b
  have hbij : Function.Bijective (fun E =>
      (graphChoiceSL3 ε) ((innerAutSL3byGL3 g) (φ E))) := by
    apply Function.Bijective.comp
    exact (graphChoiceSL3 ε).bijective
    apply Function.Bijective.comp
    exact (innerAutSL3byGL3 g).bijective
    exact φ.bijective
  rcases hbij.surjective (TransvectionSL3 0 1 b (by simp)) with ⟨Y, hY⟩
  rcases hbij.surjective (TransvectionSL3 0 2 b (by simp)) with ⟨Z, hZ⟩
  simp at hY
  simp at hZ
  have Z_as_cong : Z = (w2SL F)⁻¹ * Y * (w2SL F) := by
    have pre_eq : (TransvectionSL3 0 2 b (by simp)) =
      (w2SL F)⁻¹ * (TransvectionSL3 0 1 b (by simp)) * (w2SL F) := by
      apply Subtype.ext
      simp [w2SL, w2, TransvectionSL3, transvection, single, mul_add, vecHead, vecTail]
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    rw [<-hY, <-hZ, <-hw2,
        <-map_inv, <-map_inv, <-map_inv,
        <-deep_comm, <-deep_comm] at pre_eq
    exact hbij.injective pre_eq
  have Z_as_comm: Z = (x23SL F)⁻¹ * Y * (x23SL F) * Y⁻¹ := by
    have pre_eq : (TransvectionSL3 0 2 b (by simp)) =
        (x23SL F)⁻¹ * (TransvectionSL3 0 1 b (by simp)) * (x23SL F) * (TransvectionSL3 0 1 b (by simp))⁻¹
        := by
      simp only [x23SL.eq_TransvectionSL3, TransvectionSL3_inv]
      apply Subtype.ext
      simp [TransvectionSL3, transvection, single, mul_add]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [of_apply, add_apply, mul_apply, Fin.sum_univ_three]
    rw [<-hY, <-hZ, <-hx23,
        <-map_inv, <-map_inv, <-map_inv, <-map_inv, <-map_inv, <-map_inv,
        <-deep_comm, <-deep_comm, <-deep_comm] at pre_eq
    exact hbij.injective pre_eq
  have Y_comm_x12SL : Y * x12SL F = x12SL F * Y := by
    have pre_comm :
        (TransvectionSL3 0 1 b (by simp)) * x12SL F =
        x12SL F * (TransvectionSL3 0 1 b (by simp)) := by
      apply Subtype.ext
      simp [x12SL.eq_TransvectionSL3, TransvectionSL3]
      exact transv_comm_transv 0 1 0 1 b 1 (by simp)
    rw [<-hY, <-hx12, <-deep_comm, <-deep_comm] at pre_comm
    exact hbij.injective pre_comm
  have Y_comm_x13SL : Y * x13SL F = x13SL F * Y := by
    have pre_comm :
        (TransvectionSL3 0 1 b (by simp)) * x13SL F =
        x13SL F * (TransvectionSL3 0 1 b (by simp)) := by
      apply Subtype.ext
      simp [x13SL.eq_TransvectionSL3, TransvectionSL3]
      exact transv_comm_transv 0 1 0 2 b 1 (by simp)
    rw [<-hY, <-hx13, <-deep_comm, <-deep_comm] at pre_comm
    exact hbij.injective pre_comm
  have Y_comm_x32SL' : Y * (x32SL' F) = (x32SL' F) * Y := by
    have pre_comm :
        (TransvectionSL3 0 1 b (by simp)) * x32SL' F =
        x32SL' F * (TransvectionSL3 0 1 b (by simp)) := by
      apply Subtype.ext
      simp [x32SL'.eq_TransvectionSL3, TransvectionSL3]
      exact transv_comm_transv 0 1 2 1 b (-1) (by simp)
    rw [<-hY, <-hx32', <-deep_comm, <-deep_comm] at pre_comm
    exact hbij.injective pre_comm
  rcases _cong_comm_mat_helper
      Y_comm_x12SL
      Y_comm_x13SL
      Y_comm_x32SL'
      Z_as_cong
      Z_as_comm
    with ⟨t, Ymat, Zmat⟩
  use t
  simp
  have Y_as_transv : Y = TransvectionSL3 0 1 t (by simp) := by
    apply Subtype.ext
    simp [TransvectionSL3, transvection, single]
    ext i j
    fin_cases i <;> fin_cases j <;> rw [Ymat] <;> simp
  constructor
  rw [<-Y_as_transv]
  exact hY
  -- UNIQNESS
  intro y' hy'
  have : TransvectionSL3 0 1 y' (by simp) = Y :=
    hbij.injective (hy'.trans hY.symm)
  have := entries_gen this 0 1
  simp [TransvectionSL3, transvection, single, of_apply, Ymat] at this
  exact this


-- Due to large amount  of exact cases
set_option maxHeartbeats 250000 in
theorem transvections_preserved_unique (φ : AutSL3 F) :
    ∃ (g : GL3 F) (ε : Bool),
      graphChoiceSL3 ε (innerAutSL3byGL3 g (φ (d1SL F))) = d1SL F ∧
      graphChoiceSL3 ε (innerAutSL3byGL3 g (φ (d2SL F))) = d2SL F ∧
      graphChoiceSL3 ε (innerAutSL3byGL3 g (φ (d3SL F))) = d3SL F ∧
      graphChoiceSL3 ε (innerAutSL3byGL3 g (φ (w1SL F))) = w1SL F ∧
      graphChoiceSL3 ε (innerAutSL3byGL3 g (φ (w2SL F))) = w2SL F ∧
      graphChoiceSL3 ε (innerAutSL3byGL3 g (φ (x12SL F))) = x12SL F ∧
      graphChoiceSL3 ε (innerAutSL3byGL3 g (φ (x13SL F))) = x13SL F ∧
      graphChoiceSL3 ε (innerAutSL3byGL3 g (φ (x23SL F))) = x23SL F ∧
      graphChoiceSL3 ε (innerAutSL3byGL3 g (φ (x32SL' F))) = x32SL' F ∧
    ∃ (f : F → F), Function.Bijective f ∧ ∀ (i j : Fin 3) (u : F) (h : i ≠ j),
    (graphChoiceSL3 ε) ((innerAutSL3byGL3 g)
      (φ (TransvectionSL3 i j u h))) = (TransvectionSL3 i j (f u) h)
    := by
  rcases transvection_12_preserved_unique_and_on F φ with
      ⟨g, ε, hd1, hd2, hd3, hw1, hw2, hx12, hx13, hx23, hx32', find, find'⟩
  use g, ε
  simp [*]
  set f := fun u => (find u).choose with f.def
  have hf : ∀ u, (graphChoiceSL3 ε) ((innerAutSL3byGL3 g) (φ (TransvectionSL3 0 1 u (by simp)))) =
      TransvectionSL3 0 1 (f u) (by simp) := by
    intro u
    -- Idk how it works
    exact (find u).choose_spec.1
  use f
  constructor
  -- Bijectivety
  apply (Function.bijective_iff_existsUnique f).mpr
  intro b
  rcases find' b with ⟨a, hA, uniqA⟩
  use a
  simp
  constructor
  have := entries_gen (hA.symm.trans (hf a)) 0 1
  simp [TransvectionSL3, transvection, single, of_apply] at this
  exact this.symm
  intro y hy
  have hY := hf y
  rw [hy] at hY
  have := uniqA y
  simp at this
  exact this hY
  -- Preserves transvections
  intro i j u neq
  have hu := hf u
  fin_cases i <;> fin_cases j <;> simp at neq <;> simp
  -- Case 0 1
  · exact hu
  -- Case 0 2
  · have conj : ∀ (c : F), TransvectionSL3 0 2 c (by simp)
        = (w2SL F)⁻¹ * (TransvectionSL3 0 1 c (by simp)) * (w2SL F)
        := by
      intro c
      ext i j
      simp only [TransvectionSL3, transvection, single, w2SL, w2]
      fin_cases i <;> fin_cases j
        <;> simp [vecMul, vecHead, vecTail, mul_apply, Fin.sum_univ_three, one_apply]
    simp [conj, hf, hw2]
  -- Case 1 0
  · have conj : ∀ (c : F), TransvectionSL3 1 0 c (by simp)
        = (w1SL F)⁻¹ * (TransvectionSL3 0 1 (c) (by simp))⁻¹ * (w1SL F)
        := by
      intro c
      ext i j
      simp only [TransvectionSL3, transvection, single, w1SL, w1]
      fin_cases i <;> fin_cases j
        <;> simp [vecMul, vecHead, vecTail, mul_apply, Fin.sum_univ_three, adjugate_fin_three]
    simp [conj, hf, hw1]
  -- Case 1 2
  · have conj : ∀ (c : F), TransvectionSL3 1 2 c (by simp)
        = (w1SL F) * (w2SL F) * (TransvectionSL3 0 1 (c) (by simp)) * (w2SL F)⁻¹ * (w1SL F)⁻¹
        := by
      intro c
      ext i j
      simp only [TransvectionSL3, transvection, single, w1SL, w1, w2SL, w2]
      fin_cases i <;> fin_cases j
        <;> simp [vecMul, vecHead, vecTail, mul_apply, Fin.sum_univ_three, one_apply]
    simp [conj, hf, hw1, hw2]
  -- Case 2 0
  · have conj : ∀ (c : F), TransvectionSL3 2 0 c (by simp)
        = (w2SL F) * (w1SL F) * (TransvectionSL3 0 1 (c) (by simp)) * (w1SL F)⁻¹ * (w2SL F)⁻¹
        := by
      intro c
      ext i j
      simp only [TransvectionSL3, transvection, single, w1SL, w1, w2SL, w2]
      fin_cases i <;> fin_cases j
        <;> simp [vecMul, vecHead, vecTail, mul_apply, Fin.sum_univ_three, one_apply]
    simp [conj, hf, hw1, hw2]
  -- Case 2 1
  · have conj : ∀ (c : F), TransvectionSL3 2 1 c (by simp)
        = (w1SL F) * (w2SL F)⁻¹ * (w1SL F)
          * (TransvectionSL3 0 1 (c) (by simp))
          * (w1SL F)⁻¹ * (w2SL F) * (w1SL F)⁻¹
        := by
      intro c
      ext i j
      simp only [TransvectionSL3, transvection, single, w1SL, w1, w2SL, w2]
      fin_cases i <;> fin_cases j
        <;> simp [vecMul, vecHead, vecTail, mul_apply, Fin.sum_univ_three, one_apply]
    simp [conj, hf, hw1, hw2]


theorem transv_to_transv_same_coeff_F (φ : AutSL3 (F)) :
    ∃ (g : GL3 F) (ε : Bool) (σ: F ≃+* F), ∀ (E : SL3 F), (IsTransvectionSL3 E)
    → (graphChoiceSL3 ε) ((innerAutSL3byGL3 g) (φ E)) = E.map σ := by
  rcases transvections_preserved_unique F φ with
      ⟨g, ε, hd1, hd2, hd3, hw1, hw2, hx12, hx13, hx23, hx32', f, hbij, hf⟩
  use g, ε
  have one_as_transvection01 : (1:SL3 F) = TransvectionSL3 0 1 0 (by simp) := by
    apply Subtype.ext
    simp [TransvectionSL3]
  have zero_preserved : f 0 = 0 := by
    have h := hf 0 1 0 (by simp)
    simp [<-one_as_transvection01] at h
    have := congr_arg (fun M : SL3 F => (M : SL3 F) 0 1) h.symm
    simp [TransvectionSL3, transvection] at this
    exact this
  have one_preserved : f 1 = 1 := by
    have h := hf 0 1 1 (by simp)
    rw [<-x12SL.eq_TransvectionSL3, hx12] at h
    have := congr_arg (fun M : SL3 F => (M : SL3 F) 0 1) h.symm
    simp [TransvectionSL3, transvection, x12SL, x12] at this
    exact this
  have add_preserved : ∀ a b, f (a+b) = f a + f b := by
    intro a b
    have hab := hf 0 1 (a+b) (by simp)
    have ha := hf 0 1 a (by simp)
    have hb := hf 0 1 b (by simp)
    rw [TransvectionSL3_mul_TransvectionSL3_same, deep_comm] at hab
    simp [ha, hb] at hab
    rw [<-TransvectionSL3_mul_TransvectionSL3_same] at hab
    have := congr_arg (fun M : SL3 F => (M : SL3 F) 0 1) hab.symm
    simp [TransvectionSL3, transvection] at this
    exact this
  have mul_preserved : ∀ a b, f (a*b) = f a * f b := by
    intro a b
    have ha := hf 0 1 a (by simp)
    have hb := hf 1 2 b (by simp)
    have hab := hf 0 2 (a*b) (by simp)
    have commutator (x y : F) : TransvectionSL3 0 2 (x*y) (by simp) =
        (TransvectionSL3 0 1 x (by simp)) * (TransvectionSL3 1 2 y (by simp))
        * (TransvectionSL3 0 1 x (by simp))⁻¹ * (TransvectionSL3 1 2 y (by simp))⁻¹
        := by
      simp [TransvectionSL3_inv]
      simp [TransvectionSL3, transvection]
      ext i j
      fin_cases i <;> fin_cases j
        <;> simp [mul_apply, Fin.sum_univ_three, one_apply]
    simp [commutator a b, ha, hb] at hab
    rw [<-commutator (f a) (f b)] at hab
    have := congr_arg (fun M : SL3 F => (M : SL3 F) 0 2) hab.symm
    simp [TransvectionSL3, transvection] at this
    exact this
  set fHom : F →+* F := {
      toFun    := f
      map_zero' := zero_preserved
      map_one'  := one_preserved
      map_add'  := add_preserved
      map_mul'  := mul_preserved
    } with fHom.def
  set fIso : F ≃+* F := RingEquiv.ofBijective fHom hbij with fIso.def
  have hfIso : ∀ c, fIso c = f c := by
    intro c
    simp [fIso.def, fHom.def]
  use fIso
  intro E hE
  rcases hE with ⟨i, j, c, inej, hE⟩
  rw [hE, hf i j c inej]
  simp [TransvectionSL3, transvection, single, SpecialLinearGroup.map]
  fin_cases i <;> fin_cases j
    <;> simp at inej
    <;> simp at hE
    <;> simp
    <;> ext i j
    <;> fin_cases i
      <;> fin_cases j
      <;> simp [hfIso, one_preserved, zero_preserved]


theorem field_class (φ : AutSL3 F) :
    ∃ (σ : F ≃+* F) (ε : Bool) (g : GL (Fin 3) F),
      ∀ (x : SL3 F),
        φ x = (innerAutSL3byGL3 g) ((graphChoiceSL3 ε) (x.map σ))
    := by
  rcases transv_to_transv_same_coeff_F F φ with ⟨g, ε, σ, trans2trans⟩
  use σ, ε, g⁻¹
  intro M
  have hM : M ∈ (⊤ : Subgroup (SL3 F)) := Subgroup.mem_top M
  rw [<-SL3_generated_by_transvections] at hM
  have inner_inverse : (innerAutSL3byGL3 g)⁻¹ = (innerAutSL3byGL3 g⁻¹) := by
    ext A i j
    simp [innerAutSL3byGL3]
  have graph_involution : (graphChoiceSL3 ε)⁻¹ = graphChoiceSL3 (R:=F) ε := by
    ext A i j
    cases ε <;> simp [graphChoiceSL3, invTransposeAutSL3]
  refine Subgroup.closure_induction ?_ ?_ ?_ ?_ hM
  · intro A hA
    simp [TransvectionSetSL3, IsTransvectionSL3] at hA
    rcases (by exact hA) with ⟨i, j, c, neq, asTransvection⟩
    have mapped := trans2trans A hA
    apply (innerAutSL3byGL3 g).injective
    simp [<-inner_inverse]
    apply (graphChoiceSL3 ε).injective
    nth_rw 2 [<-graph_involution]
    simp
    exact mapped
  · simp
  · intro A B hA hB mapA mapB
    simp [mapA, mapB]
  · intro A hA mapA
    simp [map_inv, mapA]


end FieldAutomorpisms
