import Final_Project.cong_subgroup
import Final_Project.field_aut
import Final_Project.local_aut
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.Tactic

set_option warningAsError false


open Matrix BigOperators CongruenceSubgroup
open scoped MatrixGroups

noncomputable section

/-
Part 2 of the project.
-/
namespace ResidueReduction

variable (R : Type*) [CommRing R] [IsLocalRing R] [Invertible (2 : R)]

abbrev k : Type _ := CongruenceSubgroup.k R
abbrev reduction : SL3 R →* SL3 (k R) := CongruenceSubgroup.ρ R
abbrev reductionKernel : Subgroup (SL3 R) := CongruenceSubgroup.N R
abbrev QuotSL3 : Type _ := SL3 R ⧸ reductionKernel R

instance reductionKernelNormal : (reductionKernel R).Normal := by
  dsimp [reductionKernel, CongruenceSubgroup.N]
  infer_instance

noncomputable instance residueInvertibleTwo : Invertible (2 : k R) := by
  let h : Invertible ((IsLocalRing.residue R) (2 : R)) :=
    Invertible.map (IsLocalRing.residue R) (2 : R)
  exact h.copy (2 : k R) ((map_ofNat (IsLocalRing.residue R) 2).symm)

theorem reductionKernel_characteristic :
    (reductionKernel R).Characteristic :=
  CongruenceSubgroup.N_characteristic R

/-- Step 2.1: descend an automorphism through the characteristic kernel. -/
def inducedQuotientAut (φ : AutSL3 R) : QuotSL3 R ≃* QuotSL3 R := by
  classical
  have hchar : ∀ ψ : AutSL3 R,
      reductionKernel R ≤ (reductionKernel R).comap ψ.toMonoidHom :=
    Subgroup.characteristic_iff_le_comap.mp (reductionKernel_characteristic R)
  let f : QuotSL3 R →* QuotSL3 R :=
    QuotientGroup.map _ _ φ.toMonoidHom (hchar φ)
  let g : QuotSL3 R →* QuotSL3 R :=
    QuotientGroup.map _ _ φ.symm.toMonoidHom (hchar φ.symm)
  have hgf : ∀ x, g (f x) = x := fun x =>
    QuotientGroup.induction_on x (fun a => by simp [f, g])
  have hfg : ∀ x, f (g x) = x := fun x =>
    QuotientGroup.induction_on x (fun a => by simp [f, g])
  refine MulEquiv.ofBijective f
    ⟨fun a b hab => ?_, fun b => ⟨g b, hfg b⟩⟩
  calc
    a = g (f a) := (hgf a).symm
    _ = g (f b) := by rw [hab]
    _ = b := hgf b

/-- Step 2.2: first-isomorphism-theorem identification with the residue group. -/
def quotientResidueEquiv : QuotSL3 R ≃* SL3 (k R) := by
  classical
  have hsurj : Function.Surjective (reduction R) := by
    intro y
    have hy : y ∈ CongruenceSubgroup.E3 (k R) := by
      rw [CongruenceSubgroup.SL3_generated_by_transvections (k R)]
      simp
    have hE : CongruenceSubgroup.E3 (k R) ≤ MonoidHom.range (reduction R) := by
      change Subgroup.closure (CongruenceSubgroup.TransvectionSetSL3 (k R)) ≤
        MonoidHom.range (reduction R)
      apply (Subgroup.closure_le (MonoidHom.range (reduction R))).2
      intro z hz
      rcases hz with ⟨i, j, hij, a, rfl⟩
      rcases IsLocalRing.residue_surjective a with ⟨r, hr⟩
      refine ⟨CongruenceSubgroup.transvectionSL3 R i j hij r, ?_⟩
      apply Subtype.ext
      ext p q
      change (IsLocalRing.residue R) ((Matrix.transvection i j r) p q) =
        (Matrix.transvection i j a) p q
      simp [Matrix.transvection, Matrix.one_apply, Matrix.single_apply, hr]
      by_cases hs : i = p ∧ j = q <;> simp [hs, hr]
    exact hE hy
  exact QuotientGroup.quotientKerEquivOfSurjective (reduction R) hsurj

/-- The automorphism induced on `SL₃(k)`. -/
def inducedResidueAut (φ : AutSL3 R) : AutSL3 (k R) := by
  classical
  exact (quotientResidueEquiv R).symm.trans
    ((inducedQuotientAut R φ).trans (quotientResidueEquiv R))

theorem inducedResidueAut_commutes (φ : AutSL3 R) (x : SL3 R) :
    inducedResidueAut R φ (reduction R x) = reduction R (φ x) := by
  classical
  change quotientResidueEquiv R
      (inducedQuotientAut R φ
        ((quotientResidueEquiv R).symm (reduction R x))) = reduction R (φ x)
  have hx :
      (quotientResidueEquiv R).symm (reduction R x) =
        QuotientGroup.mk' (reductionKernel R) x := by
    apply (quotientResidueEquiv R).injective
    rw [(quotientResidueEquiv R).apply_symm_apply]
    change reduction R x = QuotientGroup.kerLift (reduction R)
      (QuotientGroup.mk' (reductionKernel R) x)
    exact (QuotientGroup.kerLift_mk (reduction R) x).symm
  rw [hx]
  have hmap :
      inducedQuotientAut R φ (QuotientGroup.mk' (reductionKernel R) x) =
        QuotientGroup.mk' (reductionKernel R) (φ x) := by
    simp [inducedQuotientAut]
  rw [hmap]
  change QuotientGroup.kerLift (reduction R)
      (QuotientGroup.mk' (reductionKernel R) (φ x)) = reduction R (φ x)
  exact QuotientGroup.kerLift_mk (reduction R) (φ x)

/-- Entrywise formulation of a chosen lift. -/
def GL3ReducesTo (g : GL3 R) (B : GL3 (k R)) : Prop :=
  ∀ i j : Fin 3,
    IsLocalRing.residue R ((g : Matrix (Fin 3) (Fin 3) R) i j) =
      (B : Matrix (Fin 3) (Fin 3) (k R)) i j

/--
Step 2.3: lift the field-level conjugating matrix from `GL₃(k)` to `GL₃(R)`.
This uses locality: if the determinant is nonzero modulo `J`, its lift is a unit.
-/
private noncomputable def liftGL3FromResidueMatrix (B : GL3 (k R)) :
    Matrix (Fin 3) (Fin 3) R :=
  fun i j => (IsLocalRing.residue_surjective ((B : Matrix (Fin 3) (Fin 3) (k R)) i j)).choose

omit [Invertible (2 : R)] in
private theorem liftGL3FromResidueMatrix_spec (B : GL3 (k R)) (i j : Fin 3) :
    IsLocalRing.residue R (liftGL3FromResidueMatrix R B i j) =
      (B : Matrix (Fin 3) (Fin 3) (k R)) i j :=
  (IsLocalRing.residue_surjective ((B : Matrix (Fin 3) (Fin 3) (k R)) i j)).choose_spec

omit [Invertible (2 : R)] in
private theorem liftGL3FromResidueMatrix_det_unit (B : GL3 (k R)) :
    IsUnit (liftGL3FromResidueMatrix R B).det := by
  have hdet : IsLocalRing.residue R (liftGL3FromResidueMatrix R B).det =
      (B : Matrix (Fin 3) (Fin 3) (k R)).det := by
    have hmap : (IsLocalRing.residue R).mapMatrix (liftGL3FromResidueMatrix R B) =
        (B : Matrix (Fin 3) (Fin 3) (k R)) := by
      ext i j
      exact liftGL3FromResidueMatrix_spec R B i j
    rw [RingHom.map_det, hmap]
  rw [← IsLocalRing.notMem_maximalIdeal, ← IsLocalRing.residue_eq_zero_iff, hdet]
  exact (Matrix.isUnits_det_units B).ne_zero

def liftGL3FromResidue (B : GL3 (k R)) : GL3 R :=
  Matrix.GeneralLinearGroup.mk'' (liftGL3FromResidueMatrix R B)
    (liftGL3FromResidueMatrix_det_unit R B)

omit [Invertible (2 : R)] in
/-- The chosen lift really reduces to the prescribed matrix over the residue field. -/
theorem liftGL3FromResidue_spec (B : GL3 (k R)) :
    GL3ReducesTo R (liftGL3FromResidue R B) B := by
  intro i j
  show IsLocalRing.residue R (liftGL3FromResidueMatrix R B i j) = _
  exact liftGL3FromResidueMatrix_spec R B i j

/-- The normalization dictated by the residue-field classification. -/
def normalizeByResidueStandardData
    (φ : AutSL3 R) (B : GL3 (k R)) (σk : k R ≃+* k R) (ε : Bool) :
    AutSL3 R := by
  classical
  let g : GL3 R := liftGL3FromResidue R B
  exact (FieldAutomorpisms.graphChoiceSL3 R ε).trans
    ((innerAutSL3byGL3 R g⁻¹).trans φ)

/-- After residue normalization, the six generators are fixed modulo `J`. -/
theorem normalizeByResidueStandardData_fixed_mod
    (φ : AutSL3 R)
    (B : GL3 (k R))
    (σk : k R ≃+* k R)
    (ε : Bool)
    (hfield :
      ∀ x : SL3 (k R),
        inducedResidueAut R φ x =
          ringAutSL3 (k R) σk
            ((FieldAutomorpisms.graphChoiceSL3 (k R) ε)
              (innerAutSL3byGL3 (k R) B x))) :
    LocalAutomorphisms.BasicGeneratorsFixedModJ R
      (normalizeByResidueStandardData R φ B σk ε) := by
  classical

  let g : GL3 R := liftGL3FromResidue R B

  have hg :
      Matrix.GeneralLinearGroup.map (IsLocalRing.residue R) g = B := by
    ext i j
    dsimp [g]
    exact liftGL3FromResidue_spec R B i j

  have hred_inner (h : GL3 R) (x : SL3 R) :
      reduction R (innerAutSL3byGL3 R h x) =
        innerAutSL3byGL3 (k R)
          (Matrix.GeneralLinearGroup.map (IsLocalRing.residue R) h)
          (reduction R x) := by
    have hxGL :
        Matrix.GeneralLinearGroup.map (IsLocalRing.residue R)
            (Matrix.SpecialLinearGroup.toGL x) =
          Matrix.SpecialLinearGroup.toGL
            ((Matrix.SpecialLinearGroup.map
              (IsLocalRing.residue R)) x) := by
      ext p q
      simp [Matrix.SpecialLinearGroup.map_apply_coe]

    have hconj :
        Matrix.GeneralLinearGroup.map (IsLocalRing.residue R)
            (h * Matrix.SpecialLinearGroup.toGL x * h⁻¹) =
          Matrix.GeneralLinearGroup.map (IsLocalRing.residue R) h *
            Matrix.SpecialLinearGroup.toGL
              ((Matrix.SpecialLinearGroup.map
                (IsLocalRing.residue R)) x) *
            (Matrix.GeneralLinearGroup.map
              (IsLocalRing.residue R) h)⁻¹ := by
      rw [Matrix.GeneralLinearGroup.map_mul,
          Matrix.GeneralLinearGroup.map_mul,
          Matrix.GeneralLinearGroup.map_inv,
          hxGL]

    apply Subtype.ext
    ext i j

    change
      (((Matrix.SpecialLinearGroup.map (IsLocalRing.residue R))
          ((innerAutSL3byGL3 R h) x) :
          Matrix (Fin 3) (Fin 3) (k R)) i j) =
        (((innerAutSL3byGL3 (k R)
            (Matrix.GeneralLinearGroup.map (IsLocalRing.residue R) h))
            ((Matrix.SpecialLinearGroup.map
              (IsLocalRing.residue R)) x) :
          Matrix (Fin 3) (Fin 3) (k R)) i j)

    rw [Matrix.SpecialLinearGroup.map_apply_coe,
        RingHom.mapMatrix_apply,
        Matrix.map_apply]

    change
      (IsLocalRing.residue R)
          (((h * Matrix.SpecialLinearGroup.toGL x * h⁻¹ : GL3 R) :
            Matrix (Fin 3) (Fin 3) R) i j) =
        (((Matrix.GeneralLinearGroup.map (IsLocalRing.residue R) h *
            Matrix.SpecialLinearGroup.toGL
              ((Matrix.SpecialLinearGroup.map
                (IsLocalRing.residue R)) x) *
            (Matrix.GeneralLinearGroup.map
              (IsLocalRing.residue R) h)⁻¹ : GL3 (k R)) :
          Matrix (Fin 3) (Fin 3) (k R)) i j)

    have hc := congrArg
      (fun z : GL3 (k R) =>
        ((z : Matrix (Fin 3) (Fin 3) (k R)) i j))
      hconj

    simpa only [Matrix.GeneralLinearGroup.map_apply] using hc

  have hred_graph (e : Bool) (x : SL3 R) :
      reduction R (FieldAutomorpisms.graphChoiceSL3 R e x) =
        FieldAutomorpisms.graphChoiceSL3 (k R) e (reduction R x) := by
    cases e with
    | false =>
        simp [FieldAutomorpisms.graphChoiceSL3]
    | true =>
        apply Subtype.ext
        ext i j
        simp [FieldAutomorpisms.graphChoiceSL3, reduction,
          CongruenceSubgroup.ρ, invTransposeAutSL3, invTransposeMap]
        exact congrFun (congrFun
          (RingHom.map_adjugate (IsLocalRing.residue R)
            (x : Matrix (Fin 3) (Fin 3) R)) j) i

  have hinvol (x : SL3 (k R)) :
      invTransposeAutSL3 (k R)
        (invTransposeAutSL3 (k R) x) = x := by
    change invTransposeMap (k R) (invTransposeMap (k R) x) = x
    exact (invTransposeAutSL3 (k R)).left_inv x

  have hinner_cancel (y : SL3 (k R)) :
      innerAutSL3byGL3 (k R) B
        (innerAutSL3byGL3 (k R) B⁻¹ y) = y := by
    change
      (innerAutSL3byGL3 (k R) B)
        ((innerAutSL3byGL3 (k R) B).symm y) = y
    exact (innerAutSL3byGL3 (k R) B).apply_symm_apply y

  have hnorm (x : SL3 R) :
      reduction R
          (normalizeByResidueStandardData R φ B σk ε x) =
        ringAutSL3 (k R) σk (reduction R x) := by
    change
      reduction R
        (φ (innerAutSL3byGL3 R g⁻¹
          (FieldAutomorpisms.graphChoiceSL3 R ε x))) =
        ringAutSL3 (k R) σk (reduction R x)

    rw [← inducedResidueAut_commutes R φ,
        hfield,
        hred_inner,
        hred_graph,
        Matrix.GeneralLinearGroup.map_inv,
        hg]

    cases ε <;>
      simp [FieldAutomorpisms.graphChoiceSL3,
        hinner_cancel, hinvol]

  have hfixed (A : SL3 R)
      (hA :
        ringAutSL3 (k R) σk (reduction R A) =
          reduction R A) :
      LocalAutomorphisms.SL3FixedModJ R
        (normalizeByResidueStandardData R φ B σk ε) A := by
    apply (LocalAutomorphisms.sl_congruent_iff_reduction_eq (R := R)).2
    change
      reduction R
          (normalizeByResidueStandardData R φ B σk ε A) =
        reduction R A
    rw [hnorm]
    exact hA
  have hringfix (A : SL3 R)
      (hA : ∀ i j,
        σk ((IsLocalRing.residue R)
          ((A : Matrix (Fin 3) (Fin 3) R) i j)) =
        (IsLocalRing.residue R)
          ((A : Matrix (Fin 3) (Fin 3) R) i j)) :
      ringAutSL3 (k R) σk (reduction R A) =
        reduction R A := by
    apply Subtype.ext
    ext i j

    change
      σk
        (((reduction R A : SL3 (k R)) :
          Matrix (Fin 3) (Fin 3) (k R)) i j) =
      (((reduction R A : SL3 (k R)) :
        Matrix (Fin 3) (Fin 3) (k R)) i j)

    change
      σk
        ((IsLocalRing.residue R)
          ((A : Matrix (Fin 3) (Fin 3) R) i j)) =
      (IsLocalRing.residue R)
        ((A : Matrix (Fin 3) (Fin 3) R) i j)

    exact hA i j

  refine ⟨
    hfixed _ (hringfix _ ?_),
    hfixed _ (hringfix _ ?_),
    hfixed _ (hringfix _ ?_),
    hfixed _ (hringfix _ ?_),
    hfixed _ (hringfix _ ?_),
    hfixed _ (hringfix _ ?_)
  ⟩ <;>
    intro i j <;>
    fin_cases i <;>
    fin_cases j <;>
    simp [FieldAutomorpisms.d1SL, FieldAutomorpisms.d1,
      FieldAutomorpisms.d2SL, FieldAutomorpisms.d2,
      FieldAutomorpisms.d3SL, FieldAutomorpisms.d3,
      FieldAutomorpisms.w1SL, FieldAutomorpisms.w1,
      FieldAutomorpisms.w2SL, FieldAutomorpisms.w2,
      FieldAutomorpisms.x12SL, FieldAutomorpisms.x12]

/-- Undoing the normalization preserves standardness. -/
theorem standard_of_normalized
    (φ : AutSL3 R) (B : GL3 (k R)) (σk : k R ≃+* k R) (ε : Bool)
    (hstd : LocalAutomorphisms.IsStandardSL3Aut R
      (normalizeByResidueStandardData R φ B σk ε)) :
    LocalAutomorphisms.IsStandardSL3Aut R φ := by
  classical
  rcases hstd with ⟨σ, δ, g, hg⟩
  let b : GL3 R := liftGL3FromResidue R B
  let graphGL3 : GL3 R → GL3 R := fun h =>
    { val := (((h⁻¹ : GL3 R) : Matrix (Fin 3) (Fin 3) R).transpose)
      inv := (((h : GL3 R) : Matrix (Fin 3) (Fin 3) R).transpose)
      val_inv := by rw [← Matrix.transpose_mul]; simp
      inv_val := by rw [← Matrix.transpose_mul]; simp }

  have hcomm (h : GL3 R) (x : SL3 R) :
      innerAutSL3byGL3 R h (invTransposeAutSL3 R x) =
        invTransposeAutSL3 R (innerAutSL3byGL3 R (graphGL3 h) x) := by
    change ↑(innerAutSL3byGL3 R h (invTransposeMap R x)) =
      ↑(invTransposeMap R (innerAutSL3byGL3 R (graphGL3 h) x))
    apply Subtype.ext
    unfold invTransposeMap
    rw [← (innerAutSL3byGL3 R (graphGL3 h)).map_inv x]
    change (((h : Matrix (Fin 3) (Fin 3) R) *
        (((x⁻¹ : SL3 R) : Matrix (Fin 3) (Fin 3) R).transpose)) *
        ((h⁻¹ : GL3 R) : Matrix (Fin 3) (Fin 3) R)) =
      ((((graphGL3 h : GL3 R) : Matrix (Fin 3) (Fin 3) R) *
        ((x⁻¹ : SL3 R) : Matrix (Fin 3) (Fin 3) R)) *
        (((graphGL3 h)⁻¹ : GL3 R) : Matrix (Fin 3) (Fin 3) R)).transpose
    simp [graphGL3, Matrix.transpose_mul, mul_assoc]

  have hinvol (x : SL3 R) :
      invTransposeAutSL3 R (invTransposeAutSL3 R x) = x := by
    change invTransposeMap R (invTransposeMap R x) = x
    exact (invTransposeAutSL3 R).left_inv x
  have hinner_mul (a c : GL3 R) (x : SL3 R) :
      innerAutSL3byGL3 R a (innerAutSL3byGL3 R c x) =
        innerAutSL3byGL3 R (a * c) x := by
    apply Subtype.ext
    dsimp [innerAutSL3byGL3]
    rw [_root_.mul_inv_rev]
    simp only [Matrix.GeneralLinearGroup.coe_mul]
    change (((a : Matrix (Fin 3) (Fin 3) R) *
        (((c : Matrix (Fin 3) (Fin 3) R) *
          (x : Matrix (Fin 3) (Fin 3) R)) *
          ((c⁻¹ : GL3 R) : Matrix (Fin 3) (Fin 3) R))) *
          ((a⁻¹ : GL3 R) : Matrix (Fin 3) (Fin 3) R)) =
      ((((a : Matrix (Fin 3) (Fin 3) R) *
        (c : Matrix (Fin 3) (Fin 3) R)) *
        (x : Matrix (Fin 3) (Fin 3) R)) *
        (((c⁻¹ : GL3 R) : Matrix (Fin 3) (Fin 3) R) *
          ((a⁻¹ : GL3 R) : Matrix (Fin 3) (Fin 3) R)))
    simpa only [mul_assoc]
  have hinner_cancel (a : GL3 R) (x : SL3 R) :
      innerAutSL3byGL3 R a⁻¹ (innerAutSL3byGL3 R a x) = x := by
    change (innerAutSL3byGL3 R a).symm ((innerAutSL3byGL3 R a) x) = x
    exact (innerAutSL3byGL3 R a).symm_apply_apply x

  have hundo_false (x : SL3 R) :
      normalizeByResidueStandardData R φ B σk false
        (innerAutSL3byGL3 R b x) = φ x := by
    change φ (innerAutSL3byGL3 R b⁻¹ (innerAutSL3byGL3 R b x)) = φ x
    rw [hinner_cancel]
  have hundo_true (x : SL3 R) :
      normalizeByResidueStandardData R φ B σk true
        (invTransposeAutSL3 R (innerAutSL3byGL3 R b x)) = φ x := by
    change φ (innerAutSL3byGL3 R b⁻¹
      (invTransposeAutSL3 R (invTransposeAutSL3 R
        (innerAutSL3byGL3 R b x)))) = φ x
    rw [hinvol, hinner_cancel]

  cases ε with
  | false =>
      refine ⟨σ, δ, g * b, ?_⟩
      intro x
      have h := hg (innerAutSL3byGL3 R b x)
      rw [hundo_false x, hinner_mul] at h
      exact h
  | true =>
      cases δ with
      | false =>
          refine ⟨σ, true, graphGL3 g * b, ?_⟩
          intro x
          have h := hg (invTransposeAutSL3 R (innerAutSL3byGL3 R b x))
          rw [hundo_true x, hcomm g (innerAutSL3byGL3 R b x), hinner_mul] at h
          simpa [FieldAutomorpisms.graphChoiceSL3] using h
      | true =>
          refine ⟨σ, false, graphGL3 g * b, ?_⟩
          intro x
          have h := hg (invTransposeAutSL3 R (innerAutSL3byGL3 R b x))
          rw [hundo_true x, hcomm g (innerAutSL3byGL3 R b x), hinner_mul] at h
          simpa [FieldAutomorpisms.graphChoiceSL3, hinvol] using h

/-- Final assembly: Group 1 + Group 3 + Group 4. -/
theorem every_aut_SL3_standard (φ : AutSL3 R) :
    LocalAutomorphisms.IsStandardSL3Aut R φ := by
  classical
  rcases FieldAutomorpisms.field_class (k R) (inducedResidueAut R φ) with
    ⟨σk, ε, B, hfield⟩
  have hmod := normalizeByResidueStandardData_fixed_mod R φ B σk ε hfield
  have hstd := LocalAutomorphisms.local_class R
    (normalizeByResidueStandardData R φ B σk ε) hmod
  exact standard_of_normalized R φ B σk ε hstd

end ResidueReduction

end