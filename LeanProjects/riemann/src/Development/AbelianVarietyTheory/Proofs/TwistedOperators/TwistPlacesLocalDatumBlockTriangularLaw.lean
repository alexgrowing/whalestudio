import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TameOnOne

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts GlobalTheory.StepLaw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.OmegaTwistLaw

section Fin
variable {κ : Type} [CommRing κ]

theorem lowZero_mul {a b c r : ℕ} {A : Matrix (Fin b) (Fin c) κ} {B : Matrix (Fin c) (Fin a) κ}
    (hA : LowZero r A) (hB : LowZero r B) : LowZero r (A * B) := by
  intro i j hi hj
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  rcases le_or_gt r l.val with hl | hl
  · rw [hB l j hl hj, mul_zero]
  · rw [hA i l hi hl, zero_mul]

theorem topL_eq {a b r : ℕ} (ha : r ≤ a) (hb : r ≤ b) (A : Matrix (Fin b) (Fin a) κ) :
    topL r A = A.submatrix (Fin.castLE hb) (Fin.castLE ha) := by
  ext i j
  have hij : i.val < b ∧ j.val < a := ⟨lt_of_lt_of_le i.isLt hb, lt_of_lt_of_le j.isLt ha⟩
  show (if h : i.val < b ∧ j.val < a then A ⟨i.val, h.1⟩ ⟨j.val, h.2⟩ else 0) = A (Fin.castLE hb i) (Fin.castLE ha j)
  rw [dif_pos hij]
  rfl

theorem topL_mul {a b c r : ℕ} (ha : r ≤ a) (hb : r ≤ b) (hc : r ≤ c) (A : Matrix (Fin b) (Fin c) κ)
    {B : Matrix (Fin c) (Fin a) κ} (hB : LowZero r B) : topL r (A * B) = topL r A * topL r B := by
  rw [topL_eq ha hb, topL_eq hc hb, topL_eq ha hc]
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  symm
  refine Fintype.sum_of_injective (Fin.castLE hc) (Fin.castLE_injective hc) _ _ (fun l hl => ?_) (fun l => rfl)
  have hlr : r ≤ l.val := by
    by_contra hlt
    exact hl ⟨⟨l.val, not_le.mp hlt⟩, Fin.ext rfl⟩
  rw [hB l _ hlr (by simp), mul_zero]

theorem lowZero_of_mem {n r : ℕ} {g : GL (Fin n) κ} (h : g ∈ blockTri (blk2 r)) : LowZero r g.val := by
  intro i j hi hj
  refine mem_blockTri.mp h i j ?_
  have h1 : blk2 r i = 1 := if_neg (not_lt.mpr hi)
  have h0 : blk2 r j = 0 := if_pos hj
  rw [h0, h1]
  exact Nat.zero_lt_one

theorem det_eq {n r : ℕ} (hr : r ≤ n) {g : GL (Fin n) κ} (h : g ∈ blockTri (blk2 r)) :
    Matrix.GeneralLinearGroup.det g = Matrix.GeneralLinearGroup.det (upperLeftBlock hr g) * dBlk (blk2 r) 1 g := by
  have hg : (g.val).BlockTriangular (blk2 r) := fun i j hij => mem_blockTri.mp h i j hij
  let e : Fin r ≃ {x : Fin n // blk2 r x = 0} :=
    { toFun := fun i => ⟨Fin.castLE hr i, if_pos (by simp)⟩
      invFun := fun x => ⟨x.1.val, by
        have hx := x.2
        unfold blk2 at hx
        split_ifs at hx with hlt
        exact hlt⟩
      left_inv := fun i => Fin.ext rfl
      right_inv := fun x => Subtype.ext (Fin.ext rfl) }
  have hsub : (g.val.toSquareBlock (blk2 r) 0).submatrix e e = g.val.submatrix (Fin.castLE hr) (Fin.castLE hr) := by
    ext i j
    rfl
  ext
  rw [Units.val_mul, Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply,
    upper_block_val_submatrix hr h, diag_block_det_val 1 h, hg.det, ← hsub, Matrix.det_submatrix_equiv_self]
  have hsub2 : Finset.univ.image (blk2 (n := n) r) ⊆ {0, 1} := by
    intro x hx
    obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp hx
    unfold blk2
    split_ifs <;> simp
  rw [Finset.prod_subset hsub2 (fun x _ hx => ?_), Finset.prod_pair zero_ne_one]
  · rfl
  · haveI : IsEmpty {y : Fin n // blk2 r y = x} :=
      ⟨fun y => hx (Finset.mem_image.mpr ⟨y.1, Finset.mem_univ _, y.2⟩)⟩
    exact Matrix.det_isEmpty

theorem det_topL {a b r : ℕ} (ha : r ≤ a) (hb : r ≤ b) {gS : GL (Fin a) κ} {gT : GL (Fin b) κ}
    (hS : gS ∈ blockTri (blk2 r)) (hT : gT ∈ blockTri (blk2 r)) {y : Matrix (Fin b) (Fin a) κ} (hy : LowZero r y) :
    (topL r ((gT⁻¹).val * y * gS.val)).det =
      ((Matrix.GeneralLinearGroup.det (upperLeftBlock hb gT))⁻¹ * Matrix.GeneralLinearGroup.det (upperLeftBlock ha gS) : κˣ) *
        (topL r y).det := by
  have hTi : gT⁻¹ ∈ blockTri (blk2 r) := inv_mem hT
  have hinv : upperLeftBlock hb gT⁻¹ = (upperLeftBlock hb gT)⁻¹ := extendOne_inv (blkR hb) hT
  rw [topL_mul ha hb ha ((gT⁻¹).val * y) (lowZero_of_mem hS), topL_mul ha hb hb (gT⁻¹).val hy,
    Matrix.det_mul, Matrix.det_mul, topL_eq ha ha gS.val, topL_eq hb hb (gT⁻¹).val, ← upper_block_val_submatrix ha hS,
    ← upper_block_val_submatrix hb hTi, hinv, ← Matrix.GeneralLinearGroup.val_det_apply, ← Matrix.GeneralLinearGroup.val_det_apply,
    map_inv, Units.val_mul]
  ring

theorem lowZero_iff {a b r : ℕ} {gS : GL (Fin a) κ} {gT : GL (Fin b) κ}
    (hS : gS ∈ blockTri (blk2 r)) (hT : gT ∈ blockTri (blk2 r)) (y : Matrix (Fin b) (Fin a) κ) :
    LowZero r ((gT⁻¹).val * y * gS.val) ↔ LowZero r y := by
  have hS' := lowZero_of_mem hS
  have hTi := lowZero_of_mem (inv_mem hT)
  constructor
  · intro h
    have hy : y = gT.val * ((gT⁻¹).val * y * gS.val) * (gS⁻¹).val := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul,
        Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
    rw [hy]
    exact lowZero_mul (lowZero_mul (lowZero_of_mem hT) h) (lowZero_of_mem (inv_mem hS))
  · intro h
    exact lowZero_mul (lowZero_mul hTi h) hS'

end Fin

theorem omegaQ_blockTri : ∀ (D : D7) (a b r : ℕ), r ≤ a → r ≤ b → ∀ (Q : Finset (Pl D.host.E)) (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (k : ℤ) (gS : ∀ PP : Pl D.host.E, GL (Fin a) (kP PP)) (gT : ∀ PP : Pl D.host.E, GL (Fin b) (kP PP)) (y y' : ∀ PP : Pl D.host.E, Matrix (Fin b) (Fin a) (kP PP)), (∀ PP ∈ Q, gS PP ∈ blockTri (blk2 r)) → (∀ PP ∈ Q, gT PP ∈ blockTri (blk2 r)) → (∀ PP ∈ Q, y' PP = ((gT PP)⁻¹).val * y PP * (gS PP).val) → (∏ PP ∈ Q, (((ξ PP (Matrix.GeneralLinearGroup.det (gS PP)) : ℂˣ) : ℂ)⁻¹ * ((ξ PP (Matrix.GeneralLinearGroup.det (gT PP)) : ℂˣ) : ℂ))) ^ k * omegaQ Q r ξ k y' = (∏ PP ∈ Q, (((ξ PP (dBlk (blk2 r) 1 (gS PP)) : ℂˣ) : ℂ)⁻¹ * ((ξ PP (dBlk (blk2 r) 1 (gT PP)) : ℂˣ) : ℂ))) ^ k * omegaQ Q r ξ k y := by
  intro D a b r ha hb Q ξ k gS gT y y' hS hT hy'
  have hdet : ∀ PP ∈ Q, LowZero r (y PP) → (topL r (y' PP)).det =
      (((Matrix.GeneralLinearGroup.det (upperLeftBlock hb (gT PP)))⁻¹ * Matrix.GeneralLinearGroup.det (upperLeftBlock ha (gS PP)) :
        (kP PP)ˣ) : kP PP) * (topL r (y PP)).det := fun PP hPP hl => by
    rw [hy' PP hPP]
    exact det_topL ha hb (hS PP hPP) (hT PP hPP) hl
  have hcond : (∀ PP ∈ Q, LowZero r (y' PP) ∧ IsUnit (topL r (y' PP)).det) ↔
      (∀ PP ∈ Q, LowZero r (y PP) ∧ IsUnit (topL r (y PP)).det) := by
    refine forall₂_congr fun PP hPP => ?_
    have hlz : LowZero r (y' PP) ↔ LowZero r (y PP) := by
      rw [hy' PP hPP]
      exact lowZero_iff (hS PP hPP) (hT PP hPP) (y PP)
    rw [hlz]
    refine and_congr_right fun hl => ?_
    rw [hdet PP hPP hl, Units.isUnit_units_mul]
  have hsplit : ∀ (A : Pl D.host.E → ℂ) (U : Q → ℂ),
      (∏ PP ∈ Q, A PP) ^ k * ∏ PP ∈ Q.attach, U PP ^ k = ∏ PP ∈ Q.attach, (A PP.1 * U PP) ^ k := by
    intro A U
    rw [← Finset.prod_attach Q A, ← Finset.prod_zpow, ← Finset.prod_mul_distrib]
    simp only [mul_zpow]
  unfold omegaQ
  by_cases h : ∀ PP ∈ Q, LowZero r (y PP) ∧ IsUnit (topL r (y PP)).det
  · have h' := hcond.mpr h
    rw [dif_pos h', dif_pos h, hsplit, hsplit]
    refine Finset.prod_congr rfl fun PP _ => ?_
    congr 1
    obtain ⟨P, hP⟩ := PP
    have eS := det_eq ha (hS P hP)
    have eT := det_eq hb (hT P hP)
    have eU : (h' P hP).2.unit = ((Matrix.GeneralLinearGroup.det (upperLeftBlock hb (gT P)))⁻¹ *
        Matrix.GeneralLinearGroup.det (upperLeftBlock ha (gS P))) * (h P hP).2.unit := by
      ext
      rw [IsUnit.unit_spec, Units.val_mul, IsUnit.unit_spec]
      exact hdet P hP (h P hP).1
    simp only []
    rw [eS, eT, eU]
    simp only [map_mul, map_inv, Units.val_mul, Units.val_inv_eq_inv_val]
    field_simp
  · have h' : ¬ ∀ PP ∈ Q, LowZero r (y' PP) ∧ IsUnit (topL r (y' PP)).det := fun h'' => h (hcond.mp h'')
    rw [dif_neg h', dif_neg h, mul_zero, mul_zero]

end GlobalTheory.OmegaTwistLaw

end
