import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsLiftOfMemKO
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodIdempotentFixesOfOnlySeriesOfLabelActs
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroInertia
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIrrHarishChandraInductionThetaInvDet
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DetCharacterIrreducibleLabel

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.PendOf GlobalTheory.LevelType
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.LevelType.RestrictionTwo

open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders
open scoped Classical

variable {p : ℕ} [Fact p.Prime]

theorem stdBlock_iff (a : ℕ) (y : Gn p (a + 1)) :
    StdBlock a y ↔ InPar a (y : Mt p (a + 1)) ∧ tl a (y : Mt p (a + 1)) = 1 := by
  constructor
  · intro h
    refine ⟨fun i j hj hi => ?_, ?_⟩
    · rw [h i j (by omega)]
      have : i ≠ j := fun e => by rw [e] at hi; omega
      simp [this]
    · ext i j
      have hi : (i : ℕ) < a + 1 := by omega
      have hj : (j : ℕ) < a + 1 := by omega
      have := h ⟨i, hi⟩ ⟨j, hj⟩ (by first | omega | simp | (simp; omega))
      simp only [tl, entN, hi, hj, and_self, dif_pos, Matrix.one_apply, Fin.ext_iff] at this ⊢
      exact this
  · rintro ⟨h1, h2⟩ i j hij
    have hj : (j : ℕ) < a := by omega
    by_cases hi : (i : ℕ) < a
    · have := congrFun (congrFun h2 ⟨i, hi⟩) ⟨j, hj⟩
      have hi' : (i : ℕ) < a + 1 := by omega
      have hj' : (j : ℕ) < a + 1 := by omega
      simp only [tl, entN, hi', hj', and_self, dif_pos, Matrix.one_apply, Fin.ext_iff] at this
      simp only [Fin.ext_iff]
      exact this
    · have hne : i ≠ j := fun e => by rw [e] at hi; omega
      rw [if_neg hne]
      exact h1 i j hj (by omega)

theorem det_eq_of_stdBlock (a : ℕ) (y : Gn p (a + 1)) (h : StdBlock a y) :
    Matrix.GeneralLinearGroup.det y = Matrix.GeneralLinearGroup.det (toG (br a 1 (y : Mt p (a + 1)))) := by
  obtain ⟨h1, h2⟩ := (stdBlock_iff a y).1 h
  rw [GlobalTheory.GLq.LabelDet.det_par a 1 y h1, h2, GlobalTheory.GLq.LabelDet.toG_one, map_one, one_mul]

theorem br_eq_iff (a : ℕ) (y : Gn p (a + 1)) (h : InPar a (y : Mt p (a + 1))) (x : Gn p 1) :
    br a 1 (y : Mt p (a + 1)) = (x : Mt p 1) ↔ x = toG (br a 1 (y : Mt p (a + 1))) := by
  have hd := GlobalTheory.GLq.LabelDet.det_inPar a 1 _ h
  have h0 : (tl a (y : Mt p (a + 1))).det * (br a 1 (y : Mt p (a + 1))).det ≠ 0 := hd ▸ y.det_ne_zero
  have hu : IsUnit (br a 1 (y : Mt p (a + 1))) :=
    (Matrix.isUnit_iff_isUnit_det _).2 (Ne.isUnit (right_ne_zero_of_mul h0))
  have hv : ((toG (br a 1 (y : Mt p (a + 1))) : Gn p 1) : Mt p 1) = br a 1 (y : Mt p (a + 1)) := by
    unfold toG; rw [dif_pos hu]; exact IsUnit.unit_spec hu
  constructor
  · intro e; apply Units.ext; rw [hv, e]
  · intro e; rw [e, hv]

theorem sum_res_eq (a : ℕ) (θ : (ZMod p)ˣ →* ℂˣ) (α : Gn p (a + 1) → ℂ) :
    ∑ x : Gn p 1, ((θ⁻¹ (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) * res a 1 α 1 x =
      ((p : ℂ) ^ a)⁻¹ * stdTrace a θ α := by
  rw [stdTrace, Finset.mul_sum]
  unfold res
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  by_cases hs : StdBlock a y
  · obtain ⟨h1, h2⟩ := (stdBlock_iff a y).1 hs
    rw [if_pos hs]
    have e : ∀ x : Gn p 1, ((θ⁻¹ (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) * (((p : ℂ) ^ (a * 1))⁻¹ *
        if InPar a (y : Mt p (a + 1)) ∧ tl a (y : Mt p (a + 1)) = ((1 : Gn p a) : Mt p a) ∧
          br a 1 (y : Mt p (a + 1)) = (x : Mt p 1) then α y else 0) =
        if x = toG (br a 1 (y : Mt p (a + 1))) then
          ((p : ℂ) ^ a)⁻¹ * ((((θ (Matrix.GeneralLinearGroup.det y))⁻¹ : ℂˣ) : ℂ) * α y) else 0 := by
      intro x
      by_cases hx : x = toG (br a 1 (y : Mt p (a + 1)))
      · rw [if_pos ⟨h1, by rw [h2, Units.val_one], (br_eq_iff a y h1 x).2 hx⟩, if_pos hx, det_eq_of_stdBlock a y hs, ← hx,
          MonoidHom.inv_apply, Nat.mul_one]
        ring
      · rw [if_neg (fun h => hx ((br_eq_iff a y h1 x).1 h.2.2)), if_neg hx, mul_zero, mul_zero]
    rw [Finset.sum_congr rfl fun x _ => e x, Finset.sum_ite_eq']
    simp
  · rw [if_neg hs, mul_zero]
    refine Finset.sum_eq_zero fun x _ => ?_
    rw [if_neg, mul_zero, mul_zero]
    rintro ⟨h1, h2, -⟩
    exact hs ((stdBlock_iff a y).2 ⟨h1, by rw [h2, Units.val_one]⟩)

theorem exists_irr_hc_of_stdTrace_ne_zero : ∀ (p : ℕ) [Fact p.Prime] (a : ℕ) (θ : (ZMod p)ˣ →* ℂˣ)
    (α : GlobalTheory.GLq.Gn p (a + 1) → ℂ), GlobalTheory.GLq.IsIrr α → stdTrace a θ α ≠ 0 →
    ∃ σ : GlobalTheory.GLq.Gn p a → ℂ, GlobalTheory.GLq.IsIrr σ ∧ GlobalTheory.GLq.ip α (GlobalTheory.GLq.hc a 1 σ
      (fun y : GlobalTheory.GLq.Gn p 1 => ((θ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ)) (a + 1)) ≠ 0 := by
  intro p _ a θ α hα hne
  have key : ∑ x : Gn p 1, ((θ⁻¹ (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) * res a 1 α 1 x ≠ 0 := by
    rw [sum_res_eq]
    exact mul_ne_zero (inv_ne_zero (pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero))) hne
  obtain ⟨σ, hσ, h⟩ := (GlobalTheory.GLq.HCFrobWeight.exists_irr_hc_thetaInv p a α hα θ⁻¹).1 key
  exact ⟨σ, hσ, by simpa only [inv_inv] using h⟩

end GlobalTheory.LevelType.RestrictionTwo
