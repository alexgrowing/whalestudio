import Mathlib
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.RigFrame
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LowerTriIsUnitDet
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsCombAtIffIsDerivAt0
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsDerivAt0CompLinear
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.TriangularFrameMovesPeriodBlockTriangular
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.UniformizationPeriodLatticeChange
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsInvariantNatLengthLattice

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif GlobalTheory.FrameNorm
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.FrameNorm

theorem mulVec_single_of_support {T : Type} {m : T → ℕ} {g : ℕ} (e : Fin g ≃ Σ τ : T, Fin (m τ))
    (h : Matrix (Fin g) (Fin g) ℂ) (hs : ∀ j j', h j j' ≠ 0 → (e j).1 = (e j').1) (τ : T) (i : Fin (m τ)) :
    h *ᵥ Pi.single (e.symm ⟨τ, i⟩) 1 =
      ∑ i', h (e.symm ⟨τ, i'⟩) (e.symm ⟨τ, i⟩) • (Pi.single (e.symm ⟨τ, i'⟩) 1 : Fin g → ℂ) := by
  classical
  ext j
  obtain ⟨⟨τ', a⟩, rfl⟩ := e.symm.surjective j
  simp only [Matrix.mulVec_single_one, Matrix.col_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  by_cases hτ : τ' = τ
  · subst hτ
    rw [Finset.sum_eq_single a (fun b _ hb => ?_) (by simp), Pi.single_eq_same, mul_one]
    rw [Pi.single_eq_of_ne, mul_zero]
    intro hh
    exact hb (eq_of_heq (Sigma.mk.inj (e.symm.injective hh)).2).symm
  · rw [Finset.sum_eq_zero fun b _ => ?_]
    · by_contra hne
      have := hs _ _ hne
      rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at this
      exact hτ this
    · rw [Pi.single_eq_of_ne, mul_zero]
      intro hh
      exact hτ (Sigma.mk.inj (e.symm.injective hh)).1

set_option maxHeartbeats 1000000 in

theorem frBor_of_triangular_period : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) (k : Fin F.n) (P P₀ : (F.Di k).La →+ (Fin g → ℂ)) (h₀ : Matrix (Fin g) (Fin g) ℂ) (y y₀ : FrPt Xo c (CAt σ)), IsPeriod (F.Di k) (fun j => relab c σ (e j).1) P → IsPeriod (F.Di k) (fun j => relab c σ (e j).1) P₀ → (∀ a, P₀ a = h₀ *ᵥ P a) → (∀ j j', h₀ j j' ≠ 0 → (e j).1 = (e j').1 ∧ ((e j).2 : ℕ) ≤ (e j').2) → y.x = F.u k P → y₀.x = F.u k P₀ → (∀ τ (i : Fin (Dw.mult τ)), IsDerivAt0 (fun z => (F.ex k P z).left) (Pi.single (e.symm ⟨τ, i⟩) 1) (y.u τ i)) → (∀ τ (i : Fin (Dw.mult τ)), IsDerivAt0 (fun z => (F.ex k P₀ z).left) (Pi.single (e.symm ⟨τ, i⟩) 1) (y₀.u τ i)) → ∃ t : Ix Dw → (CAt σ)ˣ, FrBor t y₀ y ∧ ∀ j, toC (t (some (e j)) : CAt σ) = h₀ j j := by
  intro E _ _ _ H Dw l Xo c σ g e F k P P₀ h₀ y y₀ hP hP₀ hh hs hy hy₀ hu hu₀
  classical
  obtain ⟨hdet, hpt, hex⟩ := GlobalTheory.FamRigid.ex_eq_of_level_group GlobalTheory.latMinkowski E H Dw l Xo _ g _ F k P P₀
    (LinearEquiv.refl _ _) h₀ hP hP₀ (fun _ _ => rfl) (fun a _ => ⟨0, by simp⟩) (fun a => ⟨0, by simp⟩) hh
  have hinj : ∀ j j', (e j).1 = (e j').1 → ((e j).2 : ℕ) = (e j').2 → j = j' := by
    intro j j' h1 h2
    apply e.injective
    exact Sigma.ext h1 ((Fin.heq_ext_iff (by rw [h1])).2 h2)
  have hdiag : ∀ j, h₀ j j ≠ 0 := by
    rw [GlobalTheory.PerBor.det_of_support (fun j => (e j).1) (fun j => ((e j).2 : ℕ)) hinj h₀ hs] at hdet
    exact fun j => Finset.prod_ne_zero_iff.1 hdet.ne_zero j (Finset.mem_univ j)
  have hx : y.x = y₀.x := hy.trans (hpt.trans hy₀.symm)
  let cf : ∀ τ, Fin (Dw.mult τ) → Fin (Dw.mult τ) → CAt σ := fun τ i i' =>
    (h₀ (e.symm ⟨τ, i'⟩) (e.symm ⟨τ, i⟩) : ℂ)
  have hc : ∀ τ i, IsCombAt y₀.x (y₀.u τ) (cf τ i) (y.u τ i) := by
    intro τ i
    have d1 := (GlobalTheory.ExpChain.isDerivAt0_ex_iff E H Dw l Xo _ g _ F k P hP k P₀ (Matrix.mulVecLin h₀) hP₀ hex
      _ _).1 (hu τ i)
    rw [Matrix.mulVecLin_apply, mulVec_single_of_support e h₀ (fun j j' h => (hs j j' h).1)] at d1
    have d2 := (GlobalTheory.DerLin.isCombAt_iff_isDerivAt0 E H Dw l Xo _ g _ F k P₀ hP₀ _ (y₀.u τ)
      (fun i => Pi.single (e.symm ⟨τ, i⟩) 1) (hu₀ τ) _ (y.u τ i)).2 d1
    rw [hy₀]
    exact d2
  obtain ⟨t, ht⟩ := (frBor_calculus E H Dw l Xo c (CAt σ) y₀ y y).2.1 hx fun τ i =>
    ⟨cf τ i, isUnit_iff_ne_zero.2 (hdiag _), fun j hj => by
      by_contra hne
      have := (hs _ _ hne).2
      rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at this
      exact absurd hj (not_lt.2 this), hc τ i⟩
  refine ⟨t, ht, fun j => ?_⟩
  obtain ⟨⟨τ, i⟩, rfl⟩ := e.symm.surjective j
  rw [Equiv.apply_symm_apply]
  obtain ⟨a, ha, -, hac⟩ := ht.2.1 τ i
  have htan : IsTanAt y₀.x (y.u τ i) := by rw [← hx]; exact y.tan τ i
  have := (y₀.basis τ (y.u τ i) htan (y.eig τ i)).unique hac (hc τ i)
  rw [← ha, this]
  rfl

end GlobalTheory.FrameNorm
