import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PrOfMulEqZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchwartzBruhatHalfTensorOrthogonalIdempotentsStatement

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.AdForm
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.PutIn.HalfOff

variable {D : D7} {S T : HSp D}

theorem smul_apply' (b : AE D) (t : WO S T) (i j) : (b • t) i j = b * t i j := by
  rw [Matrix.smul_apply, smul_eq_mul]

theorem smul_half_zero {a b : AE D} (hab : a * b = 0) {x : WO S T} (hx : IsHalf a x) : b • x = 0 := by
  ext i j
  rw [smul_apply', Matrix.zero_apply, ← hx i j, ← mul_assoc, mul_comm b a, hab, zero_mul]

theorem half_smul {b : AE D} (hb : b * b = b) (t : WO S T) : IsHalf b (b • t) := fun i j => by
  rw [smul_apply', ← mul_assoc, hb]

theorem tens_trans {a b : AE D} (hab : a * b = 0) (Φ Ψ : WO S T → ℂ) {x : WO S T} (hx : IsHalf a x) :
    tens b (fun t => Φ (t + x)) Ψ = fun t => tens b Φ Ψ (t + x) := by
  funext t
  simp only [tens_apply, smul_add, smul_half_zero hab hx, add_zero]
  congr 2
  abel

theorem tens_modul (ψ : AddChar (AF D.host.F) ℂ) {a b : AE D} (hab : a * b = 0) (hb : b * b = b)
    (Φ Ψ : WO S T → ℂ) {y : WO S T} (hy : IsHalf (cA D a) y) :
    tens b (fun t => ψ (symplO S T t y) * Φ t) Ψ = fun t => ψ (symplO S T t y) * tens b Φ Ψ t := by
  funext t
  have hba : b * a = 0 := by rw [mul_comm, hab]
  have e1 : symplO S T t y = symplO S T (t - b • t) y + symplO S T (b • t) y := by
    rw [← GlobalTheory.LocMod.TensorModel.symplO_add_left', sub_add_cancel]
  rw [tens_apply, tens_apply, e1, GlobalTheory.LocMod.TensorModel.symplO_half_zero hba (half_smul hb t) hy, add_zero, mul_assoc]

theorem tens_vac {a b : AE D} (hab : a * b = 0) (hb : b * b = b) (Λ : AddSubgroup (WO S T))
    (hΛ : ∀ u ∈ Λ, b • u ∈ Λ) :
    tens b ((1 : ℂ) • halfInd a Λ) (halfInd b Λ) = (1 : ℂ) • halfInd (a + b) Λ := by
  classical
  funext t
  simp only [one_smul, tens_apply]
  set M : WO S T := b • t with hMdef
  have hM : IsHalf b M := half_smul hb t
  have key : ((t - M ∈ Λ ∧ IsHalf a (t - M)) ∧ M ∈ Λ) ↔ (t ∈ Λ ∧ IsHalf (a + b) t) := by
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      refine ⟨by simpa using add_mem h1 h3, fun i j => ?_⟩
      have h := h2 i j
      simp only [hMdef, Matrix.sub_apply, smul_apply'] at h
      linear_combination h + t i j * hab
    · rintro ⟨h1, h2⟩
      have h3 : M ∈ Λ := hΛ t h1
      refine ⟨⟨sub_mem h1 h3, fun i j => ?_⟩, h3⟩
      simp only [hMdef, Matrix.sub_apply, smul_apply']
      linear_combination h2 i j - t i j * hab
  unfold halfInd
  by_cases hR : t ∈ Λ ∧ IsHalf (a + b) t
  · obtain ⟨⟨h1, h2⟩, h3⟩ := key.2 hR
    rw [if_pos hR, if_pos ⟨h1, h2⟩, if_pos ⟨h3, hM⟩, mul_one]
  · rw [if_neg hR]
    by_cases h3 : M ∈ Λ
    · rw [if_pos (show M ∈ Λ ∧ IsHalf b M from ⟨h3, hM⟩), mul_one,
        if_neg (show ¬(t - M ∈ Λ ∧ IsHalf a (t - M)) from fun h => hR (key.1 ⟨h, h3⟩))]
    · rw [if_neg (show ¬(M ∈ Λ ∧ IsHalf b M) from fun h => h3 h.1), mul_zero]

end GlobalTheory.FinPl.PutIn.HalfOff

open GlobalTheory.FinPl.PutIn.HalfOff in

theorem GlobalTheory.FinPl.PutIn.isPlaceModel_tensHalf : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (a b : AE D) (Λ : AddSubgroup (WO S T)) (f₀ : WO S T → ℂ) (Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)), a * b = 0 → b * b = b → (∀ u ∈ Λ, b • u ∈ Λ) → IsPlaceModel ψ (symplO S T) (heisO ψ S T) (a + b) Λ 1 f₀ Tm → IsPlaceModel ψ (symplO S T) (heisO ψ S T) a Λ 1 f₀ (Tm ∘ₗ GlobalTheory.FinPl.PutIn.tensL b (halfInd b Λ)) := by
  intro D ψ S T a b Λ f₀ Tm hab hb hΛ hT
  have hba : b * a = 0 := by rw [mul_comm, hab]
  have hsb : ∀ Φ, IsSBHalf a Λ Φ → IsSBHalf (a + b) Λ (tens b Φ (halfInd b Λ)) := fun Φ hΦ =>
    GlobalTheory.T.schwartzBruhat_half_tensor_orthogonal_idempotents D S T a b Λ Φ (halfInd b Λ) hab hb hΛ hΦ (GlobalTheory.isSBHalf_halfInd b Λ)
  refine ⟨fun Φ hΦ x hx => ?_, fun Φ hΦ y hy => ?_, ?_⟩
  · rw [LinearMap.comp_apply, tensL_apply, tens_trans hab Φ _ hx]
    have hx' : IsHalf (a + b) x := by
      rw [add_comm]; exact GlobalTheory.LocMod.TensorModel.half_sum hba hx
    exact hT.trans _ (hsb Φ hΦ) x hx'
  · rw [LinearMap.comp_apply, tensL_apply, tens_modul ψ hab hb Φ _ hy]
    have hy' : IsHalf (cA D (a + b)) y := by
      rw [add_comm]; exact GlobalTheory.LocMod.TensorModel.half_sum_cA hba hy
    exact hT.modul _ (hsb Φ hΦ) y hy'
  · rw [LinearMap.comp_apply, tensL_apply, tens_vac hab hb Λ hΛ]
    exact hT.vac

end
