import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergVacuumCommutantPreservesLatticeVacua
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.ThetaEigen

variable {D : D7}

def heisLin (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (w : WO S T) :
    (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ) where
  toFun := heisO ψ S T w
  map_add' f g := by funext x; simp only [heisO, Pi.add_apply, mul_add]
  map_smul' a f := by funext x; simp only [heisO, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

theorem heisLin_apply (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (w : WO S T) (f : WO S T → ℂ) :
    heisLin ψ S T w f = heisO ψ S T w f := rfl

theorem heisO_smul_comm (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (w : WO S T) (k : ℂ) (f : WO S T → ℂ) :
    heisO ψ S T w (k • f) = k • heisO ψ S T w f := (heisLin ψ S T w).map_smul k f

theorem addChar_ne_zero (ψ : AddChar (AF D.host.F) ℂ) (a : AF D.host.F) : ψ a ≠ 0 := by
  intro h
  have h1 := AddChar.map_zero_eq_one ψ
  rw [← add_neg_cancel a, AddChar.map_add_eq_mul, h, zero_mul] at h1
  exact zero_ne_one h1

theorem eq_zero_of_heisO_eq_zero (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (w : WO S T) (g : WO S T → ℂ)
    (h : heisO ψ S T w g = 0) : g = 0 := by
  funext x
  have h1 := congrFun h (x - w)
  simp only [heisO, sub_add_cancel, Pi.zero_apply] at h1
  exact (mul_eq_zero.1 h1).resolve_left (addChar_ne_zero ψ _)

theorem heisO_eigen_of_isThetaAt : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (e : AE D) (Λ : AddSubgroup (WO S T)) (f₀ Φ f : WO S T → ℂ) (w : WO S T) (c : ℂ), IsThetaAt ψ (symplO S T) (heisO ψ S T) e Λ 1 f₀ Φ f → (∀ x : WO S T, IsHalf e x → symplO S T w x = 0) → (∀ y : WO S T, IsHalf (cA D e) y → symplO S T w y = 0) → heisO ψ S T w f₀ = c • f₀ → ∃ c' : ℂ, heisO ψ S T w f = c' • f := by
  intro D ψ S T e Λ f₀ Φ f w c hθ hx hy hc
  obtain ⟨⟨T₀, hT₀⟩, hall⟩ := hθ
  have hψ0 : ψ 0 = 1 := AddChar.map_zero_eq_one ψ
  have key : ∀ k : ℂ, k • heisO ψ S T w f₀ = f₀ → f = k • heisO ψ S T w f := by
    intro k hk
    have hT' : IsPlaceModel ψ (symplO S T) (heisO ψ S T) e Λ 1 f₀ (k • (heisLin ψ S T w ∘ₗ T₀)) := by
      refine ⟨fun Φ' hΦ' x hxe => ?_, fun Φ' hΦ' y hye => ?_, ?_⟩
      · simp only [LinearMap.smul_apply, LinearMap.comp_apply, heisLin_apply]
        rw [hT₀.trans Φ' hΦ' x hxe, GlobalTheory.Asc.heisO_comm, hx x hxe, hψ0, one_smul, heisO_smul_comm]
      · simp only [LinearMap.smul_apply, LinearMap.comp_apply, heisLin_apply]
        rw [hT₀.modul Φ' hΦ' y hye, GlobalTheory.Asc.heisO_comm, hy y hye, hψ0, one_smul, heisO_smul_comm]
      · simp only [LinearMap.smul_apply, LinearMap.comp_apply, heisLin_apply]
        rw [hT₀.vac, hk]
    have h2 : f = (k • (heisLin ψ S T w ∘ₗ T₀)) Φ := hall _ hT'
    have h3 : f = T₀ Φ := hall T₀ hT₀
    rw [show (k • (heisLin ψ S T w ∘ₗ T₀)) Φ = k • heisO ψ S T w (T₀ Φ) from rfl, ← h3] at h2
    exact h2
  by_cases hc0 : c = 0
  · subst hc0
    rw [zero_smul] at hc
    have hf₀ := eq_zero_of_heisO_eq_zero ψ S T w f₀ hc
    have h1 := key 1 (by rw [one_smul, hc, hf₀])
    exact ⟨1, by rw [one_smul]; rw [one_smul] at h1; exact h1.symm⟩
  · refine ⟨c, ?_⟩
    have h1 := key c⁻¹ (by rw [hc, smul_smul, inv_mul_cancel₀ hc0, one_smul])
    calc heisO ψ S T w f = c • (c⁻¹ • heisO ψ S T w f) := by rw [smul_smul, mul_inv_cancel₀ hc0, one_smul]
      _ = c • f := by rw [← h1]

end GlobalTheory.ThetaEigen
