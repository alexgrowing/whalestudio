import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum

open CategoryTheory

noncomputable section

namespace DiscreteGroups.sglob.DzType.Kon

variable {G : Type} [Group G] [Fintype G]

theorem simple_of_isIrr (τ : FDRep ℂ G) (h : GlobalTheory.GLq.IsIrr τ.character) : Simple τ := by
  obtain ⟨V, hV, hch⟩ := h
  rw [FDRep.simple_iff_char_is_norm_one] at hV ⊢
  simpa only [hch] using hV

theorem central_scalar (τ : FDRep ℂ G) [Simple τ] (f : G → ℂ) (hf : ∀ x y : G, f (y * x * y⁻¹) = f x) :
    ∃ c : ℂ, (∀ v : τ, ∑ y, f y • τ.ρ y⁻¹ v = c • v) ∧
      c * (Module.finrank ℂ τ : ℂ) = ∑ y, f y * τ.character y⁻¹ := by
  classical
  let A : τ →ₗ[ℂ] τ := ∑ y, f y • τ.ρ y⁻¹
  have hAapp : ∀ v, A v = ∑ y, f y • τ.ρ y⁻¹ v := fun v => by
    simp only [A, LinearMap.sum_apply, LinearMap.smul_apply]
  have hA : ∀ h, A ∘ₗ τ.ρ h = τ.ρ h ∘ₗ A := by
    intro h
    refine LinearMap.ext fun v => ?_
    rw [LinearMap.comp_apply, LinearMap.comp_apply, hAapp, hAapp, map_sum]
    rw [← Equiv.sum_comp (MulAut.conj h).toEquiv]
    refine Finset.sum_congr rfl fun y _ => ?_
    have e1 : f ((MulAut.conj h).toEquiv y) = f y := by
      simpa using hf y h
    rw [e1, map_smul]
    congr 1
    rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
    congr 2
    simp [mul_assoc]
  let F : τ ⟶ τ := ⟨FGModuleCat.ofHom A, fun g => by
    ext x
    change A (τ.ρ g x) = τ.ρ g (A x)
    exact LinearMap.congr_fun (hA g) x⟩
  obtain ⟨c, hc⟩ := endomorphism_simple_eq_smul_id ℂ F
  have hAv : ∀ v, A v = c • v := fun v => by
    have : F.hom.hom.hom v = c • v := by rw [← hc]; rfl
    exact this
  refine ⟨c, fun v => by rw [← hAv, hAapp], ?_⟩
  have hAc : A = c • LinearMap.id := LinearMap.ext fun v => by rw [hAv]; rfl
  have htr : LinearMap.trace ℂ τ A = c * Module.finrank ℂ τ := by
    rw [hAc, map_smul, LinearMap.trace_id, smul_eq_mul]
  rw [← htr]
  simp only [A, map_sum, map_smul, smul_eq_mul]
  rfl

end DiscreteGroups.sglob.DzType.Kon
