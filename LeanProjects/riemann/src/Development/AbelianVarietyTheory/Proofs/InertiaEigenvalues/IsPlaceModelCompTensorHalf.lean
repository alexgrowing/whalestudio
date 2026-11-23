import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsPlaceModelCompRestrictToHalfLatticeIndicator
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.ExportSeries
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

noncomputable section

namespace GlobalTheory.TwoStepModel

variable {D : D7} {m n : ℕ}

def tensorHalf (a' b : AE D) (Ψ : Mx D m n → ℂ) : (Mx D m n → ℂ) →ₗ[ℂ] (Mx D m n → ℂ) where
  toFun Φ x := Φ (a' • x) * Ψ (b • x) * (if IsHalf (a' + b) x then 1 else 0)
  map_add' Φ Φ' := by funext x; simp only [Pi.add_apply]; ring
  map_smul' c Φ := by funext x; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

theorem tensorHalf_apply (a' b : AE D) (Ψ Φ : Mx D m n → ℂ) (x : Mx D m n) :
    tensorHalf a' b Ψ Φ x = Φ (a' • x) * Ψ (b • x) * (if IsHalf (a' + b) x then 1 else 0) := rfl

open GlobalTheory.ExportSeries.RestrictHalfModel

theorem tensorHalf_halfInd (a' b : AE D) (Λ : AddSubgroup (Mx D m n)) (Ψ : Mx D m n → ℂ) :
    tensorHalf a' b Ψ ((1 : ℂ) • halfInd a' Λ) = restrictHalf b a' Λ Ψ := by
  funext x
  simp only [tensorHalf_apply, restrictHalf_apply, one_smul, add_comm b a']
  ring

theorem isSBHalf_tensorHalf {a' b : AE D} (ha' : a' * a' = a') (hb : b * b = b) {Λ : AddSubgroup (Mx D m n)}
    (hΛ : ∀ e : AE D, e * e = e → ∀ u ∈ Λ, e • u ∈ Λ) {Φ Ψ : Mx D m n → ℂ} (hΦ : IsSBHalf a' Λ Φ)
    (hΨ : IsSBHalf b Λ Ψ) : IsSBHalf (a' + b) Λ (tensorHalf a' b Ψ Φ) := by
  obtain ⟨-, k, hk, hinv, hlat⟩ := hΦ
  obtain ⟨-, k', hk', hinv', hlat'⟩ := hΨ
  refine ⟨fun t ht => ?_, k * k', Nat.mul_pos hk hk', fun u hu hhu t => ?_, fun t ht => ?_⟩
  · rw [tensorHalf_apply] at ht
    by_contra h
    exact ht (by rw [if_neg h, mul_zero])
  · rw [isHalf_iff'] at hhu
    simp only [tensorHalf_apply]
    have e1 : a' • (t + (k * k') • u) = a' • t + k • (a' • (k' • u)) := by
      rw [smul_add, mul_comm k k', mul_smul, smul_comm k' k u, smul_comm a' k]
    have e2 : b • (t + (k * k') • u) = b • t + k' • (b • (k • u)) := by
      rw [smul_add, mul_smul, smul_comm k k' u, smul_comm b k']
    have e3 : (a' + b) • ((k * k') • u) = (k * k') • u := by rw [smul_comm, hhu]
    rw [e1, hinv _ (hΛ a' ha' _ (Λ.nsmul_mem hu k')) (isHalf_smul ha' _), e2,
      hinv' _ (hΛ b hb _ (Λ.nsmul_mem hu k)) (isHalf_smul hb _), isHalf_add_iff e3]
  · rw [tensorHalf_apply] at ht
    have h1 : Φ (a' • t) ≠ 0 := fun h => ht (by rw [h, zero_mul, zero_mul])
    have h2 : Ψ (b • t) ≠ 0 := fun h => ht (by rw [h, mul_zero, zero_mul])
    have h3 : IsHalf (a' + b) t := by
      by_contra h
      exact ht (by rw [if_neg h, mul_zero])
    rw [isHalf_iff', add_smul] at h3
    rw [← h3, smul_add, mul_smul, mul_comm k k', mul_smul k']
    exact Λ.add_mem (by rw [smul_comm k k']; exact Λ.nsmul_mem (hlat _ h1) k') (by rw [smul_comm k' k]; exact Λ.nsmul_mem (hlat' _ h2) k)

theorem isPlaceModel_comp_tensorHalf {S T : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {Λ : AddSubgroup (WO S T)}
    {f₀ : WO S T → ℂ} {a' b : AE D} {T₀ : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)} (ha' : a' * a' = a') (hb : b * b = b)
    (hab : a' * b = 0) (hΛ : ∀ e : AE D, e * e = e → ∀ u ∈ Λ, e • u ∈ Λ) {Ψ : WO S T → ℂ} (hΨ : IsSBHalf b Λ Ψ)
    (hT : IsPlaceModel ψ (symplO S T) (heisO ψ S T) (a' + b) Λ 1 f₀ T₀) :
    IsPlaceModel ψ (symplO S T) (heisO ψ S T) a' Λ 1 (T₀ (restrictHalf b a' Λ Ψ)) (T₀ ∘ₗ tensorHalf a' b Ψ) := by
  have hsb : ∀ Φ, IsSBHalf a' Λ Φ → IsSBHalf (a' + b) Λ (tensorHalf a' b Ψ Φ) :=
    fun Φ hΦ => isSBHalf_tensorHalf ha' hb hΛ hΦ hΨ
  refine ⟨fun Φ hΦ x hx => ?_, fun Φ hΦ y hy => ?_, ?_⟩
  · obtain ⟨hbx, hax⟩ := smul_of_half hab hx
    have hxa : IsHalf (a' + b) x := (isHalf_iff' _ _).2 hax
    have e : tensorHalf a' b Ψ (fun t => Φ (t + x)) = fun t => tensorHalf a' b Ψ Φ (t + x) := by
      funext z
      simp only [tensorHalf_apply]
      rw [smul_add, (isHalf_iff' _ _).1 hx, smul_add b, hbx, add_zero, isHalf_add_iff hax]
    rw [LinearMap.comp_apply, LinearMap.comp_apply, e]
    exact hT.trans _ (hsb Φ hΦ) x hxa
  · have hy' : IsHalf (cA D (a' + b)) y := by
      rw [isHalf_iff'] at hy ⊢
      rw [map_add, add_smul, hy, ← hy, smul_smul, ← map_mul, mul_comm, hab, map_zero, zero_smul, add_zero]
    have e : tensorHalf a' b Ψ (fun t => ψ (symplO S T t y) * Φ t) =
        fun t => ψ (symplO S T t y) * tensorHalf a' b Ψ Φ t := by
      funext z
      simp only [tensorHalf_apply]
      rw [GlobalTheory.SplitScalar.symplO_smul, (isHalf_iff' _ _).1 hy]
      ring
    rw [LinearMap.comp_apply, LinearMap.comp_apply, e]
    exact hT.modul _ (hsb Φ hΦ) y hy'
  · rw [LinearMap.comp_apply, tensorHalf_halfInd]

end GlobalTheory.TwoStepModel

end
