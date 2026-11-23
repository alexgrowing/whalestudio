import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SeriesKillsAvg
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraFrobeniusReciprocity
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteIrrCharactersAndFinsumCentralIdempotentsEq
open GlobalTheory.GLq GlobalTheory.MirAvg Polynomial

noncomputable section

namespace GlobalTheory.GLq.HCFrobWeight

open scoped Classical

section Reg

variable {H : Type} [Group H] [Fintype H]

theorem sum_irr_coeff (h : H) :
    ∑ σ ∈ (irr_finite_and_finsum_zOf_eq_one H).1.toFinset, (zOf σ).coeff h = if h = 1 then 1 else 0 := by
  obtain ⟨hfin, hsum⟩ := irr_finite_and_finsum_zOf_eq_one H
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin] at hsum
  have e := congrArg (fun z : MonoidAlgebra ℂ H => z.coeff h) hsum
  simp only [MonoidAlgebra.coeff_sum, Finsupp.finset_sum_apply] at e
  rw [e, MonoidAlgebra.one_def, MonoidAlgebra.coeff_single, Finsupp.single_apply]
  by_cases hh : h = 1
  · simp [hh]
  · simp [hh, Ne.symm hh]

theorem exists_irr_sum_ne_zero (F : H → ℂ) (hF : F 1 ≠ 0) :
    ∃ σ : H → ℂ, IsIrr σ ∧ ∑ h, F h * σ h⁻¹ ≠ 0 := by
  by_contra hc
  push_neg at hc
  apply hF
  set s := (irr_finite_and_finsum_zOf_eq_one H).1.toFinset with hs
  have h0 : ∑ σ ∈ s, σ 1 / (Fintype.card H : ℂ) * ∑ h, F h * σ h⁻¹ = 0 := by
    refine Finset.sum_eq_zero fun σ hσ => ?_
    rw [hc σ (by simpa [hs] using hσ), mul_zero]
  rw [← h0]
  have e : ∑ σ ∈ s, σ 1 / (Fintype.card H : ℂ) * ∑ h, F h * σ h⁻¹ =
      ∑ h, F h * ∑ σ ∈ s, (zOf σ).coeff h := by
    simp_rw [Finset.mul_sum, ZSumOne.zOf_coeff]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun h _ => Finset.sum_congr rfl fun σ _ => ?_
    ring
  rw [e, hs]
  simp_rw [sum_irr_coeff]
  simp

end Reg

variable {g : ℕ} [Fact g.Prime]

theorem isClass_of_isIrr {n : ℕ} {ψ : Gn g n → ℂ} (hψ : IsIrr ψ) : IsClass ψ := by
  obtain ⟨V, _, hV⟩ := hψ
  intro x y
  rw [← hV, ← hV]
  exact FDRep.char_conj V x y

theorem ip_hc_eq_left (a b n : ℕ) (hn : n = a + b) (χ : Gn g n → ℂ) (hχ : IsClass χ) (α : Gn g a → ℂ)
    (β : Gn g b → ℂ) :
    ip χ (hc a b α β n) = (Fintype.card (Gn g a × Gn g b) : ℂ)⁻¹ *
      ∑ h : Gn g a, (∑ y : Gn g b, res a b χ h y * β y⁻¹) * α h⁻¹ := by
  rw [hc, FrobRecHC.hcT_adjoint g a b n hn χ _ hχ]
  unfold ip
  rw [Fintype.sum_prod_type]
  congr 1
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun y _ => ?_
  simp only [Prod.fst_inv, Prod.snd_inv]
  ring

theorem ip_hc_eq_right (a b n : ℕ) (hn : n = a + b) (χ : Gn g n → ℂ) (hχ : IsClass χ) (α : Gn g a → ℂ)
    (β : Gn g b → ℂ) :
    ip χ (hc a b α β n) = (Fintype.card (Gn g a × Gn g b) : ℂ)⁻¹ *
      ∑ y : Gn g b, (∑ h : Gn g a, res a b χ h y * α h⁻¹) * β y⁻¹ := by
  rw [hc, FrobRecHC.hcT_adjoint g a b n hn χ _ hχ]
  unfold ip
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  congr 1
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun h _ => ?_
  simp only [Prod.fst_inv, Prod.snd_inv]
  ring

theorem thetaInv_det_inv (θ : (ZMod g)ˣ →* ℂˣ) (y : Gn g 1) :
    ((θ⁻¹ (Matrix.GeneralLinearGroup.det y⁻¹) : ℂˣ) : ℂ) = ((θ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ) := by
  simp [map_inv]

end GlobalTheory.GLq.HCFrobWeight

namespace GlobalTheory.GLq.HCFrobWeight

open scoped Classical

theorem exists_irr_hc_thetaInv : ∀ (g : ℕ) [Fact g.Prime] (n : ℕ) (ψ : Gn g (n + 1) → ℂ), IsIrr ψ → ∀ θ : (ZMod g)ˣ →* ℂˣ,
    (∑ x : Gn g 1, ((θ (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) * res n 1 ψ 1 x ≠ 0 →
      ∃ σ : Gn g n → ℂ, IsIrr σ ∧
        ip ψ (hc n 1 σ (fun y : Gn g 1 => ((θ⁻¹ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ)) (n + 1)) ≠ 0) ∧
    (∑ x : Gn g 1, ((θ (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) * res 1 n ψ x 1 ≠ 0 →
      ∃ σ : Gn g n → ℂ, IsIrr σ ∧
        ip ψ (hc 1 n (fun y : Gn g 1 => ((θ⁻¹ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ)) σ (n + 1)) ≠ 0) := by
  intro g _ n ψ hψ θ
  have hcl := isClass_of_isIrr hψ
  constructor
  · intro hS
    obtain ⟨σ, hσ, hne⟩ := exists_irr_sum_ne_zero
      (fun h : Gn g n => ∑ y : Gn g 1, res n 1 ψ h y * ((θ⁻¹ (Matrix.GeneralLinearGroup.det y⁻¹) : ℂˣ) : ℂ))
      (by simp_rw [thetaInv_det_inv]; simpa [mul_comm] using hS)
    refine ⟨σ, hσ, ?_⟩
    rw [ip_hc_eq_left n 1 (n + 1) rfl ψ hcl]
    exact mul_ne_zero (inv_ne_zero (Nat.cast_ne_zero.2 Fintype.card_ne_zero)) hne
  · intro hS
    obtain ⟨σ, hσ, hne⟩ := exists_irr_sum_ne_zero
      (fun y : Gn g n => ∑ h : Gn g 1, res 1 n ψ h y * ((θ⁻¹ (Matrix.GeneralLinearGroup.det h⁻¹) : ℂˣ) : ℂ))
      (by simp_rw [thetaInv_det_inv]; simpa [mul_comm] using hS)
    refine ⟨σ, hσ, ?_⟩
    rw [ip_hc_eq_right 1 n (n + 1) (by omega) ψ hcl]
    exact mul_ne_zero (inv_ne_zero (Nat.cast_ne_zero.2 Fintype.card_ne_zero)) hne

end GlobalTheory.GLq.HCFrobWeight
