import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FiltrationZeroMembership
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ToMatrixRepOf
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedExtFixedFieldFrobeniusPowDegree
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMon

theorem coef_unr_continuous : ∀ (l : ℕ) [Fact l.Prime] (r : ℕ), 0 < r → ∃ (ω : Fin r → ↥(MaximalUnramifiedExtension l)) (W : GL (Fin r) ↥(MaximalUnramifiedExtension l)),
    (∀ m k : Fin r, (W : Matrix (Fin r) (Fin r) ↥(MaximalUnramifiedExtension l)) m k = fr l m (ω k)) ∧ (∀ k, fr l r (ω k) = ω k) ∧
    ∀ (X : Type) [TopologicalSpace X] (x : X → ↥(MaximalUnramifiedExtension l)), (∀ t, fr l r (x t) = x t) →
      Continuous (fun t => ((x t : ↥(MaximalUnramifiedExtension l)) : Om l)) →
      ∃ a : X → Fin r → ℚ_[l], Continuous a ∧ ∀ t (m : Fin r),
        fr l m (x t) = ∑ k, (W : Matrix (Fin r) (Fin r) ↥(MaximalUnramifiedExtension l)) m k * algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) (a t k) := by
  intro l _ r hr
  obtain ⟨E, ω, -, -, -, hω, hli, hspan, hdet⟩ := UnrDeg.fixed_field_deg l r hr
  refine ⟨ω, Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet, fun m k => rfl, hω, ?_⟩
  intro X _ x hx hcont

  set v : Fin r → Om l := fun k => ((ω k : ↥(MaximalUnramifiedExtension l)) : Om l) with hv
  have hliv : LinearIndependent ℚ_[l] v := by
    have := hli.map' (MaximalUnramifiedExtension l).val.toLinearMap (LinearMap.ker_eq_bot.2 (fun a b h => Subtype.ext h))
    exact this
  set ψ : (Fin r → ℚ_[l]) →ₗ[ℚ_[l]] Om l := Fintype.linearCombination ℚ_[l] v with hψ
  have hinj : Function.Injective ψ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro g hg
    rw [hψ, Fintype.linearCombination_apply] at hg
    funext i
    exact Fintype.linearIndependent_iff.1 hliv g hg i
  let e := LinearEquiv.ofInjective ψ hinj
  haveI : FiniteDimensional ℚ_[l] ↥(LinearMap.range ψ) := LinearEquiv.finiteDimensional e
  have hmem : ∀ t, ((x t : ↥(MaximalUnramifiedExtension l)) : Om l) ∈ LinearMap.range ψ := by
    intro t
    obtain ⟨a, ha⟩ := hspan (x t) (hx t)
    refine ⟨a, ?_⟩
    rw [hψ, Fintype.linearCombination_apply, ha]
    simp [hv]
  refine ⟨fun t => e.symm ⟨((x t : ↥(MaximalUnramifiedExtension l)) : Om l), hmem t⟩, ?_, ?_⟩
  · exact (LinearMap.continuous_of_finiteDimensional (e.symm : ↥(LinearMap.range ψ) →ₗ[ℚ_[l]] (Fin r → ℚ_[l]))).comp
      (hcont.subtype_mk _)
  · intro t m
    have key : ψ (e.symm ⟨((x t : ↥(MaximalUnramifiedExtension l)) : Om l), hmem t⟩) = ((x t : ↥(MaximalUnramifiedExtension l)) : Om l) := by
      have h1 := congrArg Subtype.val (e.apply_symm_apply ⟨((x t : ↥(MaximalUnramifiedExtension l)) : Om l), hmem t⟩)
      rw [LinearEquiv.ofInjective_apply] at h1
      exact h1
    set a := e.symm ⟨((x t : ↥(MaximalUnramifiedExtension l)) : Om l), hmem t⟩
    have hxt : x t = ∑ k, a k • ω k := by
      apply Subtype.ext
      rw [← key, hψ, Fintype.linearCombination_apply]
      simp [hv]
    rw [hxt, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Algebra.smul_def, map_mul, fr_q, mul_comm]
    rfl

end GlobalTheory.PMon
