import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExpStar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulMemLatIff

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage

namespace GlobalTheory.ExpImage

variable {l : ℕ} [Fact l.Prime]

theorem norm_algHom_self (F : IntermediateField ℚ_[l] (Om l)) (σ : ↥F →ₐ[ℚ_[l]] ↥F) (c : ↥F) :
    ‖((σ c : ↥F) : Om l)‖ = ‖(c : Om l)‖ := by
  rw [← PadicAlgCl.spectralNorm_eq, ← PadicAlgCl.spectralNorm_eq]
  unfold spectralNorm
  have h1 := minpoly.algHom_eq F.val F.val.injective (σ c)
  have h2 := minpoly.algHom_eq F.val F.val.injective c
  have h3 := minpoly.algHom_eq σ σ.injective c
  simp only [IntermediateField.coe_val] at h1 h2
  exact congrArg spectralValue (h1.trans (h3.trans h2.symm))

theorem norm_l_pow_lt_one {j : ℕ} (hj : 1 ≤ j) : ‖(l : Om l) ^ j‖ < 1 := by
  rw [norm_pow]
  apply pow_lt_one₀ (norm_nonneg _) _ (by omega)
  rw [← map_natCast (algebraMap ℚ_[l] (Om l)), PadicAlgCl.norm_extends]
  exact Padic.norm_p_lt_one

theorem norm_sub_pow_mul_algHom (F : IntermediateField ℚ_[l] (Om l)) (σ : ↥F →ₐ[ℚ_[l]] ↥F)
    {j : ℕ} (hj : 1 ≤ j) (d : ↥F) :
    ‖((d - (l : ↥F) ^ j * σ d : ↥F) : Om l)‖ = ‖(d : Om l)‖ := by
  by_cases hd : d = 0
  · simp [hd]
  have hd' : 0 < ‖(d : Om l)‖ := norm_pos_iff.2 (by exact_mod_cast hd)
  have hlt : ‖-((l : Om l) ^ j * ((σ d : ↥F) : Om l))‖ < ‖(d : Om l)‖ := by
    rw [norm_neg, norm_mul, norm_algHom_self]
    exact mul_lt_of_lt_one_left hd' (norm_l_pow_lt_one hj)
  have e : ((d - (l : ↥F) ^ j * σ d : ↥F) : Om l) =
      (d : Om l) + -((l : Om l) ^ j * ((σ d : ↥F) : Om l)) := by
    push_cast
    ring
  rw [e, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hlt.ne', max_eq_left hlt.le]

theorem frK_isometric_and_one_sub_surjective (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) :
    (∀ c : ↥(K0 K), ‖((frK P K c : ↥(K0 K)) : Om l)‖ = ‖(c : Om l)‖) ∧
    ∀ j : ℕ, 1 ≤ j → ∀ c : ↥(K0 K), ‖(c : Om l)‖ ≤ 1 →
      ∃ d : ↥(K0 K), ‖(d : Om l)‖ ≤ 1 ∧ d - (l : ↥(K0 K)) ^ j * frK P K d = c := by
  refine ⟨norm_algHom_self _ _, fun j hj c hc => ?_⟩
  haveI : FiniteDimensional ℚ_[l] ↥(K0 K) := (P.PD K).finK₀
  let T : ↥(K0 K) →ₗ[ℚ_[l]] ↥(K0 K) :=
    LinearMap.id - (LinearMap.mulLeft ℚ_[l] ((l : ↥(K0 K)) ^ j)).comp (frK P K).toLinearMap
  have hT : ∀ d, T d = d - (l : ↥(K0 K)) ^ j * frK P K d := fun d => rfl
  have hinj : Function.Injective T := by
    rw [injective_iff_map_eq_zero]
    intro d hd
    have := norm_sub_pow_mul_algHom _ (frK P K) hj d
    rw [← hT, hd] at this
    have h0 : (d : Om l) = 0 := by
      rw [← norm_eq_zero, ← this]; simp
    exact_mod_cast h0
  obtain ⟨d, hd⟩ := LinearMap.injective_iff_surjective.1 hinj c
  rw [hT] at hd
  refine ⟨d, ?_, hd⟩
  rw [← norm_sub_pow_mul_algHom _ (frK P K) hj d, hd]
  exact hc

end GlobalTheory.ExpImage
