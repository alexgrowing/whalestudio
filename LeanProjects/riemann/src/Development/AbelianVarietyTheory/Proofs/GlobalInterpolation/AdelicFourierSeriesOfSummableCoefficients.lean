import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DecayZero
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RationalVectorsAdelesFundamentalDomainMassOneStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IntegralAdelicVectorsCharacterOrthogonalityStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AdelicPeriodicContinuousEqZeroOfFourierCoeffStatement
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.SWQ
open scoped TensorProduct NNReal ENNReal

noncomputable section
namespace GlobalTheory.SWQ.FourierSeries

variable {F : Type} [Field F] [NumberField F] {N : ℕ}

theorem bd_rat_add (a : Fin N → F) (η ξ : Fin N → F) (u : Fin N → AF F) :
    Bd (AF F) a (rat η + u) (rat ξ) = algebraMap F (AF F) (Bd F a η ξ) + Bd (AF F) a u (rat ξ) := by
  simp only [Bd, rat, Pi.add_apply, map_sum, map_mul, mul_add, add_mul, Finset.sum_add_distrib,
    Algebra.algebraMap_self, RingHom.id_apply]

theorem bd_sub (a : Fin N → F) (ξ' ξ : Fin N → F) (u : Fin N → AF F) :
    Bd (AF F) a u (rat ξ') + -Bd (AF F) a u (rat ξ) = Bd (AF F) a u (rat (ξ' - ξ)) := by
  simp only [Bd, rat, Pi.sub_apply, map_sub, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun l _ => by ring

theorem bd_zero (a : Fin N → F) (u : Fin N → AF F) : Bd (AF F) a u (rat 0) = 0 := by
  simp [Bd, rat]

theorem continuous_bd (a : Fin N → F) (ξ : Fin N → F) :
    Continuous fun u : Fin N → AF F => Bd (AF F) a u (rat ξ) := by
  unfold Bd
  refine continuous_finset_sum _ fun l _ => ?_
  exact (continuous_const.mul (continuous_apply l)).mul continuous_const

end GlobalTheory.SWQ.FourierSeries

namespace GlobalTheory.SWQ.FourierSeries

theorem countable_fn (F : Type) [Field F] [NumberField F] (N : ℕ) : Countable (Fin N → F) := by
  haveI : Countable F := (Module.finBasis ℚ F).equivFun.toEquiv.injective.countable
  infer_instance

theorem fourier_series : ∀ (F : Type) [Field F] [NumberField F] (N : ℕ) (ψ : AddChar (AF F) ℂ) (lam : InfinitePlace F → ℝ) (ν : Measure (AF F)) (a : Fin N → F), Ctx ψ lam ν a → ∀ D : Set (Fin N → AF F), IsAddFundamentalDomain (AddSubgroup.closure (Set.range (rat : (Fin N → F) → (Fin N → AF F)))) D (muV N ν) → muV N ν D = 1 → ∀ (P : (Fin N → AF F) → ℂ) (c : (Fin N → F) → ℂ), Continuous P → (∀ ξ u, P (rat ξ + u) = P u) → (∀ ξ, ∫ u in D, P u * ψ (-(Bd (AF F) a u (rat ξ))) ∂(muV N ν) = c ξ) → Summable (fun ξ => ‖c ξ‖) → ∀ u, P u = ∑' ξ, c ξ * ψ (Bd (AF F) a u (rat ξ)) := by
  intro F _ _ N ψ lam ν a hC D hD hD1 P c hP hper hc hsum
  classical
  have hC' := hC
  obtain ⟨_, ⟨hψc, hψn, hψF, -⟩, -, hcov, -⟩ := hC'
  obtain ⟨-, -, -, ⟨K, hK, hKc⟩, -⟩ := GlobalTheory.T.rationalVectors_adeles_fundamentalDomain_mass_one F N ν hcov
  haveI : Countable (Fin N → F) := countable_fn F N
  haveI : IsFiniteMeasure ((muV N ν).restrict D) := isFiniteMeasure_restrict.mpr (by rw [hD1]; simp)
  have hmass : ((muV N ν).restrict D) Set.univ = 1 := by rw [Measure.restrict_apply_univ, hD1]
  have he : ∀ ξ, Continuous fun u : Fin N → AF F => ψ (Bd (AF F) a u (rat ξ)) :=
    fun ξ => hψc.comp (continuous_bd a ξ)
  set S : (Fin N → AF F) → ℂ := fun u => ∑' ξ, c ξ * ψ (Bd (AF F) a u (rat ξ)) with hSdef
  have hS : Continuous S := continuous_tsum (fun ξ => continuous_const.mul (he ξ)) hsum
    (fun ξ u => by simp [norm_mul, hψn])
  have hSper : ∀ η u, S (rat η + u) = S u := by
    intro η u
    simp only [hSdef, bd_rat_add, AddChar.map_add_eq_mul, hψF, one_mul]

  obtain ⟨M, hM⟩ : ∃ M, ∀ u, ‖P u‖ ≤ M := by
    obtain ⟨M, hM⟩ := (hK.image hP.norm).bddAbove
    refine ⟨M, fun u => ?_⟩
    obtain ⟨ξ, hξ⟩ := hKc u
    have : P u = P (u - rat ξ) := by
      rw [← hper ξ (u - rat ξ)]; congr 1; abel
    rw [this]; exact hM ⟨_, hξ, rfl⟩
  set Q : (Fin N → AF F) → ℂ := fun u => P u - S u with hQdef
  have hQc : Continuous Q := hP.sub hS
  have hQper : ∀ ξ u, Q (rat ξ + u) = Q u := fun ξ u => by simp only [hQdef, hper, hSper]
  have hint : ∀ f : (Fin N → AF F) → ℂ, Continuous f → ∀ B : ℝ, (∀ u, ‖f u‖ ≤ B) →
      Integrable f ((muV N ν).restrict D) :=
    fun f hf B hB => Integrable.of_bound hf.aestronglyMeasurable B (Eventually.of_forall hB)
  have hcoefS : ∀ ξ, ∫ u in D, S u * ψ (-(Bd (AF F) a u (rat ξ))) ∂(muV N ν) = c ξ := by
    intro ξ
    have hterm : ∀ ξ' u, c ξ' * ψ (Bd (AF F) a u (rat ξ')) * ψ (-(Bd (AF F) a u (rat ξ))) =
        c ξ' * ψ (Bd (AF F) a u (rat (ξ' - ξ))) := by
      intro ξ' u
      rw [mul_assoc, ← AddChar.map_add_eq_mul, bd_sub]
    have hsw : ∀ u, S u * ψ (-(Bd (AF F) a u (rat ξ))) =
        ∑' ξ', c ξ' * ψ (Bd (AF F) a u (rat (ξ' - ξ))) := by
      intro u
      simp only [hSdef, ← tsum_mul_right, hterm]
    simp_rw [hsw]
    have hInt : ∀ ξ', Integrable (fun u => c ξ' * ψ (Bd (AF F) a u (rat (ξ' - ξ))))
        ((muV N ν).restrict D) :=
      fun ξ' => hint _ (continuous_const.mul (he _)) ‖c ξ'‖ (fun u => by simp [norm_mul, hψn])
    have hnorm : ∀ ξ', ∫ u in D, ‖c ξ' * ψ (Bd (AF F) a u (rat (ξ' - ξ)))‖ ∂(muV N ν) = ‖c ξ'‖ := by
      intro ξ'
      simp only [norm_mul, hψn, mul_one]
      rw [integral_const, smul_eq_mul, measureReal_def, hmass]; simp
    rw [← integral_tsum_of_summable_integral_norm hInt (by simp_rw [hnorm]; exact hsum)]
    have hval : ∀ ξ', ∫ u in D, c ξ' * ψ (Bd (AF F) a u (rat (ξ' - ξ))) ∂(muV N ν) =
        if ξ' = ξ then c ξ else 0 := by
      intro ξ'
      rw [integral_const_mul]
      split_ifs with h
      · subst h
        simp only [sub_self, bd_zero, AddChar.map_zero_eq_one]
        simp [integral_const, measureReal_def, hmass]
      · rw [GlobalTheory.T.integral_adelicVectors_character_orthogonality F N ψ lam ν a hC D hD hD1 (ξ' - ξ) (sub_ne_zero.mpr h), mul_zero]
    simp_rw [hval]
    simp
  have hQcoef : ∀ ξ : Fin N → F, ∫ u in D, Q u * ψ (-(Bd (AF F) a u (rat ξ))) ∂(muV N ν) = 0 := by
    intro ξ
    have h1 : Integrable (fun u => P u * ψ (-(Bd (AF F) a u (rat ξ)))) ((muV N ν).restrict D) :=
      hint _ (hP.mul (hψc.comp (continuous_bd a ξ).neg)) M (fun u => by simpa [norm_mul, hψn] using hM u)
    have hSb : ∀ u, ‖S u‖ ≤ ∑' ξ, ‖c ξ‖ := fun u =>
      (norm_tsum_le_tsum_norm (hsum.of_nonneg_of_le (fun _ => norm_nonneg _)
        (fun ξ' => by simp [norm_mul, hψn]))).trans
        (le_of_eq (tsum_congr fun ξ' => by simp [norm_mul, hψn]))
    have h2 : Integrable (fun u => S u * ψ (-(Bd (AF F) a u (rat ξ)))) ((muV N ν).restrict D) :=
      hint _ (hS.mul (hψc.comp (continuous_bd a ξ).neg)) _ (fun u => by simpa [norm_mul, hψn] using hSb u)
    simp only [hQdef, sub_mul]
    rw [integral_sub h1 h2, hc, hcoefS, sub_self]
  have hQ0 := GlobalTheory.T.adelicPeriodic_continuous_eq_zero_of_fourier_coeff F N ψ lam ν a hC D hD hD1 Q hQc hQper hQcoef
  intro u
  have := congrFun hQ0 u
  simp only [hQdef, Pi.zero_apply, sub_eq_zero] at this
  exact this

end GlobalTheory.SWQ.FourierSeries
