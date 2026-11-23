import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DecayZero
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RationalVectorsAdelesFundamentalDomainMassOne
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RapidDecayAdelicIntegrablePeriodisationContinuouStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IntegralAdelicVectorsCharacterOrthogonalityStatement

open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.SWQ
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.SWQ

theorem countable_numberField (F : Type) [Field F] [NumberField F] : Countable F := by
  exact (Module.finBasis ℚ F).equivFun.injective.countable

theorem Bd_comm {F : Type} [Field F] {N : ℕ} (R : Type) [CommRing R] [Algebra F R] (a : Fin N → F)
    (u u' : Fin N → R) : Bd R a u u' = Bd R a u' u := by
  unfold Bd
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

theorem continuous_Bd_left {F : Type} [Field F] [NumberField F] {N : ℕ} (a : Fin N → F)
    (u : Fin N → AF F) : Continuous fun y : Fin N → AF F => Bd (AF F) a u y := by
  unfold Bd
  exact continuous_finsetSum _ fun l _ => continuous_const.mul (continuous_apply l)

theorem integral_twisted_periodise {F : Type} [Field F] [NumberField F] {N : ℕ} {ψ : AddChar (AF F) ℂ}
    {lam : InfinitePlace F → ℝ} {ν : Measure (AF F)} {a : Fin N → F} (hC : Ctx ψ lam ν a)
    (G : (Fin N → AF F) → ℂ) (hG : Decay G) (D : Set (Fin N → AF F))
    (hD : IsAddFundamentalDomain (AddSubgroup.closure (Set.range (rat : (Fin N → F) → (Fin N → AF F))))
      D (muV N ν)) (h1 : muV N ν D = 1) (x : Fin N → AF F) :
    ∫ y in D, (∑' ξ : Fin N → F, ψ (Bd (AF F) a (rat ξ) y) * G (rat ξ + x)) ∂(muV N ν) = G x := by
  have hTR : IsTotallyReal F := hC.1
  have hψc : Continuous ψ := hC.2.1.1
  have hψn : ∀ z, ‖ψ z‖ = 1 := hC.2.1.2.1
  have : Countable F := countable_numberField F
  have : IsFiniteMeasure ((muV N ν).restrict D) :=
    ⟨by rw [Measure.restrict_apply_univ, h1]; exact ENNReal.one_lt_top⟩
  have hsum : Summable fun ξ : Fin N → F => ‖G (rat ξ + x)‖ :=
    (GlobalTheory.T.rapidDecay_adelic_integrable_periodisation_continuous F N hTR G hG).2.1 x
  have hnorm : ∀ (ξ : Fin N → F) (y : Fin N → AF F),
      ‖ψ (Bd (AF F) a (rat ξ) y) * G (rat ξ + x)‖ = ‖G (rat ξ + x)‖ := by
    intro ξ y
    rw [norm_mul, hψn, one_mul]
  have hint : ∀ ξ : Fin N → F,
      Integrable (fun y => ψ (Bd (AF F) a (rat ξ) y) * G (rat ξ + x)) ((muV N ν).restrict D) := by
    intro ξ
    refine Integrable.mono' (integrable_const ‖G (rat ξ + x)‖) ?_
      (ae_of_all _ fun y => (hnorm ξ y).le)
    exact ((hψc.comp (continuous_Bd_left a (rat ξ))).mul continuous_const).aestronglyMeasurable
  have hsum' : Summable fun ξ : Fin N → F =>
      ∫ y in D, ‖ψ (Bd (AF F) a (rat ξ) y) * G (rat ξ + x)‖ ∂(muV N ν) := by
    refine hsum.congr fun ξ => ?_
    simp_rw [hnorm]
    simp [Measure.real, h1]
  rw [← integral_tsum_of_summable_integral_norm hint hsum']
  rw [tsum_eq_single 0]
  · have hr : (rat (0 : Fin N → F) : Fin N → AF F) = 0 := by
      funext l
      simp [rat]
    simp [hr, Bd, h1, Measure.real]
  · intro ξ hξ
    rw [integral_mul_const]
    simp_rw [Bd_comm (AF F) a (rat ξ)]
    rw [GlobalTheory.T.integral_adelicVectors_character_orthogonality F N ψ lam ν a hC D hD h1 ξ hξ, zero_mul]

theorem eq_of_theta_rho : ∀ (F : Type) [Field F] [NumberField F] (N : ℕ) (ψ : AddChar (AF F) ℂ)
    (lam : InfinitePlace F → ℝ) (ν : Measure (AF F)) (a : Fin N → F), Ctx ψ lam ν a →
    ∀ G G' : (Fin N → AF F) → ℂ, Decay G → Decay G' →
      (∀ x y, th (rho ψ a x y G) = th (rho ψ a x y G')) → G = G' := by
  intro F _ _ N ψ lam ν a hC G G' hG hG' hth
  obtain ⟨D, -, hD, h1⟩ :=
    (GlobalTheory.SWQ.rat_lattice_fundamentalDomain F N ν hC.2.2.2.1).2.2.2.2
  funext x
  have key : ∀ y : Fin N → AF F,
      (∑' ξ : Fin N → F, ψ (Bd (AF F) a (rat ξ) y) * G (rat ξ + x)) =
        ∑' ξ : Fin N → F, ψ (Bd (AF F) a (rat ξ) y) * G' (rat ξ + x) := by
    intro y
    set c : AF F := algebraMap F (AF F) (1 / 2) * Bd (AF F) a x y with hc
    have hne : ψ c ≠ 0 := by
      intro h0
      have h := hC.2.1.2.1 c
      rw [h0, norm_zero] at h
      exact zero_ne_one h
    have e : ∀ H : (Fin N → AF F) → ℂ,
        th (rho ψ a x y H) = ψ c * ∑' ξ : Fin N → F, ψ (Bd (AF F) a (rat ξ) y) * H (rat ξ + x) := by
      intro H
      simp only [th, rho, AddChar.map_add_eq_mul]
      rw [← tsum_mul_left]
      congr 1
      funext ξ
      ring
    have h := hth x y
    rw [e, e] at h
    exact mul_left_cancel₀ hne h
  rw [← integral_twisted_periodise hC G hG D hD h1 x]
  simp_rw [key]
  exact integral_twisted_periodise hC G' hG' D hD h1 x

end GlobalTheory.SWQ
