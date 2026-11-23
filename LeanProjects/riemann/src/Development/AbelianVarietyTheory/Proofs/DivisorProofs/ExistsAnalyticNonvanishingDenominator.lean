import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaOn
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.CountableIdealSummableAbsNormRpow

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling GlobalTheory.ThK.Bot
open Formalism.L2.Host (aboveF)

namespace GlobalTheory.ThK.Bot.DenProd

theorem exists_hasProd_factor {ι : Type} (N : ι → ℕ) (hN : ∀ v, 1 < N v)
    (hsum : ∀ σ : ℝ, 1 < σ → Summable fun v => (N v : ℝ) ^ (-σ)) (e : ι → ℂ) (he : ∀ v, ‖e v‖ ≤ 1)
    (j : ℕ) (hj : 1 ≤ j) :
    ∃ D : ℂ → ℂ, AnalyticOnNhd ℂ D {s | 0 < s.re} ∧ ∀ s : ℂ, 0 < s.re → D s ≠ 0 ∧
      HasProd (fun v => 1 - e v * (N v : ℂ) ^ (-(2 * s + (j : ℂ)))) (D s) := by
  have hN1 : ∀ v, (1 : ℝ) < N v := fun v => by exact_mod_cast hN v
  have hj' : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hb : ∀ (a : ℝ) (s : ℂ), a ≤ s.re → ∀ v,
      ‖-(e v * (N v : ℂ) ^ (-(2 * s + (j : ℂ))))‖ ≤ (N v : ℝ) ^ (-(2 * a + 1)) := by
    intro a s hs v
    rw [norm_neg, norm_mul, Complex.norm_natCast_cpow_of_pos (by linarith [hN v])]
    refine (mul_le_of_le_one_left (by positivity) (he v)).trans ?_
    refine Real.rpow_le_rpow_of_exponent_le (hN1 v).le ?_
    simp
    linarith
  have hd : ∀ v, Differentiable ℂ fun s : ℂ => -(e v * (N v : ℂ) ^ (-(2 * s + (j : ℂ)))) := by
    intro v
    refine ((differentiable_const _).mul ?_).neg
    refine Differentiable.const_cpow (by fun_prop) (Or.inl ?_)
    exact_mod_cast (by linarith [hN v] : 0 < N v).ne'
  have ho : ∀ a : ℝ, IsOpen {z : ℂ | a < z.re} := fun a => isOpen_lt continuous_const Complex.continuous_re
  refine ⟨fun s => ∏' v, (1 + -(e v * (N v : ℂ) ^ (-(2 * s + (j : ℂ))))), ?_, fun s hs => ?_⟩
  · refine DifferentiableOn.analyticOnNhd (fun s hs => ?_) (ho 0)
    obtain ⟨a, h1, h2⟩ := exists_between (show 0 < s.re from hs)
    have h3 := (hsum (2 * a + 1) (by linarith)).hasProdLocallyUniformlyOn_one_add
      (f := fun v z => -(e v * (N v : ℂ) ^ (-(2 * z + (j : ℂ))))) (ho a)
      (Filter.Eventually.of_forall fun v z hz => hb a z (le_of_lt hz) v)
      fun v => (hd v).continuous.continuousOn
    have h4 := (hasProdLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn.1 h3).differentiableOn
      (Filter.Eventually.of_forall fun t =>
        (Differentiable.fun_finsetProd fun v _ => (hd v).const_add 1).differentiableOn) (ho a)
    exact (h4.differentiableAt ((ho a).mem_nhds h2)).differentiableWithinAt
  · have hS : Summable fun v => ‖-(e v * (N v : ℂ) ^ (-(2 * s + (j : ℂ))))‖ :=
      Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (hb s.re s le_rfl) (hsum _ (by linarith))
    refine ⟨tprod_one_add_ne_zero_of_summable (fun v h0 => ?_) hS, ?_⟩
    · have h1 := (hb s.re s le_rfl v).trans_lt
        (Real.rpow_lt_one_of_one_lt_of_neg (hN1 v) (by linarith))
      rw [eq_neg_of_add_eq_zero_right h0] at h1
      simp at h1
    · simpa only [sub_eq_add_neg] using (multipliable_one_add_of_summable hS).hasProd

theorem exists_hasProd_denInv :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (T : Finset (Pl F)),
    ∃ D : ℂ → ℂ, AnalyticOnNhd ℂ D {s | 0 < s.re} ∧ ∀ s : ℂ, 0 < s.re → D s ≠ 0 ∧ HasProd (fun v : {v : Pl F // v ∉ T} => denInv E n v.1 s) (D s) := by
  intro F E _ _ _ _ _ n T
  have key : ∀ j : ℕ, ∃ D : ℂ → ℂ, 1 ≤ j → (AnalyticOnNhd ℂ D {s | 0 < s.re} ∧ ∀ s : ℂ, 0 < s.re → D s ≠ 0 ∧
      HasProd (fun v : {v : Pl F // v ∉ T} => 1 - etaAt E v.1 ^ (n - j) *
        ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(2 * s + (j : ℂ)))) (D s)) := by
    intro j
    by_cases hj : 1 ≤ j
    · obtain ⟨D, hD⟩ := exists_hasProd_factor (ι := {v : Pl F // v ∉ T}) (fun v => Ideal.absNorm v.1.asIdeal)
        (fun v => NumberField.HeightOneSpectrum.one_lt_absNorm v.1)
        (fun σ hσ => ((GlobalTheory.countable_ideal_and_summable_absNorm_rpow F).2 σ hσ).2.subtype {v | v ∉ T})
        (fun v => etaAt E v.1 ^ (n - j))
        (fun v => by
          rw [norm_pow]
          refine pow_le_one₀ (norm_nonneg _) ?_
          unfold etaAt
          split_ifs <;> simp) j hj
      exact ⟨D, fun _ => hD⟩
    · exact ⟨0, fun h => absurd h hj⟩
  choose D hD using key
  refine ⟨fun s => ∏ j ∈ Finset.Icc 1 n, D j s, ?_, fun s hs => ⟨?_, ?_⟩⟩
  · exact Finset.analyticOnNhd_fun_prod _ fun j hj => (hD j (Finset.mem_Icc.1 hj).1).1
  · exact Finset.prod_ne_zero_iff.2 fun j hj => ((hD j (Finset.mem_Icc.1 hj).1).2 s hs).1
  · exact hasProd_prod fun j hj => ((hD j (Finset.mem_Icc.1 hj).1).2 s hs).2

end GlobalTheory.ThK.Bot.DenProd
