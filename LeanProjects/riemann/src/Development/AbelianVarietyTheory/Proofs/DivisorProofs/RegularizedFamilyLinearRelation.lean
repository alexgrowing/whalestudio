import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAut
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegFamOfContinuousAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyEqNhdsNEOfMeromorphicOfEqOnHalfPlane
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling GlobalTheory.ThK.DblKer

noncomputable section

namespace GlobalTheory.ThK.DblKer

theorem regFam_linRel : ∀ {Y : Type} (Ei : ℂ → Y → ℂ) (σ₀ : ℝ), (∀ s₁ : ℂ, ∃ (k : ℕ) (r : ℝ) (H : ℂ → Y → ℂ), 0 < r ∧
      (∀ s ∈ Metric.ball s₁ r, s ≠ s₁ → ∀ y, H s y = (s - s₁) ^ k * Ei s y) ∧
      ∀ y, DifferentiableOn ℂ (fun s => H s y) (Metric.ball s₁ r)) →
    ∀ (m : ℕ) (c : Fin m → ℂ) (T : Fin m → Y) (y₀ : Y), (∀ s : ℂ, σ₀ < s.re → Ei s y₀ = ∑ j, c j * Ei s (T j)) →
    ∀ s : ℂ, regFam Ei s y₀ = ∑ j, c j * regFam Ei s (T j) := by
  intro Y Ei σ₀ hloc m c T y₀ hrel s
  have hm : ∀ y x, MeromorphicAt (fun t => Ei t y) x := fun y x => by
    obtain ⟨k, r, H, hr, h, hH⟩ := hloc x
    exact GlobalTheory.meromorphicAt_of_pow_mul_eq hr (fun t ht hts => h t ht hts y) (hH y)
  set d : ℂ → ℂ := fun t => Ei t y₀ - ∑ j, c j * Ei t (T j) with hd
  have hdm : MeromorphicOn d Set.univ := fun x _ =>
    (hm y₀ x).sub (MeromorphicAt.fun_sum fun j _ => (MeromorphicAt.const (c j) x).fun_mul (hm (T j) x))
  have hev : ∀ᶠ t in 𝓝[≠] s, d t = 0 := by
    by_contra hne
    have h1 : meromorphicOrderAt d s ≠ ⊤ := by
      intro h
      rw [meromorphicOrderAt_eq_top_iff] at h
      exact hne h
    have h2 : meromorphicOrderAt d ((σ₀ + 1 : ℝ) : ℂ) ≠ ⊤ :=
      hdm.meromorphicOrderAt_ne_top_of_isPreconnected isPreconnected_univ (Set.mem_univ s)
        (Set.mem_univ _) h1
    apply h2
    rw [meromorphicOrderAt_eq_top_iff]
    have ho : IsOpen {z : ℂ | σ₀ < z.re} := isOpen_lt continuous_const Complex.continuous_re
    have hmem : {z : ℂ | σ₀ < z.re} ∈ 𝓝 ((σ₀ + 1 : ℝ) : ℂ) := ho.mem_nhds (by simp)
    filter_upwards [mem_nhdsWithin_of_mem_nhds hmem] with t ht
    exact sub_eq_zero.mpr (hrel t ht)
  by_cases hall : ∀ y, ∃ v, Tendsto (fun t => Ei t y) (𝓝[≠] s) (𝓝 v)
  · choose v hv using hall
    rw [regFam_eq_of_tendsto hv y₀]
    simp only [regFam_eq_of_tendsto hv]
    have hlim : Tendsto d (𝓝[≠] s) (𝓝 (v y₀ - ∑ j, c j * v (T j))) :=
      (hv y₀).sub (tendsto_finset_sum _ fun j _ => (hv (T j)).const_mul (c j))
    have h0 : Tendsto d (𝓝[≠] s) (𝓝 0) := tendsto_const_nhds.congr' (hev.mono fun t ht => ht.symm)
    exact sub_eq_zero.mp (tendsto_nhds_unique hlim h0)
  · simp [regFam_of_not hall]

example : regFam (fun (_ : ℂ) (y : ℕ) => (2 : ℂ) - y) 0 0 = ∑ j : Fin 1, (2 : ℂ) * regFam (fun _ (y : ℕ) => (2 : ℂ) - y) 0 ((fun _ => 1) j) := by
  refine regFam_linRel (fun _ (y : ℕ) => (2 : ℂ) - y) 0 (fun s₁ => ⟨0, 1, fun _ y => (2 : ℂ) - y, one_pos,
    fun s _ _ y => by simp, fun y => differentiableOn_const _⟩) 1 (fun _ => 2) (fun _ => 1) 0 (fun s _ => by norm_num) 0

end GlobalTheory.ThK.DblKer

end
