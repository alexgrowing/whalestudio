import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.SplitMulAlt

noncomputable section

open MeasureTheory Matrix Set Filter Topology
open scoped NNReal

namespace PositivityTheory.Rg.Sw.AbsSt.FarK

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt PositivityTheory.Rg.Sw.AbsSt.Far

variable {m n : ℕ} {ε : Fin m → Bool} {c t : ℝ} {p q : ℕ} {e : ℤ} {sL : PX m n →ₗ[ℂ] (GR n → ℂ)}
  {ρ : GR n → PX m n →ₗ[ℂ] PX m n}
  {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
  [SecondCountableTopology G] {Pp Γ : Subgroup G} {ι : GR n →* G} {s₀ : ℂ} {Ht : G → ℝ≥0}
  {sec I : PX m n →ₗ[ℂ] (G → ℂ)}

theorem farId [MeasurableSpace (KR n)] [BorelSpace (KR n)] (hD : CayleyBlocksInvertible) (hL : LocData ε c t p q e sL ρ)
    (hG : GlobCore ε c sL ρ G Pp Γ ι s₀ Ht sec I) {ν : Measure (KR n)} {κ : KR n → ℂ} {N : ℕ}
    {yy : Fin N → GR n} {QQ : Fin N → PX m n} {M : ℂ → Matrix (Fin N) (Fin N) ℂ}
    (hν : IsFiniteMeasure ν) (hκ : Continuous κ)
    (hMid : ∀ (w : ℂ) (i : Fin N) (y' : GR n), ∫ k, κ k * ((hLoc (y' * (k : GR n) * yy i) : ℂ) ^ w *
        F0 p q e (y' * (k : GR n) * yy i)) ∂ν = (hLoc y' : ℂ) ^ w * ∑ j, M w i j * sL (QQ j) y')
    {z : ℂ} (hmaj : ∀ C : Set G, IsCompact C → ∃ u : GlobalTheory.Eis.Cosets Pp Γ → ℝ, Summable u ∧
      ∀ g ∈ C, ∀ q', ‖GlobalTheory.Eis.term Pp Γ (hz Ht sec s₀ z 1) g q'‖ ≤ u q')
    (g : G) (hsum : ∀ j, Summable fun q' => GlobalTheory.Eis.term Pp Γ (hz Ht sec s₀ z (QQ j)) g q') (i : Fin N) :
    ∫ k, κ k * GlobalTheory.Eis.cosetSum Pp Γ (hz Ht sec s₀ z 1) (g * ι ((k : GR n) * yy i)) ∂ν =
      ∑ j, M (z - s₀) i j * GlobalTheory.Eis.cosetSum Pp Γ (hz Ht sec s₀ z (QQ j)) g := by
  classical
  have hCc : IsCompact (range fun k : KR n => g * ι ((k : GR n) * yy i)) :=
    isCompact_range (continuous_const.mul (hG.ιcont.comp (continuous_subtype_val.mul continuous_const)))
  obtain ⟨u, hu, hbu⟩ := hmaj _ hCc
  obtain ⟨B, hB⟩ := isCompact_univ.exists_bound_of_continuousOn hκ.continuousOn
  set B' := max B 0 with hB'
  set F : GlobalTheory.Eis.Cosets Pp Γ → KR n → ℂ :=
    fun q' k => κ k * hz Ht sec s₀ z 1 (((q'.out : Γ) : G) * (g * ι ((k : GR n) * yy i))) with hFdef
  have hFb : ∀ q' k, ‖F q' k‖ ≤ B' * u q' := by
    intro q' k
    simp only [hFdef, norm_mul]
    exact mul_le_mul ((hB k (mem_univ _)).trans (le_max_left _ _)) (hbu _ ⟨k, rfl⟩ q') (norm_nonneg _)
      (le_max_right _ _)
  have hFc : ∀ q', Continuous (F q') := by
    intro q'
    have := cont_hz hD hL hG z (yy i) (((q'.out : Γ) : G) * g)
    simp only [hFdef]
    refine hκ.mul ?_
    simpa only [mul_assoc] using this
  have hFi : ∀ q', Integrable (F q') ν := fun q' =>
    Integrable.mono' (integrable_const (B' * u q')) (hFc q').aestronglyMeasurable (ae_of_all _ (hFb q'))
  have hFn : ∀ q', ∫ k, ‖F q' k‖ ∂ν ≤ B' * u q' * ν.real univ := by
    intro q'
    calc ∫ k, ‖F q' k‖ ∂ν ≤ ∫ _k, B' * u q' ∂ν := integral_mono (hFi q').norm (integrable_const _) (hFb q')
      _ = B' * u q' * ν.real univ := by rw [integral_const, smul_eq_mul, mul_comm]
  have hF0 : ∀ q', q' ∉ Function.support u → ∀ k, F q' k = 0 := by
    intro q' hq k
    have h0 : u q' = 0 := Function.notMem_support.mp hq
    have := hFb q' k
    rw [h0, mul_zero] at this
    exact norm_le_zero_iff.mp this
  have : Countable (Function.support u) := hu.countable_support.to_subtype
  have hL1 : ∀ k, κ k * GlobalTheory.Eis.cosetSum Pp Γ (hz Ht sec s₀ z 1) (g * ι ((k : GR n) * yy i)) =
      ∑' s : Function.support u, F s k := by
    intro k
    rw [tsum_subtype_eq_of_support_subset (f := fun q' => F q' k) ?_]
    · simp only [hFdef, GlobalTheory.Eis.cosetSum, GlobalTheory.Eis.term]
      rw [tsum_mul_left]
    · intro q' hq
      by_contra h
      exact hq (hF0 q' h k)
  have hsumn : Summable fun s : Function.support u => ∫ k, ‖F s k‖ ∂ν :=
    Summable.of_nonneg_of_le (fun s => integral_nonneg fun _ => norm_nonneg _) (fun s => hFn s)
      (((hu.subtype _).mul_left B').mul_right (ν.real univ))
  have hint : ∫ k, κ k * GlobalTheory.Eis.cosetSum Pp Γ (hz Ht sec s₀ z 1) (g * ι ((k : GR n) * yy i)) ∂ν =
      ∑' s : Function.support u, ∫ k, F s k ∂ν := by
    simp_rw [hL1]
    exact (integral_tsum_of_summable_integral_norm (F := fun (s : Function.support u) k => F s k)
      (fun s => hFi s) hsumn).symm
  have hint2 : ∑' s : Function.support u, ∫ k, F s k ∂ν = ∑' q', ∫ k, F q' k ∂ν := by
    refine tsum_subtype_eq_of_support_subset (f := fun q' => ∫ k, F q' k ∂ν) ?_
    intro q' hq
    by_contra h
    exact hq (by simp only [hF0 q' h, integral_zero])
  have hpt : ∀ q', ∫ k, F q' k ∂ν = ∑ j, M (z - s₀) i j * hz Ht sec s₀ z (QQ j) (((q'.out : Γ) : G) * g) := by
    intro q'
    have := pointId hD hL hG hMid z i (((q'.out : Γ) : G) * g)
    simpa only [hFdef, mul_assoc] using this
  rw [hint, hint2, tsum_congr hpt]
  have hS : HasSum (fun b => ∑ j, M (z - s₀) i j * GlobalTheory.Eis.term Pp Γ (hz Ht sec s₀ z (QQ j)) g b)
      (∑ j, M (z - s₀) i j * GlobalTheory.Eis.cosetSum Pp Γ (hz Ht sec s₀ z (QQ j)) g) :=
    hasSum_sum fun j _ => ((hsum j).hasSum).mul_left (M (z - s₀) i j)
  exact hS.tsum_eq

end PositivityTheory.Rg.Sw.AbsSt.FarK

namespace PositivityTheory.Rg.Sw.AbsSt

open PositivityTheory.Rg.Sw

theorem farRightC : Iwa → CayleyBlocksInvertible → Mult → HolParam → FarRightC := by
  intro hI hD hM _hH m n ε c t p q e sL ρ hL G _ _ _ _ _ _ Pp Γ ι s₀ Ht sec I hG
  obtain ⟨σ, h1, h2, hmaj⟩ := FarK.farHol hI hM hD hL hG
  refine ⟨σ, h1, h2, ?_⟩
  intro _ _ ν κ N yy QQ M hν hκ hMid z hzr g i
  exact FarK.farId hD hL hG hν hκ hMid (hmaj z hzr) g (fun j => h2 (QQ j) g z hzr) i

end PositivityTheory.Rg.Sw.AbsSt
