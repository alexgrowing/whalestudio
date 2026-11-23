import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThPr
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PureAdelicFunctionFormula

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter GroundTheory.Global PositivityTheory.Rg.Base1 GlobalTheory.CompanionTheory.BasePsi
open scoped ENNReal NNReal Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.BasePsi

theorem exists_bound_inf {F : Type} [Field F] [NumberField F] (C : Set (Ainf F)) (hC : IsCompact C) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ y ∈ C, ∏ w : InfinitePlace F, ‖y w‖ ^ w.mult ≤ B := by
  have hc : Continuous fun y : Ainf F => ∏ w : InfinitePlace F, ‖y w‖ ^ w.mult :=
    continuous_finset_prod _ fun w _ => ((continuous_apply w).norm).pow _
  obtain ⟨B, hB⟩ := (hC.image hc).bddAbove
  exact ⟨max B 0, le_max_right _ _, fun y hy => (hB ⟨y, hy, rfl⟩).trans (le_max_left _ _)⟩

theorem exists_bound_fin {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (C : Set (Fv F v)) (hC : IsCompact C) : ∃ B : ℝ, 1 ≤ B ∧ ∀ y ∈ C, ‖y‖ ≤ B := by
  obtain ⟨B, hB⟩ := (hC.image continuous_norm).bddAbove
  exact ⟨max B 1, le_max_right _ _, fun y hy => (hB ⟨y, hy, rfl⟩).trans (le_max_left _ _)⟩

theorem md_le_of_bounds {F : Type} [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F)))
    (B : ℝ) (c : HeightOneSpectrum (𝓞 F) → ℝ) (hc : ∀ v ∈ S, 1 ≤ c v) (b : (AF F)ˣ)
    (hinf : ∏ w : InfinitePlace F, ‖(b : AF F).1 w‖ ^ w.mult ≤ B)
    (hS : ∀ v ∈ S, ‖(b : AF F).2 v‖ ≤ c v)
    (hout : ∀ v, v ∉ S → (b : AF F).2 v ∈ v.adicCompletionIntegers F) :
    md b ≤ B * ∏ v ∈ S, c v := by
  have hfin := IdeleGroup.finite_mulSupport_norm (K := F) b
  set T : Finset (HeightOneSpectrum (𝓞 F)) := hfin.toFinset ∪ S with hT
  have hsub : Function.mulSupport (fun v : HeightOneSpectrum (𝓞 F) => ‖(b : AF F).2 v‖) ⊆ (T : Set _) := by
    intro v hv
    simp only [hT, Finset.coe_union, Set.Finite.coe_toFinset]
    exact Or.inl hv
  have hfp : ∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖(b : AF F).2 v‖ ≤ ∏ v ∈ S, c v := by
    rw [finprod_eq_prod_of_mulSupport_subset _ hsub]
    calc ∏ v ∈ T, ‖(b : AF F).2 v‖ ≤ ∏ v ∈ T, (if v ∈ S then c v else 1) := by
          refine Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun v _ => ?_
          by_cases hv : v ∈ S
          · simpa [hv] using hS v hv
          · simpa [hv] using (Valued.toNormedField.norm_le_one_iff).2
              ((HeightOneSpectrum.mem_adicCompletionIntegers (R := 𝓞 F) F v).1 (hout v hv))
      _ = ∏ v ∈ S, (if v ∈ S then c v else 1) := by
          refine (Finset.prod_subset Finset.subset_union_right fun v _ hv => ?_).symm
          simp [hv]
      _ = ∏ v ∈ S, c v := Finset.prod_congr rfl fun v hv => by simp [hv]
  have hcS : 0 ≤ ∏ v ∈ S, c v := Finset.prod_nonneg fun v hv => zero_le_one.trans (hc v hv)
  have hB0 : 0 ≤ ∏ w : InfinitePlace F, ‖(b : AF F).1 w‖ ^ w.mult :=
    Finset.prod_nonneg fun w _ => pow_nonneg (norm_nonneg _) _
  have hfp0 : 0 ≤ ∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖(b : AF F).2 v‖ :=
    finprod_nonneg fun _ => norm_nonneg _
  rw [md, IdeleGroup.ideleModule_eq]
  exact mul_le_mul hinf hfp hfp0 (hB0.trans hinf)

theorem th_pure_vanish : ∀ (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))) (G : Ainf F → ℝ)
    (g : ∀ v : HeightOneSpectrum (𝓞 F), Fv F v → ℝ), HasCompactSupport G → (∀ v ∈ S, HasCompactSupport (g v)) →
    ∃ R : ℝ, ∀ a : (AF F)ˣ, R < md a → th (PositivityTheory.Rg.Base1.pure S G g fun v => rv v 0) a = 0 := by
  intro F _ _ S G g hG hg
  obtain ⟨B, -, hB⟩ := exists_bound_inf (F := F) (tsupport G) hG
  have hfin : ∀ v ∈ S, ∃ B : ℝ, 1 ≤ B ∧ ∀ y ∈ tsupport (g v), ‖y‖ ≤ B :=
    fun v hv => exists_bound_fin v _ (hg v hv)
  choose! c hc1 hc using hfin
  refine ⟨B * ∏ v ∈ S, c v, fun a ha => ?_⟩
  by_contra hne
  obtain ⟨t, ht⟩ : ∃ t : Fˣ, PositivityTheory.Rg.Base1.pure S G g (fun v => rv v 0) (pr t * a) ≠ 0 := by
    by_contra hall
    push_neg at hall
    exact hne (by simp [th, hall])
  rw [pure_rv_zero_apply] at ht
  split_ifs at ht with hint
  · have hprod : G ((pr t * a : (AF F)ˣ) : AF F).1 * ∏ v ∈ S, g v (((pr t * a : (AF F)ˣ) : AF F).2 v) ≠ 0 :=
      fun h => ht (by rw [h]; simp)
    have hGne := left_ne_zero_of_mul hprod
    have hgne := Finset.prod_ne_zero_iff.1 (right_ne_zero_of_mul hprod)
    have hle := md_le_of_bounds S B c hc1 (pr t * a)
      (hB _ (subset_tsupport _ (Function.mem_support.2 hGne)))
      (fun v hv => hc v hv _ (subset_tsupport _ (Function.mem_support.2 (hgne v hv)))) hint
    rw [md_mul, md_pr, one_mul] at hle
    exact absurd ha (not_lt.2 hle)
  · exact ht rfl

end GlobalTheory.CompanionTheory.BasePsi

end
