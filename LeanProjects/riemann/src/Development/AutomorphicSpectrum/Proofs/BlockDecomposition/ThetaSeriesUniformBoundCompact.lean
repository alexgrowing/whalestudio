import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThPr
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PureAdelicFunctionFormulaStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BoundedDenominatorsCompactIdeleSetStatement

noncomputable section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter GroundTheory.Global PositivityTheory.Rg.Base1 GlobalTheory.CompanionTheory.BasePsi
open scoped ENNReal NNReal Classical

namespace GlobalTheory.CompanionTheory.BasePsi

theorem pure_rv_zero_le {F : Type} [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F)))
    (G : Ainf F → ℝ) (g : ∀ v : HeightOneSpectrum (𝓞 F), Fv F v → ℝ)
    (hGc : Continuous G) (hGs : HasCompactSupport G)
    (hg : ∀ v ∈ S, Continuous (g v) ∧ HasCompactSupport (g v)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ a : (AF F)ˣ, PositivityTheory.Rg.Base1.pure S G g (fun v => rv v 0) a ≤ ENNReal.ofReal M := by
  obtain ⟨MG, hMG⟩ := hGc.bounded_above_of_compact_support hGs
  have hB : ∀ v : HeightOneSpectrum (𝓞 F), ∃ B : ℝ, 0 ≤ B ∧ (v ∈ S → ∀ x, |g v x| ≤ B) := by
    intro v
    by_cases hv : v ∈ S
    · obtain ⟨B, hB⟩ := (hg v hv).1.bounded_above_of_compact_support (hg v hv).2
      exact ⟨|B|, abs_nonneg _, fun _ x => (hB x).trans (le_abs_self B)⟩
    · exact ⟨0, le_rfl, fun h => absurd h hv⟩
  choose B hB0 hB using hB
  refine ⟨|MG| * ∏ v ∈ S, B v, mul_nonneg (abs_nonneg _) (Finset.prod_nonneg fun v _ => hB0 v), fun a => ?_⟩
  rw [GlobalTheory.T.pure_adelic_function_formula]
  split_ifs with h
  · refine ENNReal.ofReal_le_ofReal ?_
    refine (le_abs_self _).trans ?_
    rw [abs_mul, Finset.abs_prod]
    refine mul_le_mul ((hMG _).trans (le_abs_self MG)) ?_
      (Finset.prod_nonneg fun v _ => abs_nonneg _) (abs_nonneg _)
    exact Finset.prod_le_prod (fun v _ => abs_nonneg _) fun v hv => hB v hv _
  · simp

theorem th_pure_rv_zero_bound : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ θ : ℝ →+* Ainf F, Continuous θ → ∀ r : ℝ → (AF F)ˣ, IsRay θ r →
    ∀ (S : Finset (HeightOneSpectrum (𝓞 F))) (G : Ainf F → ℝ) (g : ∀ v : HeightOneSpectrum (𝓞 F), Fv F v → ℝ),
    Continuous G → HasCompactSupport G → (∀ v ∈ S, Continuous (g v) ∧ HasCompactSupport (g v)) →
    ∀ D : Set (AF F)ˣ, IsCompact D → ∃ C : ℝ≥0, ∀ u ∈ D, ∀ δ : ℝ, 0 < δ →
      ENNReal.ofReal (δ ^ Module.finrank ℚ F) * th (PositivityTheory.Rg.Base1.pure S G g fun v => rv v 0) (u * r δ) ≤ C := by
  intro F _ _ hF θ hθ r hr S G g hGc hGs hg D hD
  obtain ⟨M, hM0, hM⟩ := pure_rv_zero_le S G g hGc hGs hg
  obtain ⟨N, hN, hden⟩ := GlobalTheory.T.bounded_denominators_compact_idele_set F D hD S (fun v => tsupport (g v)) (fun v hv => (hg v hv).2)
  let K : Set (Ainf F) :=
    (fun p : (AF F)ˣ × Ainf F => (((p.1⁻¹ : (AF F)ˣ) : AF F).1) * p.2) '' (D ×ˢ tsupport G)
  have hK : IsCompact K := by
    refine (hD.prod hGs).image ?_
    have c1 : Continuous fun a : AF F => a.1 := continuous_fst
    have c2 : Continuous fun p : (AF F)ˣ × Ainf F => ((p.1⁻¹ : (AF F)ˣ) : AF F) :=
      Units.continuous_val.comp (continuous_inv.comp continuous_fst)
    exact (c1.comp c2).mul continuous_snd
  obtain ⟨C₀, hC₀⟩ := GlobalTheory.CompanionTheory.MassCount.countBd F hF θ hθ K hK N hN
  refine ⟨(max C₀ 0 * M).toNNReal, fun u hu δ hδ => ?_⟩
  obtain ⟨hfin, hle⟩ := hC₀ δ hδ ⊤ top_ne_bot
  set T : Set F := {x : F | x ≠ 0 ∧ (∃ y ∈ (⊤ : Ideal (𝓞 F)), (y : F) = N * x) ∧ θ δ * algebraMap F (Ainf F) x ∈ K} with hT
  have hsupp : ∀ t : Fˣ, PositivityTheory.Rg.Base1.pure S G g (fun v => rv v 0) (pr t * (u * r δ)) ≠ 0 → (t : F) ∈ T := by
    intro t ht
    obtain ⟨hr1, hr2⟩ := hr δ hδ
    rw [GlobalTheory.T.pure_adelic_function_formula] at ht
    have h1 : ∀ v, ((pr t * (u * r δ) : (AF F)ˣ) : AF F).2 v = algebraMap F (Fv F v) (t : F) * (u : AF F).2 v := by
      intro v
      have : ((pr t * (u * r δ) : (AF F)ˣ) : AF F).2 v
          = algebraMap F (Fv F v) (t : F) * ((u : AF F).2 v * (r δ : AF F).2 v) := rfl
      rw [this, hr2]
      simp
    have h0 : ((pr t * (u * r δ) : (AF F)ˣ) : AF F).1 = algebraMap F (Ainf F) (t : F) * ((u : AF F).1 * θ δ) := by
      have : ((pr t * (u * r δ) : (AF F)ˣ) : AF F).1
          = algebraMap F (Ainf F) (t : F) * ((u : AF F).1 * (r δ : AF F).1) := rfl
      rw [this, hr1]
    by_cases hint : ∀ v, v ∉ S → ((pr t * (u * r δ) : (AF F)ˣ) : AF F).2 v ∈ v.adicCompletionIntegers F
    swap
    · exact absurd (if_neg hint) ht
    rw [if_pos hint] at ht
    have hne : G ((pr t * (u * r δ) : (AF F)ˣ) : AF F).1 * ∏ v ∈ S, g v (((pr t * (u * r δ) : (AF F)ˣ) : AF F).2 v) ≠ 0 := by
      intro h
      exact ht (by rw [h]; simp)
    have hG0 := left_ne_zero_of_mul hne
    have hp0 := right_ne_zero_of_mul hne
    have hgS : ∀ v ∈ S, algebraMap F (Fv F v) (t : F) * (u : AF F).2 v ∈ tsupport (g v) := by
      intro v hv
      rw [← h1 v]
      exact subset_tsupport _ (Finset.prod_ne_zero_iff.1 hp0 v hv)
    obtain ⟨y, hy⟩ := hden u hu (t : F) hgS (fun v hv => by rw [← h1 v]; exact hint v hv)
    refine ⟨t.ne_zero, ⟨y, Submodule.mem_top, hy⟩, ?_⟩
    refine ⟨(u, ((pr t * (u * r δ) : (AF F)ˣ) : AF F).1), ⟨hu, subset_tsupport _ hG0⟩, ?_⟩
    have hinv : (((u⁻¹ : (AF F)ˣ) : AF F).1) * (u : AF F).1 = 1 := by
      exact congrArg (fun w : (AF F)ˣ => (w : AF F).1) (inv_mul_cancel u)
    show (((u⁻¹ : (AF F)ˣ) : AF F).1) * ((pr t * (u * r δ) : (AF F)ˣ) : AF F).1 = _
    rw [h0]
    calc _ = ((((u⁻¹ : (AF F)ˣ) : AF F).1) * (u : AF F).1) * (θ δ * algebraMap F (Ainf F) (t : F)) := by ring
      _ = _ := by rw [hinv, one_mul]
  have hfin' : {t : Fˣ | (t : F) ∈ T}.Finite :=
    hfin.preimage (Units.val_injective.injOn)
  have hth : th (PositivityTheory.Rg.Base1.pure S G g fun v => rv v 0) (u * r δ) ≤ (hfin'.toFinset.card : ℝ≥0∞) * ENNReal.ofReal M := by
    unfold th
    rw [tsum_eq_sum (s := hfin'.toFinset) (fun t ht => by
      by_contra h
      exact ht (hfin'.mem_toFinset.2 (hsupp t h)))]
    calc _ ≤ ∑ t ∈ hfin'.toFinset, ENNReal.ofReal M := Finset.sum_le_sum fun t _ => hM _
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
  have hcard : (hfin'.toFinset.card : ℝ) ≤ (T.ncard : ℝ) := by
    have h1 : hfin'.toFinset.card = {t : Fˣ | (t : F) ∈ T}.ncard := (Set.ncard_eq_toFinset_card _ hfin').symm
    rw [h1]
    exact_mod_cast Set.ncard_le_ncard_of_injOn (fun t : Fˣ => (t : F)) (fun t ht => ht) Units.val_injective.injOn hfin
  have hle' : δ ^ Module.finrank ℚ F * (T.ncard : ℝ) ≤ max C₀ 0 := by
    refine hle.trans ?_
    simp
  have hd0 : (0 : ℝ) ≤ δ ^ Module.finrank ℚ F := by positivity
  calc ENNReal.ofReal (δ ^ Module.finrank ℚ F) * th (PositivityTheory.Rg.Base1.pure S G g fun v => rv v 0) (u * r δ)
      ≤ ENNReal.ofReal (δ ^ Module.finrank ℚ F) * ((hfin'.toFinset.card : ℝ≥0∞) * ENNReal.ofReal M) := by gcongr
    _ = ENNReal.ofReal (δ ^ Module.finrank ℚ F * (hfin'.toFinset.card : ℝ) * M) := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul hd0, ENNReal.ofReal_natCast, mul_assoc]
    _ ≤ ENNReal.ofReal (max C₀ 0 * M) := by
        refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right ?_ hM0)
        exact (mul_le_mul_of_nonneg_left hcard hd0).trans hle'
    _ = _ := by rw [ENNReal.ofReal]

end GlobalTheory.CompanionTheory.BasePsi

end
