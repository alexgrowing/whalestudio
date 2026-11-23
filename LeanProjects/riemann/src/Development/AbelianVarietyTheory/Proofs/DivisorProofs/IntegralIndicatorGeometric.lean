import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValAtOfUnder
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasSumTupleProdOfSummableNormComplex

noncomputable section

open scoped TensorProduct NNReal nonZeroDivisors
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.UnrEuler
open GlobalTheory.Doubling (absE absEv unitFin ideleAt)

namespace GlobalTheory.UnrTate

theorem hasSum_prod_zpow_shells {ι : Type} [Fintype ι] (b : ι → ℂ) (hb0 : ∀ i, b i ≠ 0)
    (hb1 : ∀ i, ‖b i‖ < 1) (c : ι → ℤ) :
    HasSum (Set.indicator {k : ι → ℤ | ∀ i, c i ≤ k i} (fun k => ∏ i, b i ^ k i))
      (∏ i, b i ^ c i / (1 - b i)) := by
  classical
  let g : (ι → ℕ) → (ι → ℤ) := fun n i => c i + (n i : ℤ)
  have hinj : Function.Injective g := by
    intro n m h
    funext i
    have := congrFun h i
    simp only [g, add_right_inj, Nat.cast_inj] at this
    exact this
  rw [← hinj.hasSum_iff]
  · have hcomp : (Set.indicator {k : ι → ℤ | ∀ i, c i ≤ k i} (fun k => ∏ i, b i ^ k i)) ∘ g =
        fun n => ∏ i, (fun i (m : ℕ) => b i ^ c i * b i ^ m) i (n i) := by
      funext n
      simp only [Function.comp, Set.indicator_apply, Set.mem_setOf_eq]
      rw [if_pos (fun i => by simp [g])]
      refine Finset.prod_congr rfl (fun i _ => ?_)
      simp only [g]
      rw [zpow_add₀ (hb0 i)]
      simp
    rw [hcomp]
    have hsum : ∀ i, Summable (fun m : ℕ => ‖b i ^ c i * b i ^ m‖) := by
      intro i
      simp only [norm_mul, norm_pow]
      exact (summable_geometric_of_lt_one (norm_nonneg _) (hb1 i)).mul_left _
    have := GlobalTheory.hasSum_pi_prod_of_summable_norm ι (fun _ => ℕ)
      (fun i (m : ℕ) => b i ^ c i * b i ^ m) hsum
    convert this using 1
    refine Finset.prod_congr rfl (fun i _ => ?_)
    rw [tsum_mul_left, tsum_geometric_of_norm_lt_one (hb1 i), div_eq_mul_inv]
  · intro k hk
    rw [Set.indicator_apply_eq_zero]
    intro hmem
    exfalso
    apply hk
    refine ⟨fun i => (k i - c i).toNat, ?_⟩
    funext i
    have := hmem i
    simp only [g]
    omega

theorem integral_indicator_shells_eq_prod : ∀ {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul G] (μ : Measure G) [μ.IsMulLeftInvariant] {ι : Type} [Fintype ι] (o : G →* Multiplicative (ι → ℤ)), Function.Surjective o → MeasurableSet {g : G | o g = 1} → μ {g : G | o g = 1} = 1 → ∀ (a : ι → ℂ), (∀ i, a i ≠ 0) → (∀ i, ‖a i‖ < 1) → ∀ c : ι → ℤ, ∫ g, Set.indicator {g : G | ∀ i, c i ≤ Multiplicative.toAdd (o g) i} (fun g => ∏ i, a i ^ Multiplicative.toAdd (o g) i) g ∂μ = ∏ i, a i ^ c i / (1 - a i) := by
  intro G _ _ _ μ _ ι _ o ho hK hμ a ha0 ha1 c
  classical
  let φ : G → (ι → ℤ) := fun g => Multiplicative.toAdd (o g)
  have hfib : ∀ k, MeasurableSet (φ ⁻¹' {k}) ∧ μ (φ ⁻¹' {k}) = 1 := by
    intro k
    obtain ⟨b, hb⟩ := ho (Multiplicative.ofAdd k)
    have he : φ ⁻¹' {k} = (fun h => b⁻¹ * h) ⁻¹' {g : G | o g = 1} := by
      ext g
      simp only [φ, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq, map_mul, map_inv, hb]
      rw [inv_mul_eq_one, eq_comm]
      exact ⟨fun h => by rw [h]; rfl, fun h => by rw [← h]; rfl⟩
    rw [he]
    exact ⟨measurable_const_mul b⁻¹ hK, by rw [measure_preimage_mul]; exact hμ⟩
  have hφ : Measurable φ := measurable_to_countable' (fun k => (hfib k).1)
  have hmap : μ.map φ = Measure.count := by
    rw [Measure.ext_iff_singleton]
    intro k
    rw [Measure.map_apply hφ (measurableSet_singleton k), (hfib k).2, Measure.count_singleton]
  let F := Set.indicator {k : ι → ℤ | ∀ i, c i ≤ k i} (fun k => ∏ i, a i ^ k i)
  have hcomp : (fun g => Set.indicator {g : G | ∀ i, c i ≤ Multiplicative.toAdd (o g) i}
      (fun g => ∏ i, a i ^ Multiplicative.toAdd (o g) i) g) = fun g => F (φ g) := by
    funext g
    simp only [F, φ, Set.indicator_apply, Set.mem_setOf_eq]
  rw [hcomp, ← integral_map hφ.aemeasurable (measurable_of_countable F).aestronglyMeasurable, hmap]
  have hint : Integrable F Measure.count := by
    rw [integrable_count_iff]
    have h2 := (hasSum_prod_zpow_shells (fun i => ((‖a i‖ : ℝ) : ℂ)) (fun i => by simpa using ha0 i)
      (fun i => by simpa using ha1 i) c).summable
    rw [← Complex.summable_ofReal]
    convert h2 using 1
    funext k
    simp only [F, Set.indicator_apply, Set.mem_setOf_eq]
    split_ifs <;> simp [norm_prod, norm_zpow]
  rw [integral_countable hint]
  simp only [measureReal_def, Measure.count_singleton, ENNReal.toReal_one, one_smul]
  exact (hasSum_prod_zpow_shells a ha0 ha1 c).tsum_eq

end GlobalTheory.UnrTate
