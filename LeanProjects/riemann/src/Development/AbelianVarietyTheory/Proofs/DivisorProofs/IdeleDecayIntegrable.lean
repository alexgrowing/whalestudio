import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DecayNonneg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsInfEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdeleDecayMeasurableStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdeleStabilizerIsOpenStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdeleStabilizerAbsFiniteEqOneStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdeleDecaySizeArchimedeanUnitInvariantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdeleCosetRepresentativesSummableStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdeleStabilizerDecayIntegralFiniteStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.IdeleTate

open GlobalTheory.IdeleDecay

attribute [local instance] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.modTop

local instance borelIdeleT (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] :
    BorelSpace (AE F E)ˣ := ⟨rfl⟩

theorem decay_le (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (N m : ℕ)
    (l : (AE F E)ˣ) : decay F E N m l ≤ ((1 + size F E l.1) ^ N)⁻¹ := by
  unfold decay
  split_ifs
  · exact le_rfl
  · exact inv_nonneg.mpr (pow_nonneg (add_nonneg zero_le_one (size_nonneg _)) _)

theorem integrable_decay_mul_absE : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (s m : ℕ), 2 ≤ s → 0 < m →
    ∃ N : ℕ, ∀ μ : Measure (AE F E)ˣ, μ.IsHaarMeasure →
      Integrable (fun l => GlobalTheory.IdeleDecay.decay F E N m l * (absE F E l : ℝ) ^ s) μ := by
  intro F E _ _ _ _ _ s m hs hm
  obtain ⟨N, hN⟩ := GlobalTheory.T.idele_stabilizer_decay_integral_finite F E s (by omega)
  obtain ⟨b, hb1, hb2, hb3⟩ := GlobalTheory.T.idele_coset_representatives_summable F E s m hs hm
  refine ⟨N, fun μ hμ => ?_⟩
  haveI : IsTopologicalRing (AE F E) := GlobalTheory.Doubling.isTopologicalRing_tens
  haveI : MeasurableMul (AE F E)ˣ := ContinuousMul.measurableMul
  set f : (AE F E)ˣ → ℝ := fun l => decay F E N m l * (absE F E l : ℝ) ^ s with hf
  have f_nn : ∀ l, 0 ≤ f l := fun l => mul_nonneg (decay_nonneg _ _ _) (pow_nonneg (NNReal.coe_nonneg _) _)
  have fmeas : Measurable f :=
    (GlobalTheory.T.idele_decay_measurable F E N m).mul ((GlobalTheory.Doubling.continuous_absE (F := F) (E := E)).measurable.coe_nnreal_real.pow_const s)
  set g : (AE F E)ˣ → ℝ := fun h => ((1 + size F E h.1) ^ N)⁻¹ * (absInf F E h : ℝ) ^ s with hg
  set c : ℕ → ℝ := fun j => (absFin F E (b j) : ℝ) ^ s with hc
  have c_nn : ∀ j, 0 ≤ c j := fun j => pow_nonneg (NNReal.coe_nonneg _) _
  set T : ℕ → Set (AE F E)ˣ := fun j => (fun l => (b j)⁻¹ * l) ⁻¹' (stab F E : Set (AE F E)ˣ) with hT
  have Tmeas : ∀ j, MeasurableSet (T j) := fun j =>
    ((GlobalTheory.T.idele_stabilizer_isOpen F E).preimage (continuous_const.mul continuous_id)).measurableSet

  have key : ∀ j, ∀ h ∈ stab F E, f (b j * h) ≤ c j * g h := by
    intro j h hh
    have e1 : absE F E (b j * h) = absFin F E (b j) * absInf F E h := by
      rw [map_mul, absE_eq, absE_eq, absInf_eq_one (hb1 j), GlobalTheory.T.idele_stabilizer_abs_finite_eq_one F E h hh]
      ring
    simp only [hf, hg, hc]
    rw [e1, NNReal.coe_mul, mul_pow]
    have := decay_le F E N m (b j * h)
    rw [GlobalTheory.T.idele_decay_size_archimedean_unit_invariant F E (b j) h (hb1 j)] at this
    calc decay F E N m (b j * h) * ((absFin F E (b j) : ℝ) ^ s * (absInf F E h : ℝ) ^ s)
        ≤ ((1 + size F E h.1) ^ N)⁻¹ * ((absFin F E (b j) : ℝ) ^ s * (absInf F E h : ℝ) ^ s) :=
          mul_le_mul_of_nonneg_right this (by positivity)
      _ = _ := by ring

  have cover : ∀ l, ENNReal.ofReal (f l) ≤ ∑' j, (T j).indicator (fun l => ENNReal.ofReal (f l)) l := by
    intro l
    by_cases hl : ∀ i v, evFin F v ((m : AF F) * coord F E l.1 i) ∈ v.adicCompletionIntegers F
    · obtain ⟨j, hj⟩ := hb2 l hl
      refine le_trans (le_of_eq ?_) (ENNReal.le_tsum j)
      rw [Set.indicator_of_mem (show l ∈ T j from hj)]
    · have : f l = 0 := by
        simp only [hf, decay, if_neg hl, zero_mul]
      rw [this, ENNReal.ofReal_zero]
      exact bot_le
  have term : ∀ j, ∫⁻ l, (T j).indicator (fun l => ENNReal.ofReal (f l)) l ∂μ ≤
      ENNReal.ofReal (c j) * ∫⁻ h in (stab F E : Set (AE F E)ˣ), ENNReal.ofReal (g h) ∂μ := by
    intro j
    rw [← lintegral_mul_left_eq_self _ (b j)]
    calc ∫⁻ h, (T j).indicator (fun l => ENNReal.ofReal (f l)) (b j * h) ∂μ
        ≤ ∫⁻ h, (stab F E : Set (AE F E)ˣ).indicator (fun h => ENNReal.ofReal (c j) * ENNReal.ofReal (g h)) h ∂μ := by
          refine lintegral_mono fun h => ?_
          by_cases hh : h ∈ stab F E
          · have hT' : b j * h ∈ T j := by simpa [hT] using hh
            rw [Set.indicator_of_mem hT', Set.indicator_of_mem (show h ∈ (stab F E : Set (AE F E)ˣ) from hh),
              ← ENNReal.ofReal_mul (c_nn j)]
            exact ENNReal.ofReal_le_ofReal (key j h hh)
          · have hT' : b j * h ∉ T j := by simpa [hT] using hh
            rw [Set.indicator_of_notMem hT']
            exact bot_le
      _ = ENNReal.ofReal (c j) * ∫⁻ h in (stab F E : Set (AE F E)ˣ), ENNReal.ofReal (g h) ∂μ := by
          rw [lintegral_indicator (GlobalTheory.T.idele_stabilizer_isOpen F E).measurableSet, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hfin : ∫⁻ l, ENNReal.ofReal (f l) ∂μ < ⊤ := by
    calc ∫⁻ l, ENNReal.ofReal (f l) ∂μ ≤ ∫⁻ l, ∑' j, (T j).indicator (fun l => ENNReal.ofReal (f l)) l ∂μ :=
          lintegral_mono cover
      _ = ∑' j, ∫⁻ l, (T j).indicator (fun l => ENNReal.ofReal (f l)) l ∂μ :=
          lintegral_tsum fun j => ((ENNReal.measurable_ofReal.comp fmeas).indicator (Tmeas j)).aemeasurable
      _ ≤ ∑' j, ENNReal.ofReal (c j) * ∫⁻ h in (stab F E : Set (AE F E)ˣ), ENNReal.ofReal (g h) ∂μ :=
          ENNReal.tsum_le_tsum term
      _ = (∑' j, ENNReal.ofReal (c j)) * ∫⁻ h in (stab F E : Set (AE F E)ˣ), ENNReal.ofReal (g h) ∂μ :=
          ENNReal.tsum_mul_right
      _ = ENNReal.ofReal (∑' j, c j) * ∫⁻ h in (stab F E : Set (AE F E)ˣ), ENNReal.ofReal (g h) ∂μ := by
          rw [ENNReal.ofReal_tsum_of_nonneg c_nn hb3]
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hN μ hμ)
  refine ⟨fmeas.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall f_nn)]
  exact hfin

end GlobalTheory.IdeleTate
