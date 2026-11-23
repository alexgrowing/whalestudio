import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoublingConfigurationLeviIntegralImports
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralBoundLtTop

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

theorem GlobalTheory.TateConv.majorant_inv_lintegral_lt_top : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (μ : Measure (AE F E)ˣ), μ.IsHaarMeasure →
    ∀ s : ℝ, 1 < s → ∀ U : Set (Fin (Module.finrank F E) → Af F), IsCompact U → ∃ N : ℕ,
      ∫⁻ l, GlobalTheory.XTermMaj.maj F E N U ((l⁻¹ : (AE F E)ˣ) : AE F E) * ENNReal.ofReal ((absE F E l : ℝ) ^ (-s)) ∂μ < ⊤ := by
  intro F E _ _ _ _ _ μ hμ s hs U hU
  obtain ⟨N, k, L, C, hk, hb⟩ := GlobalTheory.TateConv.bound F E hs hU
  refine ⟨N, ?_⟩
  haveI := hμ
  haveI : BorelSpace (AE F E)ˣ := ⟨rfl⟩
  haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  set g : (AE F E)ˣ → ENNReal := fun m =>
    GlobalTheory.XTermMaj.maj F E N U (m : AE F E) * ENNReal.ofReal ((absE F E m : ℝ) ^ s) with hg
  have hinv : ∀ l : (AE F E)ˣ, GlobalTheory.XTermMaj.maj F E N U ((l⁻¹ : (AE F E)ˣ) : AE F E) *
      ENNReal.ofReal ((absE F E l : ℝ) ^ (-s)) = g l⁻¹ := fun l => by
    simp only [hg, map_inv, NNReal.coe_inv]
    rw [Real.inv_rpow (NNReal.coe_nonneg _), Real.rpow_neg (NNReal.coe_nonneg _)]
  simp_rw [hinv]
  have hm : ∫⁻ l, g l⁻¹ ∂μ = ∫⁻ l, g l ∂μ.inv :=
    (lintegral_map_equiv g (MeasurableEquiv.inv (AE F E)ˣ) (μ := μ)).symm
  rw [hm]
  haveI : μ.inv.IsHaarMeasure := {}
  exact lt_of_le_of_lt (lintegral_mono hb) (GlobalTheory.TateConv.lintegral_bound_lt_top F E μ.inv hs hk L C)
