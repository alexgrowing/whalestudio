import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicGroupTopology
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFundamentalDomainClosure

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.CoordPowScale

theorem sigmaFinite_smul_of_ne_top {α : Type} [MeasurableSpace α] (μ : Measure α) [SigmaFinite μ]
    {c : ENNReal} (hc : c ≠ ⊤) : SigmaFinite (c • μ) := by
  refine ⟨⟨⟨fun n => spanningSets μ n, fun _ => trivial, fun n => ?_, iUnion_spanningSets _⟩⟩⟩
  rw [Measure.smul_apply, smul_eq_mul]
  exact ENNReal.mul_lt_top hc.lt_top (measure_spanningSets_lt_top _ n)

theorem map_pi_coord_eq_pow_smul :
    ∀ {α : Type} [MeasurableSpace α] (ν : Measure α) [SigmaFinite ν] (f : α → α), Measurable f →
      ∀ c : ENNReal, c ≠ ⊤ →
  ν.map f = c • ν → ∀ k : ℕ, (Measure.pi fun _ : Fin k => ν).map (fun v i => f (v i)) =
    c ^ k • Measure.pi fun _ : Fin k => ν := by
  intro α _ ν _ f hf c hc hmap k
  haveI : SigmaFinite (ν.map f) := by rw [hmap]; exact sigmaFinite_smul_of_ne_top ν hc
  haveI : SigmaFinite (c • ν) := sigmaFinite_smul_of_ne_top ν hc
  have h1 : (Measure.pi fun _ : Fin k => ν).map (fun v i => f (v i)) =
      Measure.pi fun _ : Fin k => ν.map f :=
    Measure.pi_map_pi (fun _ => hf.aemeasurable)
  rw [h1]
  simp only [hmap]
  refine Measure.pi_eq fun s _ => ?_
  rw [Measure.smul_apply, Measure.pi_pi, smul_eq_mul]
  simp only [Measure.smul_apply, smul_eq_mul, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]

end GlobalTheory.CoordPowScale
