import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRk
open scoped Matrix
open GlobalTheory.WeilM GlobalTheory.FullRankCoinv MeasureTheory

namespace GlobalTheory.HaarScaleMatrix

open scoped Matrix in
open MeasureTheory in

theorem _root_.GlobalTheory.HaarScaleMatrix.secondCountable_of_localField (k : Type) [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k] : SecondCountableTopology k :=
  _root_.GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field.1

theorem integral_comp_addEquiv {G : Type} [AddCommGroup G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsAddHaarMeasure]
    (L : G ≃+ G) (hL : Continuous L) (hL' : Continuous L.symm) :
    ∃ c : ℝ, 0 < c ∧ ∀ f : G → ℂ, ∫ x, f (L x) ∂μ = (c : ℂ) * ∫ x, f x ∂μ := by
  haveI : (μ.map L).IsAddHaarMeasure := AddEquiv.isAddHaarMeasure_map μ L hL hL'
  let H : G ≃ₜ G := { toEquiv := L.toEquiv, continuous_toFun := hL, continuous_invFun := hL' }
  have hs := Measure.isAddLeftInvariant_eq_smul (μ.map L) μ
  refine ⟨(Measure.addHaarScalarFactor (μ.map L) μ : ℝ), ?_, fun f => ?_⟩
  · exact_mod_cast Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure (μ.map L) μ
  · have h1 : ∫ x, f x ∂(μ.map L) = ∫ x, f (L x) ∂μ :=
      integral_map_equiv H.toMeasurableEquiv f
    rw [← h1]
    conv_lhs => rw [hs]
    rw [integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]

theorem integral_comp_addEquiv_matrix :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (e d : ℕ)
    [MeasurableSpace (Matrix (Fin e) (Fin d) k)] [BorelSpace (Matrix (Fin e) (Fin d) k)]
    (μ : Measure (Matrix (Fin e) (Fin d) k)) [μ.IsAddHaarMeasure]
    (L : Matrix (Fin e) (Fin d) k ≃+ Matrix (Fin e) (Fin d) k), Continuous L → Continuous L.symm →
    ∃ c : ℝ, 0 < c ∧ ∀ f : Matrix (Fin e) (Fin d) k → ℂ, ∫ x, f (L x) ∂μ = (c : ℂ) * ∫ x, f x ∂μ := by
  intro k _ _ _ _ e d _ _ μ _ L hL hL'
  haveI := secondCountable_of_localField k
  haveI : LocallyCompactSpace (Matrix (Fin e) (Fin d) k) :=
    inferInstanceAs (LocallyCompactSpace (Fin e → Fin d → k))
  haveI : SecondCountableTopology (Matrix (Fin e) (Fin d) k) :=
    inferInstanceAs (SecondCountableTopology (Fin e → Fin d → k))
  exact integral_comp_addEquiv μ L hL hL'

end GlobalTheory.HaarScaleMatrix
