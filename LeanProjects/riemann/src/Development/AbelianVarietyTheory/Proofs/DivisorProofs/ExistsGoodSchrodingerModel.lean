import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalDarbouxCoordinatesTensorHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinitePlaceVacuumAnyDarbouxCoordinatesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallySelfDualLatticeIndicatorIsVacuum
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicGroupTopologyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiscreteTopologyRationalUnitaryStatement
open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.ModelEx

theorem exists_haar_fundDom : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (J : Matrix (Fin n) (Fin n) E), ∃ (μ : MeasureTheory.Measure (UA σ J)) (𝓕 : Set (UA σ J)),
      μ.IsHaarMeasure ∧ MeasureTheory.IsFundamentalDomain (ratU σ J) 𝓕 μ := by
  intro F E _ _ _ _ _ σ n J
  obtain ⟨h1, h2, h3, h4⟩ := GlobalTheory.T.unitary_adelic_group_topology F E σ n J
  haveI := h1; haveI := h2; haveI := h3; haveI := h4
  haveI := GlobalTheory.T.discreteTopology_rational_unitary F E σ n J
  haveI : BorelSpace (UA σ J) := ⟨rfl⟩
  obtain ⟨𝓕, h𝓕⟩ := GlobalTheory.FundDomDiscrete.exists_isFundamentalDomain (ratU σ J) (MeasureTheory.Measure.haar)
  exact ⟨MeasureTheory.Measure.haar, 𝓕, inferInstance, h𝓕⟩

theorem model_exists : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E), B.IsGood σ → ∀ (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (r s r' s' : ℕ),
    X.IsHerm σ B r s → W.IsSkew σ B r' s' → ∃ M : Model σ X W, M.IsGood B.ψ := by
  intro F E _ _ _ _ _ σ B hB n d X W r s r' s' hX hW
  classical
  obtain ⟨co, hco⟩ := GlobalTheory.RatDarboux.exists_rational_darboux_of_isGood B hB X W r s r' s' hX hW
  obtain ⟨μ, 𝓕, hμ, h𝓕⟩ := exists_haar_fundDom F E σ n X.J
  have hS := GlobalTheory.VacIndic.eventually_isVac_indicator B hB X W r s r' s' hX hW co hco
  let M₀ : Model σ X W := ⟨co, fun _ => 0, 0, ∅⟩
  let ind : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ := fun v =>
    Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1
  let vac : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ := fun v =>
    if M₀.IsVac B.ψ v (ind v) then ind v else (GlobalTheory.T.exists_finitePlace_vacuum_any_darboux_coordinates B hB X W r s r' s' hX hW co v).choose
  refine ⟨⟨co, vac, μ, 𝓕⟩, ⟨hco, fun v => ?_, ?_, hμ, h𝓕⟩⟩
  · show M₀.IsVac B.ψ v (vac v)
    by_cases h : M₀.IsVac B.ψ v (ind v)
    · simp only [vac, if_pos h]; exact h
    · simp only [vac, if_neg h]; exact (GlobalTheory.T.exists_finitePlace_vacuum_any_darboux_coordinates B hB X W r s r' s' hX hW co v).choose_spec
  · filter_upwards [hS] with v hv
    show vac v = ind v
    exact if_pos hv

end GlobalTheory.ModelEx

end
