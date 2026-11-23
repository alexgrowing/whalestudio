import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareIntegrabilityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureFundDomLtTop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableOnSqFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousLeftInvariantThetaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousLeftInvariantDualStatement

noncomputable section

namespace GlobalTheory.ThKSelfOrth

open MeasureTheory Pointwise

end GlobalTheory.ThKSelfOrth

noncomputable section
namespace GlobalTheory.ThKSelfOrth
open scoped TensorProduct
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU Topology

theorem exists_haar_fundDom : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    (∀ x, σ (σ x) = x) → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E),
      ∃ (μ : Measure (UA σ J)) (𝓕 : Set (UA σ J)), μ.IsHaarMeasure ∧ IsFundamentalDomain (ratU σ J) 𝓕 μ := by
  intro F E _ _ _ _ _ σ hσ n J
  let e := GlobalTheory.ThK.SquareIntegrability.toGAd hσ J (one_ne_zero : (1 : E) ≠ 0)
  have he : Continuous e := continuous_subtype_val.subtype_mk _
  have hes : Continuous e.symm := continuous_subtype_val.subtype_mk _
  let t : UA σ J ≃ₜ GAd σ ((1 : E) • J.map σ) := ⟨e.toEquiv, he, hes⟩
  haveI : BorelSpace (UA σ J) := ⟨rfl⟩
  haveI : IsTopologicalGroup (UA σ J) := t.isInducing.topologicalGroup e
  haveI : SecondCountableTopology (UA σ J) := t.isInducing.secondCountableTopology
  haveI : LocallyCompactSpace (UA σ J) := t.isClosedEmbedding.locallyCompactSpace
  haveI : T2Space (UA σ J) := t.isEmbedding.t2Space
  have hmemP : ∀ δ : ratU σ J, e δ.1 ∈ ratPts σ ((1 : E) • J.map σ) := fun δ => by
    obtain ⟨m, hm⟩ := Subgroup.mem_subgroupOf.1 δ.2
    have h2 := (e δ.1).2
    refine Subgroup.mem_subgroupOf.2 (Subgroup.mem_map.2 ⟨m, ?_, hm⟩)
    exact GlobalTheory.ThK.SquareIntegrability.unitary_of_map_inclR σ n _ m _ (by rw [hm]; rfl) h2
  let f : ratU σ J → ratPts σ ((1 : E) • J.map σ) := fun δ => ⟨e δ.1, hmemP δ⟩
  have hfe : IsEmbedding f := by
    refine (IsEmbedding.subtypeVal.of_comp_iff).1 ?_
    exact t.isEmbedding.comp IsEmbedding.subtypeVal
  haveI : DiscreteTopology (ratU σ J) := hfe.discreteTopology
  obtain ⟨𝓕, h𝓕⟩ := GlobalTheory.FundDomDiscrete.exists_isFundamentalDomain (ratU σ J) (Measure.haar : Measure (UA σ J))
  exact ⟨Measure.haar, 𝓕, inferInstance, h𝓕⟩

end GlobalTheory.ThKSelfOrth

noncomputable section

namespace GlobalTheory.ThKSelfOrth

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem polData_of_polMatch {a a' : ℕ} {B : Base F E} {G : Geo σ a a'} {X : Chars F E} {R : RealMaps F a a'}
    {Rf : FinMaps F a a'} {Φ Φ'} (h : PolMatch B G X R Rf Φ Φ') : Φ ∈ PolData B G.M ∧ Φ' ∈ PolData B G.M' := by
  obtain ⟨T, -, m, m', f, φ, f', φ', hi, hj, rfl, rfl, -⟩ := h
  refine ⟨Submodule.sum_mem _ fun i _ => Submodule.subset_span ⟨f i, (hi i).1, φ i, (hi i).2.1, ?_, rfl⟩,
    Submodule.sum_mem _ fun j _ => Submodule.subset_span ⟨f' j, (hj j).1, φ' j, (hj j).2.1, ?_, rfl⟩⟩
  · exact Filter.eventually_cofinite.2 (T.finite_toSet.subset fun v hv => by_contra fun h' => hv ((hi i).2.2 v h'))
  · exact Filter.eventually_cofinite.2 (T.finite_toSet.subset fun v hv => by_contra fun h' => hv ((hj j).2.2 v h'))

end GlobalTheory.ThKSelfOrth
