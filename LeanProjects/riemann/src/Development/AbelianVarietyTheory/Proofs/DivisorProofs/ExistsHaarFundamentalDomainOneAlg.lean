import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipParLeUnipFlag
import Development.AbelianVarietyTheory.Definitions.Foundations.ConstTermOnMulLeftOfNormalizer
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.LanglandsSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitOfCocompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicUnitaryLocallyCompactHausdorffStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedUnipStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalUnitaryCountableDiscreteStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicPlaneComplementDetStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffsZeroOfLev
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoC
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT GlobalTheory.ThK.FlagPar

noncomputable section

namespace GlobalTheory.ThK.UnipDomPlaneAlg

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 2000000 in

theorem exists_haar_fundamentalDomain_one_alg : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n n₁ : ℕ) (W : Spc F E n) (W₁ : Spc F E n₁) (H : Plane E n n₁), (∀ i j, σ (W.J j i) = -W.J i j) → n = n₁ + 2 →
      form σ W.J H.x H.x = 0 → form σ W.J H.y H.y = 0 → form σ W.J H.x H.y = 1 →
      (∀ u, form σ W.J (H.ι *ᵥ u) H.x = 0 ∧ form σ W.J (H.ι *ᵥ u) H.y = 0) → H.ιᵀ * W.J * H.ι.map σ = W₁.J → W.J.det ≠ 0 → W₁.J.det ≠ 0 →
      ∃ (μ : Measure (unip σ W H)) (𝓕 : Set (unip σ W H)), μ.IsHaarMeasure ∧
        IsFundamentalDomain ((ratU σ W.J).subgroupOf (unip σ W H)) 𝓕 μ ∧ μ 𝓕 = 1 := by
  intro F E _ _ _ _ _ σ hcm n n₁ W W₁ H hs hn hxx hyy hxy horth hJ₁ hdet hdet₁
  obtain ⟨i1, i2, i3⟩ := GlobalTheory.T.adelic_unitary_locally_compact_hausdorff F E σ _ W.J
  have hcl := GlobalTheory.T.isClosed_unip' F E σ _ _ W H
  haveI : BorelSpace (UA σ W.J) := ⟨rfl⟩
  haveI : LocallyCompactSpace (unip σ W H) := hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology (unip σ W H) := TopologicalSpace.Subtype.secondCountableTopology _
  obtain ⟨dc, dd⟩ := GlobalTheory.T.rational_unitary_countable_discrete F E σ _ W.J
  set Γ := (ratU σ W.J).subgroupOf (unip σ W H) with hΓ
  have hinj : Function.Injective fun γ : Γ => (⟨γ.1.1, γ.2⟩ : ratU σ W.J) :=
    fun x y h => Subtype.ext (Subtype.ext (congrArg (fun t : ratU σ W.J => (t : UA σ W.J)) h))
  haveI : Countable Γ := hinj.countable
  haveI : DiscreteTopology Γ :=
    DiscreteTopology.of_continuous_injective ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _) hinj
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  obtain ⟨K, hK, hKc⟩ := GlobalTheory.T.hyperbolic_plane_complement_det W W₁ H hcm hs hn hxx hyy hxy horth hJ₁ hdet hdet₁
  refine GlobalTheory.Per.UnitN.exists_unit_of_cocompact Γ hK fun u => ?_
  obtain ⟨γ, hγ, hγu⟩ := hKc u
  exact ⟨γ⁻¹, Γ.inv_mem hγ, γ * u, hγu, by group⟩

end GlobalTheory.ThK.UnipDomPlaneAlg
