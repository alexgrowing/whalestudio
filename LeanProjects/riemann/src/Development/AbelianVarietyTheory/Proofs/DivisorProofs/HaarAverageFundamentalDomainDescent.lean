import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockMatrixTwoByTwoFinTranspose
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.MixModel GlobalTheory.SWLit
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (UA incM ratU)
open GlobalTheory.WeilM (Darboux symp schA thetaSum UG)
open GlobalTheory.SiegelFormula (coord)
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SWLink

namespace GlobalTheory.SWLink

theorem exists_transport_mean {G H : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G] [BorelSpace G]
    [IsTopologicalGroup G] [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [SecondCountableTopology H]
    [MeasurableSpace H] [BorelSpace H] (Γ : Subgroup G) (Δ : Subgroup H) [DiscreteTopology Δ] (ι : G ≃ₜ* H)
    (hι : ∀ h, h ∈ Γ ↔ ι h ∈ Δ) (ν : Measure H) [ν.IsHaarMeasure] :
    ∃ (ν' : Measure G) (𝓕 : Set G), ν'.IsHaarMeasure ∧ IsFundamentalDomain Γ 𝓕 ν' ∧
      ∀ f : H → ℂ, LeftInv Δ f → ⨍ h in 𝓕, f (ι h) ∂ν' = ⨍ q, GlobalTheory.AutomorphicL2Unitary.descend Δ f q ∂GlobalTheory.AutomorphicL2Unitary.quotMeasure Δ ν := by
  have h₀ := isFundamentalDomain_stdDom Δ ν
  let e : G ≃ᵐ H := ι.toHomeomorph.toMeasurableEquiv
  have hp : MeasurePreserving e (ν.map e.symm) ν := ⟨e.measurable, e.map_map_symm⟩
  refine ⟨ν.map e.symm, e ⁻¹' stdDom Δ, ι.symm.isHaarMeasure_map ν, ?_, fun f hf => ?_⟩
  · refine h₀.preimage_of_equiv hp.quasiMeasurePreserving
      (e := fun δ : Δ => (⟨ι.symm δ, (hι _).2 (by rw [ι.apply_symm_apply]; exact δ.2)⟩ : Γ))
      ⟨fun a b hab => ?_, fun γ => ?_⟩ fun δ x => ?_
    · exact Subtype.ext (ι.symm.injective (congrArg Subtype.val hab))
    · exact ⟨⟨ι γ, (hι _).1 γ.2⟩, Subtype.ext (ι.symm_apply_apply _)⟩
    · exact (map_mul ι (ι.symm δ) x).trans (congrArg (· * ι x) (ι.apply_symm_apply _))
  · rw [setAverage_eq, average_eq, GlobalTheory.AutomorphicL2Unitary.integral_quotMeasure h₀, measureReal_def, measureReal_def,
      GlobalTheory.AutomorphicL2Unitary.quotMeasure_univ h₀,
      hp.measure_preimage_equiv]
    simp only [hf.descend_mk]
    exact congrArg _ (hp.setIntegral_preimage_emb e.measurableEmbedding f _)

theorem exists_fundDom_mean : ∀ (D : D7) (V : HSp D) (ι : UD D (-V.gram) ≃ₜ* GA D V), (∀ h, h ∈ ratU D.sp.cm.sig (-V.gram) ↔ ι h ∈ GQ V) → ∀ ν : Measure (GA D V), ν.IsHaarMeasure → ∃ (ν' : Measure (UD D (-V.gram))) (𝓕 : Set (UD D (-V.gram))), ν'.IsHaarMeasure ∧ IsFundamentalDomain (ratU D.sp.cm.sig (-V.gram)) 𝓕 ν' ∧ ∀ f : GA D V → ℂ, LeftInv (GQ V) f → ⨍ h in 𝓕, f (ι h) ∂ν' = ⨍ q, descend (GQ V) f q ∂autMeasure V ν := by
  intro D V ι hι ν hν
  have : BorelSpace (UD D (-V.gram)) := ⟨rfl⟩
  exact exists_transport_mean _ _ ι hι ν

end GlobalTheory.SWLink
