import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasNormGroups
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChevalleyUnits
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DecompositionGroupLocalGaloisIsoStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuationPowOfIsPlaceOverStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsExtensionPowStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MinpolyIrreducibleLocalEmbeddingStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpanBasisImageAdicCompletionEqTopStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LinearIndependentCompletionOfIrreducibleMinpolyAStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdicCompletionTraceNormOfBasisImageStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdicCompletionTraceNormContinuousStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ResidueClosureIsoRamifiedExtStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalEmbeddingsDifferByDecompositionStatement
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

theorem GlobalTheory.LocalExtCompletion.exists_completion_ext : ∀ (K L Ω : Type) [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω] [Field L] [NumberField L] [Algebra L Ω] [IsAlgClosure L Ω] [Algebra K L] [IsScalarTower K L Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K)) (v' : HeightOneSpectrum (𝓞 L)) (h : IsPlaceOver A v) (_ : IsPlaceOver A v'), IsLocalExt L h → ∀ (ι : Ω →ₐ[K] Kbar v) (ι' : Ω →ₐ[L] Kbar v'), IsLocEmb A v ι → IsLocEmb A v' ι' → ∃ (f : v.adicCompletion K →+* v'.adicCompletion L) (b : Kbar v ≃+* Kbar v'), Continuous f ∧ (∀ x, b (algebraMap _ _ x) = algebraMap _ _ (f x)) ∧ (∀ z, b (ι z) = ι' z) ∧ (∀ x : K, f (algebraMap K _ x) = algebraMap L _ (algebraMap K L x)) ∧ (letI := f.toAlgebra; Module.finrank (v.adicCompletion K) (v'.adicCompletion L) = Module.finrank K L ∧ Continuous (Algebra.trace (v.adicCompletion K) (v'.adicCompletion L)) ∧ (∀ z : L, Algebra.trace (v.adicCompletion K) (v'.adicCompletion L) (algebraMap L _ z) = algebraMap K _ (Algebra.trace K L z)) ∧ Continuous (Algebra.norm (v.adicCompletion K) : v'.adicCompletion L → v.adicCompletion K) ∧ ∀ z : L, Algebra.norm (v.adicCompletion K) (algebraMap L (v'.adicCompletion L) z) = algebraMap K _ (Algebra.norm K z)) := by
  intro K L Ω _ _ _ _ _ _ _ _ _ _ _ A v v' h h' hloc ι ι' hι hι'
  obtain ⟨e, he, hv⟩ := GlobalTheory.T.valuation_pow_of_isPlaceOver_alt K L Ω A v v' h h'
  obtain ⟨f, hfc, hfK, hfv⟩ := GlobalTheory.T.exists_extension_pow_alt K L v v' e he hv
  have hirr := GlobalTheory.T.minpoly_irreducible_local_embedding K L Ω A v h (fun σ => by
    obtain ⟨τ, hτ⟩ := hloc σ
    exact ⟨τ, Weil_le_Dec h τ.2, hτ⟩) ι hι
  letI : Algebra (v.adicCompletion K) (v'.adicCompletion L) := f.toAlgebra
  have hind := GlobalTheory.T.linearIndependent_completion_of_irreducible_minpoly_alt K L v v' f hfK hirr _ (Module.finBasis K L)
  have hspan := GlobalTheory.T.span_basis_image_adicCompletion_eq_top_alt K L v v' f hfc hfK _ (Module.finBasis K L)
  let b' : Module.Basis (Fin (Module.finrank K L)) (v.adicCompletion K) (v'.adicCompletion L) :=
    Module.Basis.mk hind hspan.ge
  have hb' : ∀ i, b' i = algebraMap L _ (Module.finBasis K L i) := fun i => Module.Basis.mk_apply _ _ _
  haveI hfd : FiniteDimensional (v.adicCompletion K) (v'.adicCompletion L) := Module.Finite.of_basis b'
  have hrank : Module.finrank (v.adicCompletion K) (v'.adicCompletion L) = Module.finrank K L := by
    rw [Module.finrank_eq_card_basis b', Fintype.card_fin]
  have htn := GlobalTheory.T.adicCompletion_trace_norm_of_basis_image_alt K L v v' f hfK _ (Module.finBasis K L) b' hb'
  have hcont := GlobalTheory.T.adicCompletion_trace_norm_continuous_alt K L v v' f hfc hfd

  haveI : Algebra.IsAlgebraic (v.adicCompletion K) (v'.adicCompletion L) := Algebra.IsAlgebraic.of_finite _ _
  haveI : Algebra.IsAlgebraic (v.adicCompletion K) (Kbar v') :=
    Algebra.IsAlgebraic.trans (v.adicCompletion K) (v'.adicCompletion L) (Kbar v')
  haveI : IsAlgClosure (v.adicCompletion K) (Kbar v') := ⟨inferInstance, inferInstance⟩
  let b₀ : Kbar v ≃ₐ[v.adicCompletion K] Kbar v' := IsAlgClosure.equiv (v.adicCompletion K) (Kbar v) (Kbar v')
  have hb₀ : ∀ x, b₀ (algebraMap (v.adicCompletion K) (Kbar v) x) = algebraMap (v'.adicCompletion L) (Kbar v') (f x) :=
    fun x => (b₀.commutes x).trans rfl
  have hint := GlobalTheory.T.residue_closure_iso_ramified_ext K L v v' e f he hfv hfd b₀.toRingEquiv hb₀
  let ι₂ : Ω →ₐ[K] Kbar v :=
    { (b₀.symm.toRingEquiv.toRingHom.comp ι'.toRingHom) with
      commutes' := fun x => by
        change b₀.symm (ι' (algebraMap K Ω x)) = algebraMap K (Kbar v) x
        rw [IsScalarTower.algebraMap_apply K L Ω, ι'.commutes,
          IsScalarTower.algebraMap_apply L (v'.adicCompletion L) (Kbar v'), ← hfK, ← hb₀,
          AlgEquiv.symm_apply_apply, ← IsScalarTower.algebraMap_apply] }
  have hι₂ : IsLocEmb A v ι₂ := fun z => by
    rw [hι' z, hint]
    change IsIntegral _ (ι' z) ↔ IsIntegral _ (b₀ (b₀.symm (ι' z)))
    rw [AlgEquiv.apply_symm_apply]
  obtain ⟨σ, hσ, hσι⟩ := GlobalTheory.T.local_embeddings_differ_by_decomposition K Ω A v ι ι₂ hι hι₂
  obtain ⟨θ, -, -, hθ⟩ := GlobalTheory.T.decomposition_group_local_galois_iso K Ω A v h ι hι
  let g := θ ⟨σ, hσ⟩
  have hg : ∀ z, g (ι z) = b₀.symm (ι' z) := fun z => (hθ ⟨σ, hσ⟩ z).trans (hσι z).symm
  refine ⟨f, g.toRingEquiv.trans b₀.toRingEquiv, hfc, fun x => ?_, fun z => ?_, hfK, hrank, hcont.1,
    fun z => (htn z).1, hcont.2, fun z => (htn z).2⟩
  · change b₀ (g (algebraMap _ _ x)) = _
    rw [g.commutes, hb₀]
  · change b₀ (g (ι z)) = _
    rw [hg, AlgEquiv.apply_symm_apply]

end
