import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CyclicStrongAtCusp
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RestrictEqInvLocalArtinMap
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalArtinFrobeniusAction
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalEmbeddingOverPlace
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DecompositionGroupLocalGaloisIso
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIntegralIffSpectralNormLeOne
import GroundTheory.LocalFields.MainTheorem
import GroundTheory.GlobalFields.CompletionAtPlace
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

open GlobalTheory.LocDict GroundTheory.LocalField GroundTheory.Global.AdicLiesOver

namespace GlobalTheory.ArtinNormU

theorem localArtin_normU : ∀ (K L Ω : Type) [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω] [Field L] [NumberField L] [Algebra L Ω] [IsAlgClosure L Ω] [Algebra K L] [IsScalarTower K L Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K)) (v' : HeightOneSpectrum (𝓞 L)) (h : IsPlaceOver A v) (h' : IsPlaceOver A v') [v'.asIdeal.LiesOver v.asIdeal] (a : Weil h →* (v.adicCompletion K)ˣ) (a' : Weil h' →* (v'.adicCompletion L)ˣ), IsLocalArtin h a → IsLocalArtin h' a' → ∀ (g : Weil h) (g' : Weil h'), (∀ z : Ω, (g : G K Ω) z = (g' : G L Ω) z) → a g = GlobalTheory.BCChar.normU v v' (a' g') := by
  intro K L Ω _ _ _ _ _ _ _ _ _ _ _ A v v' h h' _ a a' ha ha' g g' hgg
  classical
  haveI : CharZero (v.adicCompletion K) := charZero_of_injective_algebraMap (algebraMap K (v.adicCompletion K)).injective
  haveI : CharZero (v'.adicCompletion L) :=
    charZero_of_injective_algebraMap (algebraMap L (v'.adicCompletion L)).injective
  haveI : IsSepClosure (v'.adicCompletion L) (Kbar v') := ⟨inferInstance, inferInstance⟩
  haveI : Algebra.IsSeparable (v.adicCompletion K) (v'.adicCompletion L) := inferInstance
  haveI : IsSepClosure (v.adicCompletion K) (Kbar v') :=
    isSepClosure_of_isSeparable (v.adicCompletion K) (v'.adicCompletion L) (Kbar v')
  haveI : Algebra.IsAlgebraic (v.adicCompletion K) (v'.adicCompletion L) := Algebra.IsAlgebraic.of_finite _ _
  haveI : Algebra.IsAlgebraic (v.adicCompletion K) (Kbar v') :=
    Algebra.IsAlgebraic.trans (v.adicCompletion K) (v'.adicCompletion L) (Kbar v')
  haveI : IsAlgClosure (v.adicCompletion K) (Kbar v') := ⟨inferInstance, inferInstance⟩
  obtain ⟨ι', hι'⟩ := GlobalTheory.LocDict.exists_isLocEmb L Ω A v' h'
  obtain ⟨θ, -, -, hθ⟩ := GlobalTheory.LocDec.decomposition_mulEquiv_galLoc L Ω A v' h' ι' hι'
  let gL : GalLoc v' := θ ⟨g', Weil_le_Dec h' g'.2⟩
  have hgL : Lifts ι' gL (g' : G L Ω) := hθ _
  let gK : Kbar v' ≃ₐ[v.adicCompletion K] Kbar v' := gL.restrictScalars (v.adicCompletion K)
  have hgK : ∀ z : Ω, gK (ι'.toRingHom z) = ι'.toRingHom ((g : G K Ω) z) := fun z => by
    change gL (ι' z) = ι' _
    rw [hgL z, hgg z]
  have hj : ∀ x : K, ι'.toRingHom (algebraMap K Ω x) =
      algebraMap (v.adicCompletion K) (Kbar v') (algebraMap K (v.adicCompletion K) x) := fun x => by
    rw [IsScalarTower.algebraMap_apply K L Ω]
    change ι' (algebraMap L Ω _) = _
    rw [ι'.commutes, IsScalarTower.algebraMap_apply (v.adicCompletion K) (v'.adicCompletion L) (Kbar v'),
      GroundTheory.Global.AdicLiesOver.algebraMap_eq, GroundTheory.Global.adicCompletionMap_algebraMap,
      ← IsScalarTower.algebraMap_apply L (v'.adicCompletion L) (Kbar v')]
  let b : Kbar v ≃ₐ[v.adicCompletion K] Kbar v' := IsAlgClosure.equiv (v.adicCompletion K) (Kbar v) (Kbar v')
  have hb : ∀ x, (b : Kbar v ≃+* Kbar v') (algebraMap _ (Kbar v) x) =
      algebraMap (v'.adicCompletion L) (Kbar v') (GroundTheory.Global.adicCompletionMap v v' x) := fun x => by
    change b _ = _
    rw [b.commutes, IsScalarTower.algebraMap_apply (v.adicCompletion K) (v'.adicCompletion L) (Kbar v')]
    rfl
  have hc : (algebraMap (v.adicCompletion K) (Kbar v')).comp
      (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) =
      (b : Kbar v →+* Kbar v').comp (algebraMap (v.adicCompletionIntegers K) (Kbar v)) := RingHom.ext fun x => by
    rw [RingHom.comp_apply, RingHom.comp_apply,
      IsScalarTower.algebraMap_apply (v.adicCompletionIntegers K) (v.adicCompletion K) (Kbar v)]
    exact (b.commutes _).symm
  have hA : ∀ z : Ω, z ∈ A ↔ ((algebraMap (v.adicCompletion K) (Kbar v')).comp
      (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K))).IsIntegralElem (ι'.toRingHom z) := fun z => by
    have e := GlobalTheory.ClosureIso.isIntegral_map_iff (GroundTheory.Global.adicCompletionMap v v')
      (GroundTheory.Global.continuous_adicCompletionMap v v') (b : Kbar v ≃+* Kbar v') hb (b.symm (ι' z))
    have e2 : (b : Kbar v ≃+* Kbar v') (b.symm (ι' z)) = ι' z := b.apply_symm_apply _
    rw [e2] at e
    rw [hι' z, e, hc]
    change _ ↔ ((b : Kbar v →+* Kbar v').comp (algebraMap (v.adicCompletionIntegers K) (Kbar v))).IsIntegralElem (ι' z)
    constructor
    · rintro ⟨p, hp, hp'⟩
      refine ⟨p, hp, ?_⟩
      have := congrArg (b : Kbar v →+* Kbar v') hp'
      rw [Polynomial.hom_eval₂, map_zero] at this
      rwa [show (b : Kbar v →+* Kbar v') (b.symm (ι' z)) = ι' z from b.apply_symm_apply _] at this
    · rintro ⟨p, hp, hp'⟩
      refine ⟨p, hp, (b : Kbar v →+* Kbar v').injective ?_⟩
      rw [Polynomial.hom_eval₂, map_zero, show (b : Kbar v →+* Kbar v') (b.symm (ι' z)) = ι' z from b.apply_symm_apply _]
      exact hp'
  have HK := (GlobalTheory.ArtinCompare.restrict_eq_inv_reciprocity K Ω A v h (Kbar v') ι'.toRingHom hj hA a ha g gK hgK).1
  have HL := GlobalTheory.ArtinCompareApply.lift_localArtinMap_apply L Ω A v' h' a' ha' ι' hι' g' gL hgL
  have kK : ∀ (y : Kbar v') (hy : y ∈ maximalAbelianExtension (v.adicCompletion K) (Kbar v')),
      gK ((localArtinMap (v.adicCompletion K) (Kbar v') (a g) ⟨y, hy⟩ :
        maximalAbelianExtension (v.adicCompletion K) (Kbar v')) : Kbar v') = y := fun y hy => by
    have e : AlgEquiv.restrictNormalHom (maximalAbelianExtension (v.adicCompletion K) (Kbar v')) gK
        (localArtinMap (v.adicCompletion K) (Kbar v') (a g) ⟨y, hy⟩) = ⟨y, hy⟩ := by
      rw [HK, ← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]
    have e2 := congrArg (fun y : maximalAbelianExtension (v.adicCompletion K) (Kbar v') => (y : Kbar v')) e
    simp only [AlgEquiv.restrictNormalHom_apply] at e2
    exact e2
  have key : localArtinMap (v.adicCompletion K) (Kbar v') (a g) =
      localArtinMap (v.adicCompletion K) (Kbar v') (normUnits (v.adicCompletion K) (v'.adicCompletion L) (a' g')) := by
    refine AlgEquiv.ext fun y => Subtype.ext ?_
    have hN := localArtinMap_norm (K := v.adicCompletion K) (K' := v'.adicCompletion L) (Ω := Kbar v') (a' g') y.2
    apply gK.injective
    rw [kK y y.2]
    change (y : Kbar v') = gL _
    rw [← hN, HL]
  exact injective_localArtinMap key

end GlobalTheory.ArtinNormU
