import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsModelOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NefFibOfIsGenerated
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JGenSpecializes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonemptyNormalOpenArithmeticVarietyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemChart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DimensionOfDominantFlatCover
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueDegreeOfIsOpenImmersion
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteNormalFlatClosure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalCoordinatesExtendProjectiveSpace
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical

open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.TrueGeo

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.NormalModel

open TopologicalSpace

theorem exists_normal_model : ∀ (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] (D m : ℕ) (y : Fin (m + 1) → Ω) (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp (𝓞 K)) (g : X ⟶ PSpace (𝓞 K) m) (ψ : Ω →+* X.functionField),
    (g ≫ PSpace.str (𝓞 K) m = p ∧ IsArithVar p D ∧ Function.Bijective ψ ∧
      (∀ a : 𝓞 K, ψ (algebraMap K Ω (a : K)) = fnOf ⊤ (TopologicalSpace.Opens.mem_top _) (algX p ⊤ a)) ∧
      ∀ (k l : Fin (m + 1)) (i : ((ProjSpace.O1 (𝓞 K) m).pull g).ι) (h : genericPoint X ∈ ((ProjSpace.O1 (𝓞 K) m).pull g).U i),
        ψ (y k) * fnOf _ h ((GlobalTheory.Cartier.secPull (ProjSpace.coord (𝓞 K) m l) g).f i) =
          ψ (y l) * fnOf _ h ((GlobalTheory.Cartier.secPull (ProjSpace.coord (𝓞 K) m k) g).f i)) →
    ∃ (X' : Scheme.{0}) (_ : IsIntegral X') (p' : X' ⟶ Sp (𝓞 K)) (g' : X' ⟶ PSpace (𝓞 K) m) (ψ' : Ω →+* X'.functionField),
      g' ≫ PSpace.str (𝓞 K) m = p' ∧ IsArithVar p' D ∧ ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X' ∧ Function.Bijective ψ' ∧
      (∀ a : 𝓞 K, ψ' (algebraMap K Ω (a : K)) = fnOf ⊤ (TopologicalSpace.Opens.mem_top _) (algX p' ⊤ a)) ∧
      ∀ (k l : Fin (m + 1)) (i : ((ProjSpace.O1 (𝓞 K) m).pull g').ι) (h : genericPoint X' ∈ ((ProjSpace.O1 (𝓞 K) m).pull g').U i),
        ψ' (y k) * fnOf _ h ((GlobalTheory.Cartier.secPull (ProjSpace.coord (𝓞 K) m l) g').f i) =
          ψ' (y l) * fnOf _ h ((GlobalTheory.Cartier.secPull (ProjSpace.coord (𝓞 K) m k) g').f i) := by
  intro K Ω _ _ _ _ D m y X _ p g ψ ⟨hgp, hX, hψ, hK, hy⟩
  obtain ⟨W, hne, hn⟩ := GlobalTheory.T.exists_nonempty_normal_open_arithmeticVariety (𝓞 K) X p D hX
  have := hX.finite
  have : IsFinite (spMap (Int.castRingHom (𝓞 K))) :=
    (IsFinite.SpecMap_iff _).2 (by
      have : (Int.castRingHom (𝓞 K)) = algebraMap ℤ (𝓞 K) := RingHom.ext_int _ _
      change (Int.castRingHom (𝓞 K)).Finite
      rw [this]
      exact RingHom.finite_algebraMap.2 hX.finite)
  have hs : IsProjOver (p ≫ spMap (Int.castRingHom (𝓞 K))) := by
    obtain ⟨h₁, h₂⟩ := (isProjOver_iff_isProper_and_exists_isAmpleLB p).1 hX.isProjOver
    exact (isProjOver_iff_isProper_and_exists_isAmpleLB _).2 ⟨inferInstance, h₂⟩
  have := hX.flat
  obtain ⟨Y, ν, e, hν, hnY, -, hfl, hpb, hd⟩ :=
    GraphClosure.exists_normalisation_of_locallyClosed ℤ X W.toScheme
      (p ≫ spMap (Int.castRingHom (𝓞 K))) W (𝟙 _) hs inferInstance hn inferInstance
  have he : IsOpenImmersion e := MorphismProperty.of_isPullback hpb.flip inferInstance
  have : Nonempty W.toScheme := hne.to_subtype
  have : IsIntegral W.toScheme := isIntegral_of_isOpenImmersion W.ι
  have : IsIntegral Y := by
    have := GlobalTheory.IsNormalScheme.of_pred hnY
    have h := ((IrreducibleSpace.isIrreducible_univ W.toScheme).image _
      e.continuous.continuousOn).closure
    rw [Set.image_univ, hd.closure_eq] at h
    have : IrreducibleSpace Y := (irreducibleSpace_def _).2 h
    exact isIntegral_of_irreducibleSpace_of_isReduced Y
  have hfac : e ≫ ν = W.ι := by rw [hpb.w, Category.id_comp]
  have hoi : IsOpenImmersion (e ≫ ν) := by rw [hfac]; infer_instance
  have hg : e (genericPoint _) = genericPoint Y := genericPoint_eq_of_isOpenImmersion _
  have hgen : ν (genericPoint Y) = genericPoint X := by
    rw [← hg, ← Scheme.Hom.comp_apply]
    exact genericPoint_eq_of_isOpenImmersion _
  have hdeg : ν.residueDegree (genericPoint Y) ≠ 0 := by
    intro h0
    have h1 := CurveDegreesCompare.residueDegree_comp e ν (genericPoint _)
    rw [CurveDegreesCompare.residueDegree_of_isOpenImmersion, hg, h0, zero_mul] at h1
    exact one_ne_zero h1
  have hproj : IsProjOver (ν ≫ p) := isProjOver_comp_of_isFinite ν hX.isProjOver
  have hflat : Flat ((ν ≫ p) ≫ spMap (Int.castRingHom (𝓞 K))) := by rwa [Category.assoc]
  have har : IsArithVar (ν ≫ p) D := ⟨hX.isDomain, hX.finite, ‹_›, hproj, hflat,
    DimCover.topologicalKrullDim_eq (𝓞 K) X Y p (ν ≫ p) D hX hproj hflat ν rfl hgen hdeg⟩

  have hη : ν (genericPoint Y) ⤳ genericPoint X := specializes_of_eq hgen
  have hWη : W.ι (genericPoint W.toScheme) ⤳ genericPoint X :=
    specializes_of_eq (genericPoint_eq_of_isOpenImmersion _)
  have heη : e (genericPoint W.toScheme) ⤳ genericPoint Y := specializes_of_eq hg
  have hbij : Function.Bijective (SmallSec.fnMap ν hη) := by
    refine ⟨(SmallSec.fnMap ν hη).injective, fun u => ?_⟩
    obtain ⟨t, ht⟩ := SmallSec.fnMap_surjective W.ι hWη (SmallSec.fnMap e heη u)
    refine ⟨t, (SmallSec.fnMap e heη).injective ?_⟩
    rw [← ht, ← ProjSpace.fnMap_comp e ν heη hη (ProjSpace.comp_genericPoint_specializes _ _ heη hη)]
    exact ProjSpace.fnMap_congr hfac _ _ t
  refine ⟨Y, ‹_›, ν ≫ p, ν ≫ g, (SmallSec.fnMap ν hη).comp ψ, by rw [Category.assoc, hgp], har, hnY,
    hbij.comp hψ, fun a => ?_, fun k l i h => ?_⟩
  · have e₁ : ν.app ⊤ (algX p ⊤ a) = algX (ν ≫ p) ⊤ a := by
      simp [algX, Scheme.Hom.appLE]
      rfl
    rw [RingHom.comp_apply, hK, SmallSec.fnMap_fnOf ν hη _ (Opens.mem_top _), e₁]
    rfl
  · have hX' : genericPoint X ∈ ((ProjSpace.O1 (𝓞 K) m).pull g).U i := (pull_U _ g i).ge (by
      have h' : ν (genericPoint Y) ∈ g ⁻¹ᵁ (ProjSpace.O1 (𝓞 K) m).U (i PUnit.unit) :=
        (pull_U _ (ν ≫ g) i).le h
      rw [hgen] at h'
      exact h')
    have key (a : Fin (m + 1)) : fnOf _ h ((GlobalTheory.Cartier.secPull (ProjSpace.coord (𝓞 K) m a) (ν ≫ g)).f i) =
        SmallSec.fnMap ν hη (fnOf _ hX' ((GlobalTheory.Cartier.secPull (ProjSpace.coord (𝓞 K) m a) g).f i)) := by
      have h₁ : genericPoint Y ∈ (ν ≫ g) ⁻¹ᵁ (ProjSpace.O1 (𝓞 K) m).U (i PUnit.unit) :=
        (pull_U _ (ν ≫ g) i).le h
      have h₂ : genericPoint X ∈ g ⁻¹ᵁ (ProjSpace.O1 (𝓞 K) m).U (i PUnit.unit) :=
        (pull_U _ g i).le hX'
      change fnOf _ h (resG Y _ _) = SmallSec.fnMap ν hη (fnOf _ hX' (resG X _ _))
      rw [fnOf_resG, fnOf_resG, SmallSec.fnMap_fnOf ν hη h₂ h₁, Scheme.Hom.comp_app]
      rfl
    rw [RingHom.comp_apply, RingHom.comp_apply, key, key, ← map_mul, ← map_mul, hy k l i hX']

end GlobalTheory.NormalModel
