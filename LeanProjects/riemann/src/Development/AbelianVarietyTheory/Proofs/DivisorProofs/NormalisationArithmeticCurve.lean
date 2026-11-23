import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemChart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonemptyNormalOpenArithmeticVarietyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DimensionOfDominantFlatCover
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueDegreeOfIsOpenImmersion
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteNormalFlatClosure

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB

namespace GlobalTheory.NormalCover

theorem exists_normal_isArithVar (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k)
    [IsIntegral X] (D : ℕ) (hX : IsArithVar p D) :
    ∃ (Y : Scheme.{0}) (_ : IsIntegral Y) (ν : Y ⟶ X), IsFinite ν ∧
      ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Y ∧ IsArithVar (ν ≫ p) D ∧
      ν (genericPoint Y) = genericPoint X ∧ ν.residueDegree (genericPoint Y) ≠ 0 := by
  obtain ⟨Ω, hne, hn⟩ := GlobalTheory.T.exists_nonempty_normal_open_arithmeticVariety k X p D hX
  have := hX.finite
  have : IsFinite (spMap (Int.castRingHom k)) :=
    (IsFinite.SpecMap_iff _).2 (by
      have : (Int.castRingHom k) = algebraMap ℤ k := RingHom.ext_int _ _
      change (Int.castRingHom k).Finite
      rw [this]
      exact RingHom.finite_algebraMap.2 hX.finite)
  have hs : IsProjOver (p ≫ spMap (Int.castRingHom k)) := by
    obtain ⟨h₁, h₂⟩ := (isProjOver_iff_isProper_and_exists_isAmpleLB p).1 hX.isProjOver
    exact (isProjOver_iff_isProper_and_exists_isAmpleLB _).2 ⟨inferInstance, h₂⟩
  have := hX.flat
  obtain ⟨Y, ν, e, hν, hnY, -, hfl, hpb, hd⟩ :=
    GraphClosure.exists_normalisation_of_locallyClosed ℤ X Ω.toScheme
      (p ≫ spMap (Int.castRingHom k)) Ω (𝟙 _) hs inferInstance hn inferInstance
  have he : IsOpenImmersion e := MorphismProperty.of_isPullback hpb.flip inferInstance
  have : Nonempty Ω.toScheme := hne.to_subtype
  have : IsIntegral Ω.toScheme := isIntegral_of_isOpenImmersion Ω.ι
  have : IsIntegral Y := by
    have := GlobalTheory.IsNormalScheme.of_pred hnY
    have h := ((IrreducibleSpace.isIrreducible_univ Ω.toScheme).image _
      e.continuous.continuousOn).closure
    rw [Set.image_univ, hd.closure_eq] at h
    have : IrreducibleSpace Y := (irreducibleSpace_def _).2 h
    exact isIntegral_of_irreducibleSpace_of_isReduced Y
  have hfac : e ≫ ν = Ω.ι := by rw [hpb.w, Category.id_comp]
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
  have hflat : Flat ((ν ≫ p) ≫ spMap (Int.castRingHom k)) := by rwa [Category.assoc]
  exact ⟨Y, ‹_›, ν, hν, hnY, ⟨hX.isDomain, hX.finite, ‹_›, hproj, hflat,
    DimCover.topologicalKrullDim_eq k X Y p (ν ≫ p) D hX hproj hflat ν rfl hgen hdeg⟩,
    hgen, hdeg⟩

theorem exists_normal_surface : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k)
    [IsIntegral X], IsArithVar p 1 → ∃ (Y : Scheme.{0}) (_ : IsIntegral Y) (ν : Y ⟶ X),
      IsFinite ν ∧ ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Y ∧ IsArithVar (ν ≫ p) 1 ∧
      ν (genericPoint Y) = genericPoint X ∧ ν.residueDegree (genericPoint Y) ≠ 0 :=
  fun k _ X p _ h => exists_normal_isArithVar k X p 1 h

end GlobalTheory.NormalCover
