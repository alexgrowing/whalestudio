import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecCarried
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrreducibleSpaceFibreSemiAbelianFieldPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfSpecializesSameFibreIsIntegralHom
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

theorem spMap_eq_closedPoint_iff {R R' : Type} [CommRing R] [IsLocalRing R] [CommRing R'] [IsLocalRing R']
    (ρ : R →+* R') (hρ : ρ.Finite) (y : Sp R') : spMap ρ y = closedPoint R ↔ y = closedPoint R' := by
  letI : Algebra R R' := ρ.toAlgebra
  haveI : Module.Finite R R' := hρ
  haveI : Algebra.IsIntegral R R' := inferInstance
  constructor
  · intro h
    have hc : (y.asIdeal.comap (algebraMap R R')).IsMaximal := by
      have : (spMap ρ y).asIdeal = y.asIdeal.comap ρ := rfl
      rw [h] at this
      change (y.asIdeal.comap ρ).IsMaximal
      rw [← this]; exact IsLocalRing.maximalIdeal.isMaximal R
    haveI : y.asIdeal.IsPrime := PrimeSpectrum.isPrime (y : PrimeSpectrum R')
    have hm : y.asIdeal.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_comap _ hc
    exact PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal hm)
  · rintro rfl
    have hc : ((maximalIdeal R').comap (algebraMap R R')).IsMaximal :=
      Ideal.isMaximal_comap_of_isIntegral_of_isMaximal _
    exact PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal hc)

theorem exists_open_secNz_closedFibre : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (hB : Base R) (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R') (hF : FinExt ρ) (hG : IsGal ρ) (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'] (hS' : IsSemiAbelian G') (U' : Unif (maximalIdeal R') D' A' G') (a : GalAct ρ hD U') (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (β : G'.left ⟶ G.left) (hS : IsSemiAbelian G) (hβ : IsGrpPullback G' G (spMap ρ) β) (hact : ∀ σ, a.act σ ≫ β = β), ∀ θ : U'.LG.L.Sec, (∃ g' : G'.left, G'.hom g' = closedPoint R' ∧ g' ∈ secNz θ) → ∃ O : G.left.Opens, (∃ g ∈ O, G.hom g = closedPoint R) ∧ ∀ g' : G'.left, β g' ∈ O → G.hom (β g') = closedPoint R → g' ∈ secNz θ := by
  intro R _ _ _ hB R' _ _ _ ρ hF hG D D' hD A' G' _ _ hS' U' a G _ _ β hS hβ hact θ ⟨g0, hg0c, hg0⟩
  have hfin : IsFinite (spMap ρ) := by rw [IsFinite.SpecMap_iff]; exact hF.2.2
  haveI hβfin : IsFinite β := MorphismProperty.of_isPullback hβ.1.flip hfin
  have hcl : IsClosedMap β := β.isClosedMap
  have hsq : ∀ g' : G'.left, G.hom (β g') = spMap ρ (G'.hom g') := fun g' => by
    change (β ≫ G.hom) g' = (G'.hom ≫ spMap ρ) g'
    rw [hβ.1.w]

  obtain ⟨s, hs⟩ : ∃ s : (Sp R' : Scheme.{0}), s = closedPoint R' := ⟨_, rfl⟩
  rw [← hs] at hg0c
  haveI hirr : IrreducibleSpace (G'.hom.fiber s) :=
    GlobalTheory.SemiAbFibre.irreducibleSpace_fibre _ G' hS' _ ((Sp R').fromSpecResidueField s)
  obtain ⟨η', hη'⟩ : ∃ η' : G'.left, η' = G'.hom.fiberι s (genericPoint (G'.hom.fiber s)) := ⟨_, rfl⟩
  have hspec : ∀ g' : G'.left, G'.hom g' = s → η' ⤳ g' := by
    intro g' hg'
    obtain ⟨z, hz⟩ : g' ∈ Set.range (G'.hom.fiberι s) := (Scheme.Hom.range_fiberι G'.hom s).ge hg'
    rw [← hz, hη']
    exact ((genericPoint_spec (G'.hom.fiber s)).specializes trivial).map (G'.hom.fiberι s).continuous
  have hηs : G'.hom η' = s := by
    rw [hη']; exact (Scheme.Hom.range_fiberι G'.hom s).le ⟨_, rfl⟩
  have hηnz : η' ∈ secNz θ := (hspec g0 hg0c).mem_open (secNz θ).isOpen hg0
  refine ⟨⟨farSet β θ, isOpen_farSet β hcl θ⟩, ⟨β η', ?_, ?_⟩, ?_⟩
  · show ∀ g', β g' = β η' → g' ∈ secNz θ
    intro g' hg'
    have hg's : G'.hom g' = s := by
      rw [hs, ← spMap_eq_closedPoint_iff ρ hF.2.2, ← hsq, hg', hsq, hηs]
      exact (spMap_eq_closedPoint_iff ρ hF.2.2 s).2 hs
    have := GlobalTheory.eq_of_specializes_of_isIntegralHom β (hspec g' hg's) hg'.symm
    rw [← this]; exact hηnz
  · rw [hsq, hηs]; exact (spMap_eq_closedPoint_iff ρ hF.2.2 s).2 hs
  · intro g' hg' _
    exact hg' g' rfl

end GlobalTheory.Mum
