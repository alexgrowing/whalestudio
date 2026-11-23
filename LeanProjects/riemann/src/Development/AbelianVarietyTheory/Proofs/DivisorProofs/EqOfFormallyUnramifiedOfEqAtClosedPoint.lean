import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaCompOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
open scoped CategoryTheory.Obj
attribute [local instance] CategoryTheory.Hom.group
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelMod)
open MonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.TorsSpec

theorem eq_of_unramified_of_closedPoint : ∀ {S T : Scheme.{0}} (f : T ⟶ S) [FormallyUnramified f]
    [LocallyOfFiniteType f] (R : CommRingCat.{0}) [IsLocalRing R] (u₁ u₂ : Spec R ⟶ T) (h : u₁ ≫ f = u₂ ≫ f)
    (K : Type) [Field K] (k : Sp K ⟶ Spec R) (hk : ∀ x, k x = IsLocalRing.closedPoint R)
    (hku : k ≫ u₁ = k ≫ u₂), u₁ = u₂ := by
  intro S T f _ _ R _ u₁ u₂ h K _ k hk hku
  let g : Spec R ⟶ pullback f f := pullback.lift u₁ u₂ h
  have hkg : k ≫ g = (k ≫ u₁) ≫ pullback.diagonal f := by
    apply pullback.hom_ext
    · simp [g, pullback.lift_fst]
    · simp [g, hku, pullback.lift_snd]
  obtain ⟨x⟩ : Nonempty (Sp K) := (inferInstance : Nonempty (PrimeSpectrum K))
  have hc : g (IsLocalRing.closedPoint R) ∈ Set.range (pullback.diagonal f) := by
    refine ⟨(k ≫ u₁) x, ?_⟩
    rw [← hk x, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hkg]
  have hopen : IsOpen (Set.range (pullback.diagonal f)) :=
    (pullback.diagonal f).isOpenEmbedding.isOpen_range
  have hr : Set.range g ⊆ Set.range (pullback.diagonal f) := by
    rintro _ ⟨y, rfl⟩
    have hs : y ⤳ IsLocalRing.closedPoint R := IsLocalRing.specializes_closedPoint y
    exact (hs.map g.continuous).mem_open hopen hc
  have hl := IsOpenImmersion.lift_fac (pullback.diagonal f) g hr
  have h1 : u₁ = IsOpenImmersion.lift (pullback.diagonal f) g hr := by
    have e : (IsOpenImmersion.lift (pullback.diagonal f) g hr ≫ pullback.diagonal f) ≫ pullback.fst f f
        = g ≫ pullback.fst f f := by rw [hl]
    rw [Category.assoc, pullback.diagonal_fst, Category.comp_id, pullback.lift_fst] at e
    exact e.symm
  have h2 : u₂ = IsOpenImmersion.lift (pullback.diagonal f) g hr := by
    have e : (IsOpenImmersion.lift (pullback.diagonal f) g hr ≫ pullback.diagonal f) ≫ pullback.snd f f
        = g ≫ pullback.snd f f := by rw [hl]
    rw [Category.assoc, pullback.diagonal_snd, Category.comp_id, pullback.lift_snd] at e
    exact e.symm
  exact h1.trans h2.symm

end GlobalTheory.TorsSpec
