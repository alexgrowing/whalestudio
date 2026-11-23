import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonemptyTorusExtensionOfIsAlgClosed
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AllTorsMap
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.GeneratorValues
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TorusPart

theorem mono_gtTorus_and_factor {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {A : Type}
    [CommRing A] [IsLocalRing A] [IsNoetherianRing A] {ρ : R →+* A} {D : Out.DegPre R} {e : ℕ}
    {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] {G₀ : Over (Sp A)} [GrpObj G₀]
    {φ : G₀.left ⟶ G.left} (g : Out.GtCoord I D e G) (hρ : ∀ x ∈ I ^ (e + 1), ρ x = 0)
    (h : IsGrpPullback G₀ G (spMap ρ) φ) :
    Mono (gtTorus g hρ h) ∧ ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
      (i : splitTorus (Sp A) X ⟶ G₀), IsMonHom i →
        ∃ r : D.X →+ X, i = GlobalTheory.SplitTorus.torusMap _ r ≫ gtTorus g hρ h := by
  have := g.i_hom; have := g.q_hom; have := D.P.isAb.proper
  have : IsProper (Out.thickObj R I e D.P.A).hom := inferInstanceAs (IsProper (pullback.snd _ _))
  obtain ⟨q', hq', hk'⟩ := exists_isKernel_pullTorus (isGrpPullback_thickLift hρ h) g.i g.q g.isKernel
  have hk : IsPullback (gtTorus g hρ h) (toUnit _) q' η[_] := hk'
  have : IsProper ((Over.pullback (thickPt e hρ)).obj (Out.thickObj R I e D.P.A)).hom :=
    inferInstanceAs (IsProper (pullback.snd _ _))
  haveI : ConnectedSpace (Sp A) := GlobalTheory.SplitTorus.connectedSpace_of_isLocalRing A
  have hm : Mono (gtTorus g hρ h) := ⟨fun a b k => hk.hom_ext k (toUnit_unique _ _)⟩
  refine ⟨hm, fun X _ _ _ i hi => ?_⟩
  haveI := hi; haveI := hq'
  have ht : i ≫ q' = toUnit _ ≫ η[_] :=
    splitTorus_hom_proper_trivial_local A X _ (i ≫ q') inferInstance
  let u := hk.lift i (toUnit _) ht
  have hu : u ≫ gtTorus g hρ h = i := hk.lift_fst _ _ _
  have : IsMonHom u := Serre.isMonHom_of_mul_comp u fun T x y => by
    rw [← cancel_mono (gtTorus g hρ h), MonObj.mul_comp (x ≫ u), Category.assoc, Category.assoc,
      Category.assoc, hu, MonObj.mul_comp]
  obtain ⟨r, hr⟩ := GlobalTheory.SplitTorus.exists_eq_torusMap u
  exact ⟨r, by rw [← hr, hu]⟩

theorem mono_gtTorus_unif_and_factor : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (t : SAB H (Sp R)) (P : PELUnif I t)
    (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (a : R →+* A) (e : ℕ) (ha : ∀ x ∈ I ^ (e + 1), a x = 0)
    (G₀ : Over (Sp A)) [GrpObj G₀] (φ : G₀.left ⟶ t.G.left) (h : IsGrpPullback G₀ t.G (spMap a) φ),
    Mono (GlobalTheory.TorusPart.gtTorus (P.U.gt e) ha h) ∧
    ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (i : splitTorus (Sp A) X ⟶ G₀), IsMonHom i →
      ∃ ρ : P.D.toPre.X →+ X, i = GlobalTheory.SplitTorus.torusMap _ ρ ≫ GlobalTheory.TorusPart.gtTorus (P.U.gt e) ha h := by
  intro E _ _ _ H R _ _ I t P A _ _ _ a e ha G₀ _ φ h
  exact mono_gtTorus_and_factor (P.U.gt e) ha h

end GlobalTheory.TorusPart
