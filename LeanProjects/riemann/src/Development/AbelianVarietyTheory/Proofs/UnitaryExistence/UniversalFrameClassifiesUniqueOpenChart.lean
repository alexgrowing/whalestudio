import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.UniversalFrameClassifiesFramedPointsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

namespace GlobalTheory.Frames

private theorem spectrumMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]

theorem univFrame_classifies_unique : Out.SecBaseChangeSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (R : Type) [CommRing R] [Algebra c.F R] (A : Type) [CommRing A] [Algebra c.F A] (j : Sp R ⟶ Xo.XF c) (y₀ : FrPt Xo c R) (π : R →ₐ[c.F] A) (X : (∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) A)) (s : Aˣ) (u : FrPt Xo c A), OpenChart j y₀ → UnivFrame y₀ π X s u → ∀ (T : Type) [CommRing T] [Algebra c.F T] (a a' : A →ₐ[c.F] T) (z : FrPt Xo c T), FrMap a u z → FrMap a' u z → a = a' := by
  intro hS E _ _ _ H Dw l Xo c R _ _ A _ _ j y₀ π X s u hj hu T _ _ a a' z ha ha'
  obtain ⟨hopen, hj1, hj2⟩ := hj
  obtain ⟨u₀, hπ, hchg⟩ := hu.2
  have key : ∀ b : A →ₐ[c.F] T, FrMap b u z → z.x = spMap (b.comp π).toRingHom ≫ y₀.x := by
    intro b hb
    rw [hb.1, hchg.1, hπ.1, ← Category.assoc, ← spectrumMap_comp]
    rfl
  have hov : ∀ ψ : R →ₐ[c.F] T, spMap ψ.toRingHom ≫ spMap (algebraMap c.F R) = spMap (algebraMap c.F T) := by
    intro ψ
    rw [← spectrumMap_comp]
    congr 1
    exact ψ.comp_algebraMap
  have h1 : spMap (a.comp π).toRingHom ≫ j = spMap (a'.comp π).toRingHom ≫ j := by
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, hj1, ← key a ha, ← key a' ha']
    · rw [Category.assoc, Category.assoc, hj2, hov, hov]
  have h2 : spMap (a.comp π).toRingHom = spMap (a'.comp π).toRingHom := (cancel_mono j).1 h1
  have h3 : a.comp π = a'.comp π := by
    have h4 := Spec.map_injective h2
    have h5 := congrArg CommRingCat.Hom.hom h4
    exact AlgHom.coe_ringHom_injective h5
  obtain ⟨b, -, hb⟩ := GlobalTheory.T.universalFrame_classifies_framedPoints hS E H Dw l Xo c R A y₀ π X s u hu T z (a.comp π) (key a ha)
  exact (hb a ⟨rfl, ha⟩).trans (hb a' ⟨h3.symm, ha'⟩).symm

end GlobalTheory.Frames
