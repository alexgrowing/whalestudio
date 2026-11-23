import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFramedPointBaseChangeAlgebraMapStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointBaseChangeUniqueReflIffStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameChangeExistsUniqueOfSamePointStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameChangeCommBaseChangeStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

namespace GlobalTheory.Frames

theorem univFrame_classifies : Out.SecBaseChangeSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (R : Type) [CommRing R] [Algebra c.F R] (A : Type) [CommRing A] [Algebra c.F A] (y₀ : FrPt Xo c R) (π : R →ₐ[c.F] A) (X : (∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) A)) (s : Aˣ) (u : FrPt Xo c A), UnivFrame y₀ π X s u → ∀ (T : Type) [CommRing T] [Algebra c.F T] (z : FrPt Xo c T) (ψ : R →ₐ[c.F] T), z.x = spMap ψ.toRingHom ≫ y₀.x → ∃! a : A →ₐ[c.F] T, a.comp π = ψ ∧ FrMap a u z := by
  intro hS E _ _ _ H Dw l Xo c R _ _ A _ _ y₀ π X s u hu T _ _ z ψ hz
  obtain ⟨⟨-, hring⟩, u₀, hu₀, hchg⟩ := hu
  obtain ⟨z₀, hz₀⟩ := GlobalTheory.T.exists_framedPoint_baseChange_algebraMap hS E H Dw l Xo c R T ψ y₀
  have hx₀ : z₀.x = spMap ψ.toRingHom ≫ y₀.x :=
    (((GlobalTheory.T.framedPoint_baseChange_unique_refl_iff E H Dw l Xo c R T ψ y₀).2.2 z₀).1 hz₀).1
  obtain ⟨hex, huniq⟩ := GlobalTheory.T.frameChange_exists_unique_of_same_point E H Dw l Xo c T z₀ z
  obtain ⟨g, a₀, hg, hgz⟩ := hex (hz.trans hx₀.symm)
  have key : ∀ k : A →ₐ[c.F] T, k.comp π = ψ →
      (FrMap k u z ↔ FrChg (fun τ => (X τ).map k) (k (s : A)) z₀ z) := by
    intro k hk
    obtain ⟨w, hw⟩ := GlobalTheory.T.exists_framedPoint_baseChange_algebraMap hS E H Dw l Xo c A T k u₀
    have hw' : FrMap (k.comp π) y₀ w := frMap_trans (Xo := Xo) (c := c) _ _ _ π k y₀ u₀ w hu₀ hw
    rw [hk] at hw'
    obtain rfl : w = z₀ := (GlobalTheory.T.framedPoint_baseChange_unique_refl_iff E H Dw l Xo c R T ψ y₀).1 w z₀ hw' hz₀
    exact GlobalTheory.T.frameChange_comm_baseChange E H Dw l Xo c A T k u₀ u w z X (s : A) hchg hw
  obtain ⟨k, ⟨hk, hkX, hks⟩, hku⟩ := hring T ψ g a₀ hg
  refine ⟨k, ⟨hk, (key k hk).2 ?_⟩, ?_⟩
  · have h1 : (fun τ => (X τ).map k) = g := funext hkX
    rw [h1, hks]
    exact hgz
  · rintro k' ⟨hk', hm⟩
    obtain ⟨h1, h2⟩ := huniq _ _ _ _ ((key k' hk').1 hm) hgz
    exact hku k' ⟨hk', fun τ => congrFun h1 τ, h2⟩

end GlobalTheory.Frames
