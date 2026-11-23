import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Heat

theorem weight_scalar_zero_eq_one : ∀ {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X] {oa : Q.OAct O} (Y : Ray oa) (S : Type) [CommRing S] (φ : R →+* S) (x x' : Over.mk (spMap φ) ⟶ Y.H) (c : Q.X → Sˣ), x' ≫ Y.q = x ≫ Y.q → (∀ χ y J, Good Q.P.L y J → val ((Y.Φ _ x').s χ) (𝟙 _) y J = gm (𝟙 (Over.mk (spMap φ)).left) y ⊤ (unitOn (c χ)) * val ((Y.Φ _ x).s χ) (𝟙 _) y J) → c 0 = 1 := by
  intro R _ _ Q O _ _ _ oa Y S _ φ x x' c _ h
  have e : unitOn (c 0) = unitOn (1 : Sˣ) := by
    refine ReciprocityTheory.ChartRestriction.G.Geo.Tor.unit_ext (X := (Over.mk (spMap φ)).left) (V := ⊤) fun y _ => ?_
    choose J hJ using fun ψ : (Over.mk (spMap φ)).left ⟶ Q.P.A.left =>
      ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_chart Q.P.isLB (ψ y)
    have hG : Good Q.P.L y J := hJ
    have h0 := h 0 y J hG
    rw [val_corr hG (Y.Φ _ x').s_zero, val_corr hG (Y.Φ _ x).s_zero, val_one, _root_.mul_one] at h0
    have h1 : unitOn (1 : Sˣ) = 1 := map_one _
    exact h0.symm.trans ((congrArg (gm _ y ⊤) h1).trans (map_one _)).symm
  exact Units.ext ((ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of S)).inv).1
    (congrArg Units.val e))

end GlobalTheory.Heat
