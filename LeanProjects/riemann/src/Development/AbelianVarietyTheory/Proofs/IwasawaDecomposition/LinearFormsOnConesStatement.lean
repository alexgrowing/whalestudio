import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LinearFormsOnCones
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linear_forms_on_cones : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : Datum H) (l : Level H)
    (Xo : Moduli D l) (c : Coeff l) (Z : GMod Xo c)
    (Cn : ∀ (X : Type) [AddCommGroup X] [Module (NumberField.RingOfIntegers E) X] [Module.Finite (NumberField.RingOfIntegers E) X] (m : ℕ),
      (Fin m → LinearMap.BilinForm ℤ X) → Prop) (ψ : GlobalTheory.LocM.InvFun (NumberField.RingOfIntegers E)),
    (∀ (X : Type) [AddCommGroup X] [Module (NumberField.RingOfIntegers E) X] [Module.Finite (NumberField.RingOfIntegers E) X]
        [Module.Projective (NumberField.RingOfIntegers E) X], Module.finrank (NumberField.RingOfIntegers E) X ≤ min D.p D.q →
      ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), Cn X m γ →
        ∃ ℓ : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ, ∀ be : LinearMap.BilinForm ℤ X, (∀ y z, be y z = be z y) →
          (∃ c : Fin m → ℝ, (∀ i, 0 ≤ c i) ∧ GlobalTheory.PolFan.toReal be = ∑ i, c i • GlobalTheory.PolFan.toReal (γ i)) →
            ψ.evalZ be = ℓ be ∧ 0 ≤ ℓ be) →
    HasCones Cn Z → ∃ BD, IsPhiDiv ψ Z BD := by
  first | exact @GlobalTheory.TorRef.exists_isPhiDiv_of_cones | exact GlobalTheory.TorRef.exists_isPhiDiv_of_cones | (intros; apply GlobalTheory.TorRef.exists_isPhiDiv_of_cones <;> assumption)
