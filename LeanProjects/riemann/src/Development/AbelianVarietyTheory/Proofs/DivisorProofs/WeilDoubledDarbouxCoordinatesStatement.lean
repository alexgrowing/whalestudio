import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilDoubledDarbouxCoordinates
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsMulVal
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField WithConv
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.PerfdLat GlobalTheory.GroupBplus GlobalTheory.GroupBplus.Aff
open Coalgebra Bialgebra
open GlobalTheory.DeRham (spOver spOver_comp)
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_free_neighbourhood : ∀ (A : Type) [CommRing A] [HenselianLocalRing A] (T : Scheme.{0}) (π : T ⟶ Sp A) [IsSeparated π]
    [LocallyOfFinitePresentation π] [QuasiCompact π] [LocallyQuasiFinite π] [Flat π],
    ∃ (C : Type) (_ : CommRing C) (_ : Algebra A C) (_ : Module.Finite A C) (_ : Module.Free A C) (U : T.Opens)
      (e : Sp C ≅ U.toScheme), e.hom ≫ U.ι ≫ π = spMap (algebraMap A C) ∧
        ∀ t : T, π t = IsLocalRing.closedPoint A → t ∈ U := by
  first | exact @GlobalTheory.exists_finite_free_chart_of_henselian | exact GlobalTheory.exists_finite_free_chart_of_henselian | (intros; apply GlobalTheory.exists_finite_free_chart_of_henselian <;> assumption)
