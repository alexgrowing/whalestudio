import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPointOpenLocalization
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
theorem _root_.GlobalTheory.T.finite_free_local_chart : ∀ (R : Type) [CommRing R] (q : PrimeSpectrum R) (T : Scheme.{0}) (π : T ⟶ Sp R)
    [LocallyOfFinitePresentation π] [QuasiCompact π] [QuasiSeparated π]
    (C' : Type) [CommRing C'] [Algebra (Localization.AtPrime q.asIdeal) C']
    [Module.Finite (Localization.AtPrime q.asIdeal) C'] [Module.Free (Localization.AtPrime q.asIdeal) C']
    (U' : (pullback π (spMap (algebraMap R (Localization.AtPrime q.asIdeal)))).Opens) (e' : Sp C' ≅ U'.toScheme),
    e'.hom ≫ U'.ι ≫ pullback.snd π (spMap (algebraMap R (Localization.AtPrime q.asIdeal))) =
      spMap (algebraMap (Localization.AtPrime q.asIdeal) C') →
    (∀ t, pullback.snd π (spMap (algebraMap R (Localization.AtPrime q.asIdeal))) t =
      IsLocalRing.closedPoint (Localization.AtPrime q.asIdeal) → t ∈ U') →
    ∃ (r : R) (_ : r ∉ q.asIdeal) (C : Type) (_ : CommRing C) (_ : Algebra R C) (_ : Algebra (Localization.Away r) C)
      (_ : IsScalarTower R (Localization.Away r) C) (_ : Module.Finite (Localization.Away r) C)
      (_ : Module.Free (Localization.Away r) C) (U : T.Opens) (e : Sp C ≅ U.toScheme),
      e.hom ≫ U.ι ≫ π = spMap (algebraMap R C) ∧ ∀ t : T, π t = q → t ∈ U := by
  first | exact @GlobalTheory.exists_finite_free_chart_away_of_atPrime | exact GlobalTheory.exists_finite_free_chart_away_of_atPrime | (intros; apply GlobalTheory.exists_finite_free_chart_away_of_atPrime <;> assumption)
