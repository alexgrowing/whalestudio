import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsCombFieldExtension
import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.is_comb_field_extension : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (F : Type) [Field F] (x : Sp F ⟶ S) (F' : Type) [Field F'] (f : F →+* F') (x' : Sp F' ⟶ S), spMap f ≫ x = x' → ∀ (n : ℕ) (v : Fin n → (epsAt x ⟶ G)) (cf : Fin n → F) (w : epsAt x ⟶ G) (v' : Fin n → (epsAt x' ⟶ G)) (w' : epsAt x' ⟶ G), (∀ i, (v' i).left = spMap (dualMap f) ≫ (v i).left) → w'.left = spMap (dualMap f) ≫ w.left → IsComb cf v w → IsComb (fun i => f (cf i)) v' w' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.CombBase.isComb_base | exact GlobalTheory.CompanionTheory.Ar.CombBase.isComb_base | (intros; apply GlobalTheory.CompanionTheory.Ar.CombBase.isComb_base <;> assumption)
