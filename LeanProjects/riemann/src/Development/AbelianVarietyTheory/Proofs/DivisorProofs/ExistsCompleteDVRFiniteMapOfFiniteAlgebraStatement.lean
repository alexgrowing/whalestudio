import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompleteDVRFiniteMapOfFiniteAlgebra
import Development.AbelianVarietyTheory.Definitions.Divisors.NotOrdGeOfNotMem
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSiegPull
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_completeDVR_finite_map_of_finiteAlgebra : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.LN.CDvr V →
    ∀ (R₁ : Type) [CommRing R₁] [Algebra (FractionRing V) R₁], Module.Finite (FractionRing V) R₁ → Nontrivial R₁ →
      ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsLocalRing W) (f : V →+* W) (ψ : R₁ →+* FractionRing W),
        GlobalTheory.LN.CDvr W ∧ Function.Injective f ∧ IsLocalHom f ∧ f.Finite ∧
        ∀ a, ψ (algebraMap (FractionRing V) R₁ (algebraMap V _ a)) = algebraMap W _ (f a) := by
  first | exact @GlobalTheory.CdvrFiniteAlgebra.exists_cdvr_map_of_finite | exact GlobalTheory.CdvrFiniteAlgebra.exists_cdvr_map_of_finite | (intros; apply GlobalTheory.CdvrFiniteAlgebra.exists_cdvr_map_of_finite <;> assumption)
