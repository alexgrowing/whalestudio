import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsGrpPullbackOfCompatibleRetracts
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NotSymEOfNe
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianDirectFactorOfIdempotentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeLineBundleEighthPowerIsoPowStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianHomExtensionHolds
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isGrpPullback_of_compatible_retracts : ∀ {S S' B : Scheme.{0}} (j : S' ⟶ S) (f : S' ⟶ B) (G : Over S) [GrpObj G] (G' : Over S') [GrpObj G'] (P : Over B) [GrpObj P] (φ : G'.left ⟶ G.left) (ψ : G'.left ⟶ P.left) (hφ : IsGrpPullback G' G j φ) (hψ : IsGrpPullback G' P f ψ) (e : G ⟶ G) (e₀ : P ⟶ P) (e' : G' ⟶ G') (he' : IsMonHom e') (h₁ : e'.left ≫ φ = φ ≫ e.left) (h₂ : e'.left ≫ ψ = ψ ≫ e₀.left) (H : Over S) [GrpObj H] (i : H ⟶ G) (r : G ⟶ H) (hi : IsMonHom i) (hr : IsMonHom r) (hir : i ≫ r = 𝟙 H) (hri : r ≫ i = e) (C : Over B) [GrpObj C] (k : C ⟶ P) (p : P ⟶ C) (hk : IsMonHom k) (hp : IsMonHom p) (hkp : k ≫ p = 𝟙 C) (hpk : p ≫ k = e₀), ∃ (C' : Over S') (_ : GrpObj C') (a : C'.left ⟶ H.left) (b : C'.left ⟶ C.left), IsGrpPullback C' H j a ∧ IsGrpPullback C' C f b := by
  first | exact @GlobalTheory.RetractPullback.exists_isGrpPullback_of_retracts | exact GlobalTheory.RetractPullback.exists_isGrpPullback_of_retracts | (intros; apply GlobalTheory.RetractPullback.exists_isGrpPullback_of_retracts <;> assumption)
