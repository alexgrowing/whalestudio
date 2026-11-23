import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BoundaryFormCompleteExtension
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PullbackModelArcPeriod
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FormallyUnramifiedUniformization
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.boundary_form_complete_extension : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E)
    (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t),
    IsCN R → P.TorsionIso →
    ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], CDvr V →
    ∀ ψ : R →+* V, Function.Injective ψ → ¬ (∀ r ∈ maximalIdeal R, ψ r ∈ maximalIdeal V) →
    ∀ (T : CDVR) (f : V →+* T.V), Function.Injective f → IsLocalHom f →
    ∀ u : SAB H (Sp T.V), SABMap u t (spMap f ≫ spMap ψ) → ∀ (P' : PELUnif (maximalIdeal T.V) u),
    ∃ r : P.D.toPre.X →ₗ[𝓞 E] P'.D.toPre.X, Function.Surjective r ∧
      ∀ y, ∃ (a : R) (b : T.V), PsiCoord P.D.toPre y a ∧ PsiCoord P'.D.toPre (r y) b ∧ Associated (f (ψ a)) b := by
  first | exact @GlobalTheory.TraitCharRestrict.main | exact GlobalTheory.TraitCharRestrict.main | (intros; apply GlobalTheory.TraitCharRestrict.main <;> assumption)
