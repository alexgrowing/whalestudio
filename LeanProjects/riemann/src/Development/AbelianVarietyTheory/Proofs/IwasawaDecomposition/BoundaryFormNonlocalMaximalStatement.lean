import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BoundaryFormNonlocalMaximal
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PullbackModelArcPeriod
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FormallyUnramifiedUniformization
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.boundary_form_nonlocal_maximal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E)
    (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t),
    IsCN R → P.TorsionIso →
    ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], CDvr V → ∀ ϖ : V, Irreducible ϖ →
    ∀ ψ : R →+* V, Function.Injective ψ → ¬ (∀ r ∈ maximalIdeal R, ψ r ∈ maximalIdeal V) →
    ∀ be ∈ levelForms H 1 P.D.toPre.X, FormAt P.D.toPre ψ ϖ be →
    ∀ (T : CDVR) (f : V →+* T.V), Function.Injective f → IsLocalHom f →
    ∀ u : SAB H (Sp T.V), SABMap u t (spMap f ≫ spMap ψ) → ∀ (P' : PELUnif (maximalIdeal T.V) u) (ϖ' : T.V),
    Irreducible ϖ' → ∀ be' ∈ levelForms H 1 P'.D.toPre.X, IsMonomial P'.D.toPre ![ϖ'] ![be'] →
    ∃ (r : P.D.toPre.X →ₗ[𝓞 E] P'.D.toPre.X) (e : ℕ), Function.Surjective r ∧ Associated (f ϖ) (ϖ' ^ e) ∧
      ∀ a b, be' (r a) (r b) = e * be a b := by
  first | exact @GlobalTheory.TraitQuotForm.main | exact GlobalTheory.TraitQuotForm.main | (intros; apply GlobalTheory.TraitQuotForm.main <;> assumption)
