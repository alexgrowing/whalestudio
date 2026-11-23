import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BoundaryFormNonlocalDvr
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.boundary_form_nonlocal_dvr : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R]
    [IsLocalRing R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t), IsCN R → P.TorsionIso →
    ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], CDvr V → ∀ ϖ : V, Irreducible ϖ →
    ∀ ψ : R →+* V, Function.Injective ψ → ¬ IsLocalHom ψ →
    ∀ be ∈ levelForms H 1 P.D.toPre.X, FormAt P.D.toPre ψ ϖ be →
    ∃ (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsLocalRing V') (f : V →+* V'),
      CDvr V' ∧ Function.Injective f ∧ IsLocalHom f ∧ Irreducible (f ϖ) ∧
      ∃ (t' : SAB H (Sp V')) (_ : SABMap t' t (spMap (f.comp ψ))) (P' : PELUnif (maximalIdeal V') t')
        (be' : LinearMap.BilinForm ℤ P'.D.toPre.X) (ρ : P.D.toPre.X →ₗ[𝓞 E] P'.D.toPre.X),
        be' ∈ levelForms H 1 P'.D.toPre.X ∧ Function.Surjective ρ ∧ (∀ a b, be' (ρ a) (ρ b) = be a b) ∧
        IsMonomial P'.D.toPre ![f ϖ] ![be'] := by
  first | exact @GlobalTheory.TraitQuot.main | exact GlobalTheory.TraitQuot.main | (intros; apply GlobalTheory.TraitQuot.main <;> assumption)
