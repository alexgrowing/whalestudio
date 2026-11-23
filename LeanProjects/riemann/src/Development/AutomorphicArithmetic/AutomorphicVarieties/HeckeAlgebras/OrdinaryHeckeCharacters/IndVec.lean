import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.Distinct
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Brauer
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsFun

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V UpperTheory.V.Hi

theorem UpperTheory.V.Hi.indVec :
    ∀ {G W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup W] [Module ℂ W]
        (H K : Subgroup G) (σ : Representation ℂ H W), IsOpen (K : Set G) → ∀ w : W, (∀ h : H, (h : G) ∈ K → σ h w = w) →
        ∃ f : GlobalTheory.PRep.smoothPart (GlobalTheory.PRep.ind H σ), f.1.1 1 = w ∧ f ∈ fixd (GlobalTheory.PRep.smInd H σ) K :=
  _root_.UpperTheory.Reformulated.B.Gr28.indVec
