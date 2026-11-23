import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalModelWithPresentation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatHalfSt
open CategoryTheory Limits AlgebraicGeometry IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.LocM GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains GlobalTheory.BundleChernComparison GlobalTheory.ChainPts
open GlobalTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_normal_model_with_presentation : GlobalTheory.CovTop.Hypotheses2 → GlobalTheory.CovHt.HypothesesH → GlobalTheory.Published.PrismaticDieudonnePerfd → GlobalTheory.GroupBplus.GroupAllSt →
  GlobalTheory.BundleChernComparison.AtAll fun D O p _ W hW _ z =>
    haveI := isDiscreteValuationRing_V z.Z.i.c (Fact.out : p.Prime) hW
    ∀ c : (nmodel z.Z).Comp, ∃ (B₁ : Vert.Model (z.Z.i.c.V W)) (f₁ : Vert.Model.Hom B₁ ((nmodel z.Z).comp c)),
      GlobalTheory.IsNormalScheme B₁.X ∧ f₁.relDim = 0 ∧ ∃ (oo : EPres B₁ (𝓞 D.host.E)) (π : Γ(B₁.X, ⊤)) (u : oo.E ⟶ oo.E'),
        IsRootOfP p π (p - 1) ∧ u ≫ oo.ψ = smulA _ π ∧
          IsEqLatPres z.Z (f₁.f ≫ (nmodel z.Z).compι c) (fun k => xAll O.S k.rev) true oo := by
  first | exact @GlobalTheory.OmegaHT.omega_half | exact GlobalTheory.OmegaHT.omega_half | (intros; apply GlobalTheory.OmegaHT.omega_half <;> assumption)
