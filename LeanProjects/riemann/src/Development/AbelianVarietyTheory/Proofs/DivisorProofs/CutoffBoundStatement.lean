import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.QuoIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HostBoundHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedProjectorIdempotentOfGroupAlgebraIdemStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedProjectorOrthogonalOfUnitaryActionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardSmulTwistedProjectorMemIntegralFormsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupIdempotentCoefficientsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowRepresentationPreservesLatticeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowInnerProductInvariantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogGroupOrderBoundStatement

set_option synthInstance.maxHeartbeats 400000

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop

namespace GlobalTheory.CovTop

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem cutAt_of_rows {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D}
    {Kc : Formalism.MainNotions.G.Consts} {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz)
    (hp : p.Rows) (ht : RecTied D L) (i : Fin D.R.m) (PP A : ℝ) (hN : HostNum D L PP A 3) : CutAt p i := by
  obtain ⟨h1, h2, h3, h4⟩ := GlobalTheory.T.group_idempotent_coefficients p hp ht
  have hI := GlobalTheory.T.twistedProjector_idempotent_of_groupAlgebra_idem (p.R.toRealDat.FW i) (fun g => (idemOf p.P.A3.A.X).coeff g) h1
  refine ⟨hI, fun σ x y => ?_, fun x hx => ?_, GlobalTheory.T.log_group_order_bound p hp ht PP A hN⟩
  · exact GlobalTheory.T.twistedProjector_orthogonal_of_unitary_action (p.R.toRealDat.FW i) (fun g => (idemOf p.P.A3.A.X).coeff g) _ hI (GlobalTheory.T.row_inner_product_invariant p hp ht i σ)
      (fun g => h4 _ g) x y
  · exact GlobalTheory.T.card_smul_twistedProjector_mem_integralForms (p.R.toRealDat.FW i) (fun g => (idemOf p.P.A3.A.X).coeff g) h2 h3 (GlobalTheory.T.row_representation_preserves_lattice p hp ht i) _ _ x hx

theorem cut_of_hypotheses (_h : Hypotheses2) : Cut := by
  refine (Sizes.hostN 3).imp fun Fm CH _ h => ?_
  obtain ⟨C, -, x0, hx⟩ := h
  exact ⟨0, le_rfl, x0, fun x hx' hle ι p hp i => cutAt_of_rows p hp.1 hp.2 i _ _ (hx x hx' hle ι p hp i)⟩

end GlobalTheory.CovTop
