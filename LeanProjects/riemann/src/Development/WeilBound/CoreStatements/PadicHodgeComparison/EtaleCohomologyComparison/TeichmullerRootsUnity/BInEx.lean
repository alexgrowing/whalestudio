import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.TeichmullerRootsUnity.TUnit
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.FirstChernCompatibleL
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AtlasGroupActions.AtlasOf

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GroundTheory.PAdicHodge CrystallineSemistableComparison

namespace CrystallineSemistableComparison.crystallineComparison

theorem bInEx : BInEx := by
  intro l _ K _ M hM j
  obtain ⟨d, hA⟩ := GlueB'.atlas_of hM
  obtain ⟨N, hN⟩ := B.main l d j
  obtain ⟨v, -, e⟩ := ACris.exists_periodT_eq_mu_mul_unit (K := ℂ_[l]) (p := l) (untilt_epsilon (p := l))
    untilt_frobeniusEquiv_symm_epsilon_ne_one
  have ht : tA l = (GlueBE.eps l).μ * v := by rw [GlueBE.eps_μ]; exact e
  have hC := B.compat l
  have hup := fun n : ℕ =>
    (hN (B.schFn M.p) (okToOC l K) (GlueBE.eps l) hA.some n).1 true
  refine ⟨⟨2 * N, fun y => ?_, fun x hx => ?_⟩, fun x n => ?_, fun g x n => ?_⟩
  · obtain ⟨x, hx⟩ := GlueBL.lim_surj (GlueB'.βS hC (B.schFn M.p) (okToOC l K) true j) _ v (tA l) N ht hup y
    exact ⟨x, fun n => congrArg (fun z => z.1 n) hx⟩
  · exact GlueBL.lim_inj (GlueB'.βS hC (B.schFn M.p) (okToOC l K) true j) _ v (tA l) N ht hup x (Subtype.ext (funext hx))
  · exact hC.phi (B.schFn M.p) (okToOC l K) n j _
  · exact hC.gal (B.schFn M.p) (okToOC l K) (IntermediateField.fixingSubgroupEquiv K g) (galOC_okToOC _) true n j _

end CrystallineSemistableComparison.crystallineComparison

end
