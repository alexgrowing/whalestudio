import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.TamagawaNumberSpecialUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeepExistenceStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeepExistenceStatementStatement

section
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR.Links ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop
namespace GlobalTheory.CovTop.DeepExist
theorem exists_deep_covering_level (hP : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems) : DeepEx := by
  refine Closed.imp (GlobalTheory.CovTop.Sizes.hostN 0) fun Fm CH _ h => ?_
  obtain ⟨C, hC, x0, h⟩ := h
  refine ⟨C, hC, x0, fun x hx hle ι p hp i hi => ?_⟩
  have hN := h x hx hle ι p hp i
  obtain ⟨Y, hY⟩ := GlobalTheory.T.exists_good_cover_over_sized_field hP.p8 (Fm.D x ι) p.T.toCore p.fw.laws.pins ((i : ℕ) + 1) ⟨by omega, i.isLt⟩ hN.split
    hN.cop (expL (Fm.L x ι).sc.L)
  refine ⟨Y, (goodCov_iff p i Y).2 (hY.mono (size_le hN ?_))⟩
  exact RecTied.core_size_le p hp.2 (by linarith [hN.big.2.1])
end GlobalTheory.CovTop.DeepExist
end
end

section
open GlobalTheory.CovTop GlobalTheory.BigTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.covering_deep_level_exists : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → DeepEx := by
  first | exact @_root_.GlobalTheory.CovTop.DeepExist.exists_deep_covering_level | exact _root_.GlobalTheory.CovTop.DeepExist.exists_deep_covering_level | (intros; apply _root_.GlobalTheory.CovTop.DeepExist.exists_deep_covering_level <;> assumption)
end
