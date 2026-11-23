import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MetaplecticLowRank.LowC
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsFixedMkEqOfCommute
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FixedInjSmooth
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsOpenGx
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCompactParahoricSubgroupStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParahoricLeviUnipotentLowerStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CentralTorusContractsLowerStatement

noncomputable section

namespace GlobalTheory.CompanionTheory.MoyPrasadTop

open PositivityTheory.LowerBoundConstant GlobalTheory GlobalTheory.Published GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead Topology

theorem moyPrasadJacquetIso : GlobalTheory.Published.MoyPrasadJacquetIso := by
  intro k _ _ _ _ n s d e V _ _ π hπ
  refine ⟨mapsTo_fixed_jacU e π _, ?_, ?_⟩
  · intro v hv w hw h
    have h0 : (Submodule.Quotient.mk (v - w) : Jacquet π (unipRad k e)) = 0 := by
      rw [Submodule.Quotient.mk_sub]
      exact sub_eq_zero.2 h
    exact sub_eq_zero.1 (GlobalTheory.CompanionTheory.DepthZeroJac.fixed_inj_smooth k n s d e V π hπ.1 (v - w) (sub_mem hv hw) h0)
  · intro y hy
    obtain ⟨v, hv, hvy⟩ := GlobalTheory.CompanionTheory.JacquetCentral.exists_fixed_mk_eq_of_commute π hπ (Gx k e) (unipRad k e) (GlobalTheory.CompanionTheory.MoyPrasad.isOpen_Gx k n s d e)
      (GlobalTheory.T.isCompact_parahoric_subgroup k n s d e) (leviEmb k e) (leviEmb_mem_normalizer k e) ((Gx k e).comap (leviEmb k e))
      (fun _ hm => hm) (lowC k e) (GlobalTheory.T.parahoric_levi_unipotent_lower k n s d e)
      (fun U hU => by
        obtain ⟨t, ht, hc⟩ := GlobalTheory.T.central_torus_contracts_lower k n s d e U hU
        exact ⟨t, fun m _ => ht m, hc⟩) y hy
    exact ⟨v, hv, hvy⟩

end GlobalTheory.CompanionTheory.MoyPrasadTop

end
