import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsCoreLat
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.EisRegularAtOfEisPoleLE
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqExistsIffDsExists
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PolarisationTwistLatticeSelfDualSameStabilisersStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CongruenceSubgroupLevelMemberClausesStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SelfDualLatticeChangeOfLatticeLawsStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.WittIdxOfParallelSig
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
open scoped TensorProduct nonZeroDivisors ComplexConjugate

namespace GlobalTheory.CoreOnto.StageProof

theorem under_mem_of_modul_le {D : D7} {T : Type} {L : LevCh D T} (P : GlobalTheory.ChiGrid.Places L) (sc : Consts)
    (Q : HeightOneSpectrum (𝓞 D.host.E)) (h : P.modul sc ≤ Q.asIdeal) : Q.under (𝓞 D.host.F) ∈ P.S0 := by
  unfold GlobalTheory.ChiGrid.Places.modul at h
  obtain ⟨v, hv, hle⟩ := (Ideal.IsPrime.prod_le Q.isPrime).1 h
  have hd : 0 < P.depth sc v ∨ P.depth sc v = 0 := by omega
  rcases hd with hd | hd
  · have h1 : (P.w v).asIdeal ≤ Q.asIdeal := Q.isPrime.le_of_pow_le hle
    have h2 : (P.w v).asIdeal = Q.asIdeal := (P.w v).isMaximal.eq_of_le Q.isPrime.ne_top h1
    have h3 : P.w v = Q := HeightOneSpectrum.ext h2
    rw [← h3, P.w_over v hv]
    exact hv
  · rw [hd, pow_zero, Ideal.one_eq_top, top_le_iff] at hle
    exact absurd hle Q.isPrime.ne_top

theorem stageOK : StageOK := by
  intro D hQ T L μ0 hL sc G W Mv hM i hi
  have hV := node_isV G hL (X := .core i) hi
  have hsd : IsSelfDualC (G.V (.core i)) (G.Λ (.core i)) := hV.sd
  obtain ⟨hsd', hstab, hcong⟩ := GlobalTheory.T.polarisationTwist_lattice_selfDual_same_stabilisers D (G.V (.core i)) (G.Λ (.core i)) hsd i
  have hRL := GlobalTheory.T.selfDualLattice_changeOfLattice_laws D
  refine ⟨?_, ?_⟩
  · obtain ⟨r, hr⟩ := hRL.1 _ _ hsd'
    exact ⟨r, hr⟩
  · intro r hr v Mo
    have hsdS : IsSelfDualC (gridStage G v i r Mo).V (gridStage G v i r Mo).Λ := by
      show IsSelfDualC r.sp (GlobalTheory.AdelicU.frameLat r.sp)
      rw [hr]; exact hsd'
    have hJ : (gridStage G v i r Mo).J = Lev.levA (gridStage G v i r Mo).V
        (congLev D.sp.cm (gridStage G v i r Mo).V.gram (gridStage G v i r Mo).Λ G.modul) := by
      show lev G (.core i) = Lev.levA r.sp (congLev D.sp.cm r.sp.gram (GlobalTheory.AdelicU.frameLat r.sp) G.modul)
      rw [hr]
      exact (congrArg (Lev.levA (G.V (.core i))) (hcong G.modul)).symm
    obtain ⟨hfin, hopen, hst, hoff, hsph, hsplit⟩ := GlobalTheory.T.congruenceSubgroup_level_member_clauses D (gridCom W) (gridStage G v i r Mo) G.modul
      (GlobalTheory.ChiGrid.Places.modul_ne_bot _ _) (fun Q hQ' => under_mem_of_modul_le G.pl sc Q hQ') hsdS hJ
    have hw : GlobalTheory.Cusp.wittIndex r.sp = GlobalTheory.Cusp.wittIndex (G.V (.core i)) :=
      ((hRL.2.1 (G.V (.core i)) r W.θ _ Mo Set.univ).2.2.2).1
    have hwle : GlobalTheory.Cusp.wittIndex (G.V (.core i)) ≤ Node.neg D.R.m (.core i) := by
      haveI : IsCMField D.host.E := D.host.isCMField_hostE
      have hpar := GlobalTheory.IndefiniteRowSideFullHecke.WittIndexParallel.parallelSig_of_sigOK hV.sigOK (fun τ => hV.sig τ)
      obtain ⟨U, hU, e⟩ := (GlobalTheory.Cusp.isGreatest_wittIndex ((G.V (.core i)) : HSpace D.host.E)).1
      obtain ⟨τ⟩ : Nonempty (D.host.E →+* ℂ) := inferInstance
      have h1 := GlobalTheory.ParallelWitt.finrank_le (E := D.host.E) (G.V (.core i)) τ (hpar τ) U (fun x hx y hy => by
        have := hU hy
        simp only [GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.perp, Submodule.mem_iInf, LinearMap.mem_ker] at this
        exact this x hx)
      omega
    exact {
      rank := hV.rank
      sigOK := hV.sigOK
      witt := by
        rw [show (gridStage G v i r Mo).V = r.sp from rfl, hw]
        refine lt_of_le_of_lt hwle ?_
        have h3 := D.R.three_m_lt_t
        have h4 := D.R.rank_add_five_le
        have h5 := D.R.m_add_three_le_k
        simp only [Node.neg, gridCom, sLen]
        unfold Ranks.r
        omega
      selfDual := hsdS
      fin := hfin
      isOpen := hopen
      stab := hst
      off := hoff
      sph := hsph
      split := hsplit
      haar := (v i).haar
      fund := (v i).fund }

end GlobalTheory.CoreOnto.StageProof
