import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BadPrimeMemExceptionalSet
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Realised
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Links2OfRowsStatement

set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie GlobalTheory.BigOn GlobalTheory.BigOn.Exp
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.BigOn.Exp
theorem ratHyp0_at_point_alt : ∀ {eps : ℝ} (Fm : FamP eps) (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x) (p : Pt Fm x hx i), p.PointConditions' → More p →
  ∀ t : (Fm.D x i).ntw.Tw, (Fm.D x i).ntw.NonzeroIndexPlace t →
  (∀ P : Pl (Fm.D x i).host.E, (((Fm.D x i).host.QS * (Fm.D x i).host.q * Ideal.absNorm (Fm.D x i).host.ccK * ((Fm.D x i).host.g 0 * (Fm.D x i).host.g 1 *
    (Fm.D x i).host.pde * (Fm.D x i).host.pde') : ℕ) : 𝓞 (Fm.D x i).host.E) ∈ P.asIdeal → P ∈ (Fm.D x i).ntw.S0 t) →
  ∀ j : Fin (Fm.D x i).R.m, RatHyp0 p.T p.R (F2 p) p.κ p.v₀ p.O t j := by
  intro eps Fm x hx i p hp hM t ht hlow j
  obtain ⟨hc, -, hu, -⟩ := _root_.GlobalTheory.T.links2_of_single_index_twisted _ _ _ _ _ _ _ _ _ _ p hp hM.1
  have hTie : TieIn p.T p.R.toRealDat p.κ p.v₀ :=
    ⟨p.fw.laws, p.fw.alg_eq, p.fw.kap, p.fw.hv₀, p.fw.chiR, p.fw.x0⟩
  exact
    { size := (Fm.parT x hx i).nV_ge
      host := p.host
      std := GlobalTheory.StdFrame.vStd_of_orthonormal_span _ j (p.stdV j)
      laws := p.fw.laws
      core :=
        { lev := hc.lev
          grp := ⟨hc.grp.red_R, hc.grp.red_L, hc.grp.levels, hc.grp.record, hc.grp.chiW⟩
          fam := ⟨hc.fam.tie, hc.fam.Sb, hc.fam.roots, hc.fam.pl_onto, hc.fam.degR, hc.fam.degL, hc.fam.muVal, hc.fam.etaVal⟩
          models := ⟨hc.models.inf, hc.models.vpos, hc.models.cX, hc.models.cV, hc.models.prX, hc.models.HX, hc.models.HV,
            hc.models.HE, hc.models.HW, hc.models.gE, hc.models.gW, hc.models.jX, hc.models.jV, hc.models.νY, hc.models.νY',
            hc.models.ν0, hc.models.νX, hc.models.νV, hc.models.νW, hc.models.BV, hc.models.order⟩
          chain := ⟨hc.chain.ωY, hc.chain.ωX, hc.chain.vY, hc.chain.vX, hc.chain.ptY, hc.chain.ptX, hc.chain.ItY, hc.chain.ItX,
            hc.chain.ioY, hc.chain.ioX, hc.chain.Th⟩
          thP := ⟨hc.thP.ωP, hc.thP.vP, hc.thP.pt_theta, hc.thP.ioP, hc.thP.thF_mem, hc.thP.thF, hc.thP.thG⟩ }
      unif := hu
      fw := ⟨p.fw⟩
      tieIn := hTie
      io := hp.ioExt
      guard := p.qGuard
      fin := GlobalTheory.BigOn.Check.finite_tuples_of_indefiniteSidePoint p
      pins := p.pins j
      phase := p.phase j hu
      galois := (Fm.ties x i).baseField_isGalois
      small := hM.2.2.small
      inUse := ht
      low := hlow }
end GlobalTheory.BigOn.Exp
end
