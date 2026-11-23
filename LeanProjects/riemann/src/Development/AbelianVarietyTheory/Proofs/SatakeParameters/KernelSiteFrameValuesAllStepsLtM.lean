import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RealAt
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RkLe
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EquivFrameBTheta
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.OperatorOnFrameAndClassSummandPolynomialStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.OperatorPolynomialCoeffsWeightExtendedByZero
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeTupleReadingEqOfRealisingPolynomialStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnitMulSourceScalarEqNextLevelScalarStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MovedFormsOperatorDegreesAtKernelSourceStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TransportedFramePolynomialComplexValuesAtPointStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.StepDeterminantConstantUnitIndependentStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsAdelicLatticeTupleDecompositionStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelSiteContractionIdentityOperatorHalfStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SiteFramesAndChangedFramesInvertible
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SiteSystemRanksEqDatumRanks

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries GlobalTheory.TwV GlobalTheory.TwV.DelB GlobalTheory.TwV.DelA

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.DelA

theorem tieDel_all_steps : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => J.Dict std → S.Pair → S.Pos → S.Law → ∀ j < D.R.m, S.Del j) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hDict hPair hPos hLaw j hj ι hι
  letI := wittFractionAlgebraCp (D.what₂.places.resChar w)
  letI := algKfC S.E.toCEmb
  have hj1 : j + 1 ≤ D.R.m := hj
  by_cases hne : Nonempty (Lv.comp j) ∧ Nonempty (Lv.comp (j + 1))
  swap
  · refine ⟨1, norm_one, ?_⟩
    intro La _ x c' L' _
    exact absurd ⟨⟨La.1⟩, ⟨c'⟩⟩ hne
  obtain ⟨⟨a⟩, ⟨a'⟩⟩ := hne
  obtain ⟨hn1, -, hsame⟩ := GlobalTheory.T.stepDeterminantConstant_unit_independent S hPos ι hι j hj1 a a'
  set cK := cKs S ι j hj1 a a' with hcK
  refine ⟨cK, hn1, ?_⟩
  obtain ⟨-, -, hrk, hRT⟩ := GlobalTheory.TwV.DelB.sysS_ranks S
  have hN := hRT j
  have h1 : ((sysS H X std).Pj (j + 1)).m + 1 = D.R.N (j + 1) := hrk (j + 1)
  obtain ⟨d0⟩ := GlobalTheory.T.exists_adelic_latticeTuple_decomposition S hDict
  intro La hLa x c' L' hL'

  have hQ : K2.SharpQ t ex.tw u μ j x (K2.qOf t ex.tw u μ j x) := by
    have hex := J.sharp j hj x
    unfold K2.qOf
    rw [dif_pos hex]
    exact Classical.choose_spec hex
  set cc := clsAt X H j La.1 La.2 with hcc
  set κ := clsAt X H (j + 1) c' L' with hκ
  set Q := K2.qOf t ex.tw u μ j x with hQdef
  set P : MvPolynomial (GL3Theta.FrV D (D.R.N (j + 1))) ℂ :=
    ((((GL3Theta.rhoOf D (t.O u μ).mt j ((t.O u μ).dt j cc) : ℂˣ) : ℂ) *
          ((GL3Theta.rhoOf' D (t.O u μ).mt j ((t.O u μ).dt (j + 1) κ) : ℂˣ) : ℂ)) •
          framePol D (t.O u μ).dgen (Q cc) ((t.rd u μ).Th t.seam t.amb j cc κ)) with hP
  have hPw : P ∈ WtPol ℂ (extNu (D.R.N (j + 1)) (Formalism.L2.Ker.nuT D u j)) :=
    Submodule.smul_mem _ _ ((wt_polDY_framePol D (rk_le _ D hN) (t.O u μ).dgen _ (Q cc) (hQ.1 cc)).2 _)
  set φ := K2.entRec t ex.tw u μ j cc x with hφ
  have hφκ : ∀ y, φ κ y = (∏ τ, (D.chTw u μ).de (j + 1) y τ ^ (D.chTw u μ).sDiv j τ)⁻¹ * frPoly (t.O u μ) (j + 1) P y := by
    intro y
    have e := (GlobalTheory.T.operatorOnFrame_and_classSummand_polynomial).2 D L hT Gi Gl Kc Dx cX ex t u μ j cc (Q cc) κ y
    have e2 : φ κ y = entQ t u μ j cc (Q cc) κ y := rfl
    rw [e2, e, hP, map_smul, Pi.smul_apply, smul_eq_mul]
    ring

  have hR : ∀ d : Dec J std, ∃ V : XR ((sysS H X std).Pj (j + 1)) ℂ, RealAt d (j + 1) hj1 h1 (c', L') φ V ∧
      MvPolynomial.map ι V = cK • S.Y.DelF j ((kaAt X H hT).cmp j x La.1 La.2) (srOf S.Y j La (c', L')) := by
    intro d
    obtain ⟨V, hV, hmap⟩ := GlobalTheory.T.transportedFramePolynomial_complex_values_at_point S hPos ι hι d j hj1 h1 (c', L') φ P hPw hφκ
    refine ⟨V, hV, ?_⟩
    rw [hmap]
    obtain ⟨hMove, hOp, hDeg⟩ := GlobalTheory.T.movedForms_operator_degrees_at_kernelSource S hDict hPos ι hι d j hj ⟨a'⟩ hN
    have hEq := GlobalTheory.FrameB.equiv_frame_b S.Y d.fd2 (ltC S.g S.hLT) (GlobalTheory.FrameB.ltC_ne S.hLT)
      ((GlobalTheory.TwV.DelB.frames_invertible S).2 d) j
    have hsc : ∀ (La : (sysS H X std).Lt j) (La' : (sysS H X std).Lt (j + 1)), ((sysS H X std).Pj j).IsLatTup La.2 →
        ((sysS H X std).Pj (j + 1)).IsLatTup La'.2 →
        cK * (Formalism.L2.G.Pend.cA (sysS H X std) ℂ_[D.what₂.places.resChar w] j (BOf d.fd2 j La) * sO d ι j La) *
          ι (d.uS S j La) * ι (d.uT S j La') = scT d S ι j La'.1 La'.2 := by
      intro La La' _ _
      have e := GlobalTheory.T.unit_mul_sourceScalar_eq_nextLevelScalar S hPos ι hι d j hj1 La La'
      rw [hsame] at e
      exact e
    have hDel := GlobalTheory.T.kernelSite_contractionIdentity_operatorHalf S hDict hPair hPos hLaw d ι hι (fun j => phi0 (sysS H X std) D (hT.gat_pos u w hg) ι j)
      (fun j c' L' => GlobalTheory.FrameB.tauV ℂ_[D.what₂.places.resChar w] d.fd2 (ltC S.g S.hLT) j (c', L'))
      (fun j c' L' => scT d S ι j c' L') (sO d ι) (gmS d) j hj cK hN hMove hOp hDeg hEq hsc
    have := hDel La hLa x Q hQ c' L' hL'
    exact this
  obtain ⟨V0, hV0, hm0⟩ := hR d0
  have hall : ∀ d : Dec J std, RealAt d (j + 1) hj1 h1 (c', L') φ V0 := by
    intro d
    obtain ⟨V, hV, hm⟩ := hR d
    have : V = V0 := MvPolynomial.map_injective ι ι.injective (hm.trans hm0.symm)
    exact this ▸ hV
  have hrd := GlobalTheory.T.latticeTupleReading_eq_of_realising_polynomial S hDict ι j hj1 h1 (c', L') hL' φ V0 hall
  exact hrd.trans hm0

end GlobalTheory.TwV.DelA
