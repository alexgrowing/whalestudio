import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RealAt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ScalInvFrame
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChangedFrameRationalUnitaryStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PosTieAt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SourceScalarLatticeTupleConstantStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.StepDeterminantConstantUnitIndependentStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SiteSystemRanksEqDatumRanks
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RkLe
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EquivFrameBTheta
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries GlobalTheory.TwV GlobalTheory.TwV.DelB GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.TwV.DelA.unit_mul_scal_eq_scT : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => S.Pos → ∀ ι : ℂ →+* ℂ_[D.what₂.places.resChar w], (∀ z : TaylorLogMetric.Qbar, ι z = S.lam z) → letI := wittFractionAlgebraCp (D.what₂.places.resChar w); letI := algKfC S.E.toCEmb; ∀ (d : Dec J std) j (hj : j + 1 ≤ D.R.m) (La : (sysS H X std).Lt j) (La' : (sysS H X std).Lt (j + 1)), cKs S ι j hj La.1 La'.1 * (Formalism.L2.G.Pend.cA (sysS H X std) ℂ_[D.what₂.places.resChar w] j (BOf d.fd2 j La) * sO d ι j La) * ι (d.uS S j La) * ι (d.uT S j La') = scT d S ι j La'.1 La'.2) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hpos ι hι
  letI := wittFractionAlgebraCp (D.what₂.places.resChar w)
  letI := algKfC S.E.toCEmb
  have hps := GlobalTheory.TwV.DelA.posTie_at S hpos ι hι
  intro d j hj La La'
  have hr := GlobalTheory.TwV.DelB.sysS_ranks S
  have hfr := GlobalTheory.T.changedFrame_rational_unitary S d j (Nat.le_of_succ_le hj) (hr.2.2.1 j) La
  have hsc := GlobalTheory.T.sourceScalar_latticeTuple_constant S d j hj ⟨La'.1⟩ La
  have hun := (GlobalTheory.T.stepDeterminantConstant_unit_independent S hpos ι hι j hj La.1 La'.1).2.1
  have hcA := GlobalTheory.TwV.DelA.scal_inv_frame (sysS H X std) D (hT.gat_pos u w hg) ℂ_[D.what₂.places.resChar w] ι (J.rho std) hps.1 d.fd2 j La (hr.2.2.1 j) (mM d j (Nat.le_of_succ_le hj) La) hfr.1 hfr.2.1
  have key : cA (sysS H X std) ℂ_[D.what₂.places.resChar w] j (BOf d.fd2 j La) * sO d ι j La * ι (d.uS S j La) =
      ι (kS J j (Nat.le_of_succ_le hj) La.1 * cOp (sysS H X std) D (hT.gat_pos u w hg) j (t.O u μ).dgen) := by
    rw [hcA, sO, dif_pos (Nat.le_of_succ_le hj), ← map_mul, ← map_mul, ← hsc]
    congr 1
    unfold dPow
    ring
  rw [mul_assoc (cKs S ι j hj La.1 La'.1), key]
  unfold cKs scT
  rw [dif_pos hj, map_mul ι (kT J j hj La'.1), map_inv₀, map_mul ι (d.uT S j La')]
  have hy : ι (kS J j (Nat.le_of_succ_le hj) La.1 * cOp (sysS H X std) D (hT.gat_pos u w hg) j (t.O u μ).dgen) ≠ 0 := hun
  field_simp
