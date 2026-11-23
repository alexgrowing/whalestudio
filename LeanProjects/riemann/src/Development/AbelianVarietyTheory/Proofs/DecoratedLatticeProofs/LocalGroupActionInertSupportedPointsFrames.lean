import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SpanRhoTEqTop
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PiEqOfFinPart
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemIntMat

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.InertFrameLoc

set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.InertFrameAct

variable {D : D7} {v : HeightOneSpectrum (𝓞 D.host.F)} {w : HeightOneSpectrum (𝓞 D.host.E)}

theorem compW_eq_toCompl (h : w.under (𝓞 D.host.F) = v) (a : AE D) :
    GlobalTheory.InertHomIdx.compW D w a = toCompl h (GlobalTheory.AdelicU.compFin D.host.F D.host.E v a) := by
  show finAdEquiv D.host.F D.host.E (finPart D a) w = _
  rw [finAdEquiv_apply h, ← GlobalTheory.EmbChart.map_evalV_map_sndA]
  rfl

theorem secW_mul (hw : IsInertAt D.host.F D.host.E v w) (h : w.under (𝓞 D.host.F) = v)
    (z : w.adicCompletion D.host.E) (a : AE D) :
    secW hw h z * a = secW hw h (z * GlobalTheory.InertHomIdx.compW D w a) := by
  show GlobalTheory.EmbChart.tensAt D.host.E v ((InertChart.complEquiv hw h).symm z) * a =
    GlobalTheory.EmbChart.tensAt D.host.E v ((InertChart.complEquiv hw h).symm (z * GlobalTheory.InertHomIdx.compW D w a))
  rw [GlobalTheory.EmbChart.tensAt_mul_right]
  congr 1
  apply (InertChart.complEquiv hw h).injective
  rw [map_mul, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply, compW_eq_toCompl h]
  rfl

theorem mul_secW (hw : IsInertAt D.host.F D.host.E v w) (h : w.under (𝓞 D.host.F) = v)
    (z : w.adicCompletion D.host.E) (a : AE D) :
    a * secW hw h z = secW hw h (GlobalTheory.InertHomIdx.compW D w a * z) := by
  rw [mul_comm, secW_mul, mul_comm]

theorem mul_map_secW (hw : IsInertAt D.host.F D.host.E v w) (h : w.under (𝓞 D.host.F) = v) {m n p : ℕ}
    (A : Matrix (Fin m) (Fin n) (AE D)) (M : Matrix (Fin n) (Fin p) (w.adicCompletion D.host.E)) :
    A * M.map (secW hw h) = (A.map (GlobalTheory.InertHomIdx.compW D w) * M).map (secW hw h) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.map_apply, map_sum, mul_secW]

theorem map_secW_mul (hw : IsInertAt D.host.F D.host.E v w) (h : w.under (𝓞 D.host.F) = v) {m n p : ℕ}
    (M : Matrix (Fin m) (Fin n) (w.adicCompletion D.host.E)) (B : Matrix (Fin n) (Fin p) (AE D)) :
    M.map (secW hw h) * B = (M * B.map (GlobalTheory.InertHomIdx.compW D w)).map (secW hw h) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.map_apply, map_sum, secW_mul]

end GlobalTheory.InertFrameAct

open GlobalTheory.InertFrameAct in

theorem GlobalTheory.InertFrameAct.actO_uPt : ∀ (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : IsInertAt D.host.F D.host.E v w) (h : w.under (𝓞 D.host.F) = v) (S T : HSp D) (k : w.adicCompletion D.host.E) (aS : GL (Fin S.rank) (w.adicCompletion D.host.E)) (aT : GL (Fin T.rank) (w.adicCompletion D.host.E)) (gS : Gv S v) (gT : Gv T v) (x : Matrix (Fin T.rank) (Fin S.rank) (w.adicCompletion D.host.E)), actO S T (embV S v gS) (embV T v gT) (uPt hw h k aS aT x) = uPt hw h k aS aT ((aT⁻¹ * locMat D.sp.cm.sig T.gram h gT * aT).1 * x * (aS⁻¹ * locMat D.sp.cm.sig S.gram h gS⁻¹ * aS).1) := by
  intro D v w hw h S T k aS aT gS gT x
  have hT : (mt T (embV T v gT)).map (GlobalTheory.InertHomIdx.compW D w) = (locMat D.sp.cm.sig T.gram h gT).1 := by
    have e := finMat_map_compAt D.sp.cm.sig T.gram h (embV T v gT)
    rw [proj_emb_self] at e
    exact e
  have hS : (mt S (embV S v gS⁻¹)).map (GlobalTheory.InertHomIdx.compW D w) = (locMat D.sp.cm.sig S.gram h gS⁻¹).1 := by
    have e := finMat_map_compAt D.sp.cm.sig S.gram h (embV S v gS⁻¹)
    rw [proj_emb_self] at e
    exact e
  have hinv : (embV S v gS)⁻¹ = embV S v gS⁻¹ := (map_inv _ _).symm
  rw [actO, uPt, uPt, hinv, mul_map_secW, map_secW_mul, hT, hS]
  congr 1
  have h1 : aT.1 * (aT⁻¹).1 = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have h2 : aS.1 * (aS⁻¹).1 = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  simp only [Units.val_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
  rw [h2, Matrix.mul_one]
  rw [← Matrix.mul_assoc aT.1 (aT⁻¹).1, h1, Matrix.one_mul]
