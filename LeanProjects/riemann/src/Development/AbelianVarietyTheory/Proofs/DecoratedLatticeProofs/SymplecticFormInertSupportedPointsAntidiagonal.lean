import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SpanRhoTEqTop
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PiEqOfFinPart

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

namespace GlobalTheory.InertFrameSympl

open Formalism.UG (cT cT_mul cT_one antiJ)
open GlobalTheory.InertFrameLoc

variable {D : D7} {v : HeightOneSpectrum (𝓞 D.host.F)} {w : HeightOneSpectrum (𝓞 D.host.E)}
  {hw : IsInertAt D.host.F D.host.E v w} {h : w.under (𝓞 D.host.F) = v}

def evW (hw : IsInertAt D.host.F D.host.E v w) (h : w.under (𝓞 D.host.F) = v) : AE D →+* w.adicCompletion D.host.E :=
  (GlobalTheory.LFun.InertChart.complEquiv hw h).toRingHom.comp (compFin D.host.F D.host.E v)

theorem secW_apply (z : w.adicCompletion D.host.E) :
    secW hw h z = GlobalTheory.EmbChart.tensAt D.host.E v ((GlobalTheory.LFun.InertChart.complEquiv hw h).symm z) := rfl

theorem secW_mul_right (z : w.adicCompletion D.host.E) (A : AE D) :
    secW hw h z * A = secW hw h (z * evW hw h A) := by
  rw [secW_apply, secW_apply, GlobalTheory.EmbChart.tensAt_mul_right]
  congr 1
  rw [map_mul (GlobalTheory.LFun.InertChart.complEquiv hw h).symm]
  show _ = _ * (GlobalTheory.LFun.InertChart.complEquiv hw h).symm ((GlobalTheory.LFun.InertChart.complEquiv hw h) _)
  rw [RingEquiv.symm_apply_apply]

theorem evW_secW (z : w.adicCompletion D.host.E) : evW hw h (secW hw h z) = z := by
  show GlobalTheory.LFun.InertChart.complEquiv hw h (compFin D.host.F D.host.E v (GlobalTheory.EmbChart.tensAt D.host.E v
    ((GlobalTheory.LFun.InertChart.complEquiv hw h).symm z))) = z
  rw [GlobalTheory.EmbChart.compFin_tensAt, RingEquiv.apply_symm_apply]

theorem evW_incA (a : D.host.E) : evW hw h (incA D a) = algebraMap D.host.E _ a := by
  show GlobalTheory.LFun.toCompl h (compFin D.host.F D.host.E v ((1 : AF D.host.F) ⊗ₜ[D.host.F] a)) = _
  show GlobalTheory.LFun.toCompl h ((evFin D.host.F v 1) ⊗ₜ[D.host.F] a) = _
  rw [map_one, GlobalTheory.LFun.toCompl_tmul, map_one, one_mul]

theorem incA_mul_secW (a : D.host.E) (z : w.adicCompletion D.host.E) :
    incA D a * secW hw h z = secW hw h (algebraMap D.host.E _ a * z) := by
  rw [mul_comm, secW_mul_right, evW_incA, mul_comm]

theorem cA_secW {c : w.adicCompletion D.host.E →+* w.adicCompletion D.host.E} (hc : GlobalTheory.LFun.IsConjAt D.sp.cm.sig h c)
    (z : w.adicCompletion D.host.E) : cA D (secW hw h z) = secW hw h (c z) := by
  rw [secW_apply, secW_apply]
  show Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF D.host.F) D.sp.cm.sig (GlobalTheory.EmbChart.tensAt D.host.E v _) = GlobalTheory.EmbChart.tensAt D.host.E v _
  rw [GlobalTheory.EmbChart.sigR_tensAt]
  congr 1
  apply (GlobalTheory.LFun.InertChart.complEquiv hw h).injective
  rw [RingEquiv.apply_symm_apply]
  have := hc ((GlobalTheory.LFun.InertChart.complEquiv hw h).symm z)
  exact this.symm.trans (congrArg c ((GlobalTheory.LFun.InertChart.complEquiv hw h).apply_symm_apply z))

theorem hO_map_secW {S T : HSp D} {c : w.adicCompletion D.host.E →+* w.adicCompletion D.host.E}
    (hc : GlobalTheory.LFun.IsConjAt D.sp.cm.sig h c) (M N : Matrix (Fin T.rank) (Fin S.rank) (w.adicCompletion D.host.E)) :
    hO S T (M.map (secW hw h)) (N.map (secW hw h)) = secW hw h (Matrix.trace
      ((S.gram⁻¹.map (algebraMap D.host.E (w.adicCompletion D.host.E)) : Matrix (Fin S.rank) (Fin S.rank) _) *
      cT c N * (T.gram.map (algebraMap D.host.E (w.adicCompletion D.host.E)) : Matrix (Fin T.rank) (Fin T.rank) _) * M)) := by
  simp only [hO, Matrix.map_apply, cA_secW hc, incA_mul_secW, secW_mul_right, evW_incA, evW_secW, ← map_sum]
  congr 1
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Finset.sum_mul, Matrix.map_apply, cT, Matrix.transpose_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Eq.trans (Finset.sum_congr rfl fun c _ => Finset.sum_comm) ?_
  rw [Finset.sum_comm]

variable {L : Type} [Field L]

theorem cT_smul' (c : L →+* L) {m n : ℕ} (k : L) (A : Matrix (Fin m) (Fin n) L) : cT c (k • A) = c k • cT c A := by
  ext i j
  simp [cT, Matrix.smul_apply]

theorem inv_eq_of_frame (c : L →+* L) {n : ℕ} {G G' : Matrix (Fin n) (Fin n) L} (hG : G' * G = 1) (a : GL (Fin n) L)
    (ha : cT c a.1 * G * a.1 = antiJ L n) : G' = a.1 * antiJ L n * cT c a.1 := by
  have h1 : G * a.1 = cT c (a⁻¹).1 * antiJ L n := by
    rw [← ha, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← cT_mul, Units.mul_inv, cT_one, Matrix.one_mul]
  have h2 : G * (a.1 * antiJ L n * cT c a.1) = 1 := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.mul_assoc (cT c (a⁻¹).1),
      Formalism.UG.P.fIwasawa_antiJ_mul_antiJ, Matrix.mul_one, ← cT_mul, Units.mul_inv, cT_one]
  rw [← Matrix.mul_one G', ← h2, ← Matrix.mul_assoc, hG, Matrix.one_mul]

theorem trace_frame (c : L →+* L) {n n' : ℕ} (k : L) (aS : GL (Fin n) L) (aT : GL (Fin n') L)
    (GT J' : Matrix (Fin n') (Fin n') L) (J : Matrix (Fin n) (Fin n) L) (hT : cT c aT.1 * GT * aT.1 = J')
    (x y : Matrix (Fin n') (Fin n) L) :
    Matrix.trace (aS.1 * J * cT c aS.1 * cT c (k • (aT.1 * y * (aS⁻¹).1)) * GT * (k • (aT.1 * x * (aS⁻¹).1))) =
      k * c k * Matrix.trace (J * cT c y * J' * x) := by
  rw [cT_smul', cT_mul, cT_mul]
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (cT c aS.1) (cT c (aS⁻¹).1), ← cT_mul, Units.inv_mul, cT_one, Matrix.one_mul,
    ← Matrix.mul_assoc GT aT.1, ← Matrix.mul_assoc (cT c aT.1) (GT * aT.1), ← Matrix.mul_assoc (cT c aT.1) GT, hT, Matrix.trace_mul_comm aS.1]
  simp only [Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
  ring

theorem hO_uPt {D : D7} {v : HeightOneSpectrum (𝓞 D.host.F)} {w : HeightOneSpectrum (𝓞 D.host.E)}
    {hw : IsInertAt D.host.F D.host.E v w} {h : w.under (𝓞 D.host.F) = v} {S T : HSp D}
    {c : w.adicCompletion D.host.E →+* w.adicCompletion D.host.E} (k : w.adicCompletion D.host.E)
    {aS : GL (Fin S.rank) (w.adicCompletion D.host.E)} {aT : GL (Fin T.rank) (w.adicCompletion D.host.E)}
    (hc : GlobalTheory.LFun.IsConjAt D.sp.cm.sig h c)
    (hS : cT c aS.1 * S.gram.map (algebraMap D.host.E _) * aS.1 = antiJ _ S.rank)
    (hT : cT c aT.1 * T.gram.map (algebraMap D.host.E _) * aT.1 = antiJ _ T.rank)
    (x y : Matrix (Fin T.rank) (Fin S.rank) (w.adicCompletion D.host.E)) :
    hO S T (uPt hw h k aS aT x) (uPt hw h k aS aT y) =
      secW hw h (k * c k * Matrix.trace (antiJ (w.adicCompletion D.host.E) S.rank * cT c y * antiJ (w.adicCompletion D.host.E) T.rank * x)) := by
  have hG : (S.gram⁻¹.map (algebraMap D.host.E (w.adicCompletion D.host.E)) : Matrix (Fin S.rank) (Fin S.rank) _) *
      S.gram.map (algebraMap D.host.E (w.adicCompletion D.host.E)) = 1 := by
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ (GlobalTheory.LatVac.gram_det_isUnit S),
      Matrix.map_one _ (map_zero _) (map_one _)]
  rw [uPt, uPt, hO_map_secW hc, inv_eq_of_frame c hG aS hS, trace_frame c k aS aT _ _ _ hT]

theorem symplOH_uPt : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : IsInertAt D.host.F D.host.E v w) (h : w.under (𝓞 D.host.F) = v) (S T : HSp D) (c : w.adicCompletion D.host.E →+* w.adicCompletion D.host.E) (k : w.adicCompletion D.host.E) (aS : GL (Fin S.rank) (w.adicCompletion D.host.E)) (aT : GL (Fin T.rank) (w.adicCompletion D.host.E)), IsConjAt D.sp.cm.sig h c → Formalism.UG.cT c aS.1 * S.gram.map (algebraMap D.host.E _) * aS.1 = Formalism.UG.antiJ _ S.rank → Formalism.UG.cT c aT.1 * T.gram.map (algebraMap D.host.E _) * aT.1 = Formalism.UG.antiJ _ T.rank → ∀ x y : Matrix (Fin T.rank) (Fin S.rank) (w.adicCompletion D.host.E), ψ (symplOH S T (uPt hw h k aS aT x) (uPt hw h k aS aT y)) = thW ψ hw h (k * c k) (2⁻¹ * GlobalTheory.Hk3.locH c 1 (GlobalTheory.SphTheta.antiG _ S.rank) (GlobalTheory.SphTheta.antiG _ T.rank) x y) := by
  intro D ψ v w hw h S T c k aS aT hc hS hT x y
  have h2 : (2 : w.adicCompletion D.host.E) ≠ 0 := by
    have : CharZero (w.adicCompletion D.host.E) := algebraRat.charZero _
    exact two_ne_zero
  have hx : (2⁻¹ : w.adicCompletion D.host.E) • x + (2⁻¹ : w.adicCompletion D.host.E) • x = x := by
    rw [← add_smul, ← two_mul, mul_inv_cancel₀ h2, one_smul]
  have hl : GlobalTheory.Hk3.locH c 1 (GlobalTheory.SphTheta.antiG _ S.rank) (GlobalTheory.SphTheta.antiG _ T.rank) x y =
      Matrix.trace (antiJ (w.adicCompletion D.host.E) S.rank * cT c y * antiJ (w.adicCompletion D.host.E) T.rank * x) := by
    rw [GlobalTheory.Hk3.locH, one_mul]
    rfl
  conv_lhs => rw [← hx, uPt_add, GlobalTheory.SplitScalar.symplOH_add_left, GlobalTheory.SplitScalar.symplOH_add_self]
  rw [thW_apply, symplO, hO_uPt k hc hS hT, hl, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, mul_assoc]

end GlobalTheory.InertFrameSympl
