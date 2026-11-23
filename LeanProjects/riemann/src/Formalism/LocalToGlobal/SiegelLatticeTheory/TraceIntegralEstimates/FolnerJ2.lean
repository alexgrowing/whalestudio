import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.FolnerG2
import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.IsFolnerOfEquiv
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.BesselLevi
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.BesselLevi

noncomputable section

open MeasureTheory Topology Matrix
open scoped ENNReal

namespace Formalism.L2.S.Pv.FolnerJ

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.Pf.WFL Formalism.L2.SG.Pf.EnergyAbs Formalism.L2.S.Pv.FolnerS Formalism.L2.S.Pv.FolnerG
  Formalism.L2.S.Pv.FolnerT PI.QuotSetU.UnitaryGroupMassFormula.ModW PI.QuotSetU.UnitaryGroupMassFormula.ModW.MG

open Formalism.MainNotions.S (uMat)

variable {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {e f : Fin r → Fin (2 * r + k + 1) → ℂ}
  {wf : Fin k → Fin (2 * r + k + 1) → ℂ} {z0 : Fin (2 * r + k + 1) → ℂ}

theorem uMat_ext {a b : Formalism.REAL.UJ ε} (h : uMat a = uMat b) : a = b :=
  Subtype.ext (Units.ext h)

theorem continuous_uMat : Continuous (uMat : Formalism.REAL.UJ ε → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :=
  Units.continuous_val.comp continuous_subtype_val

def ofM (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (hg : g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) :
    GH k r :=
  mk (PI.QuotSetU.UnitaryGroupMassFormula.unitary_hermitian_group k r) g hg

theorem toM_ofM (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (hg : g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) :
    (ofM g hg).toM = g := toM_mk g hg

def psiF (hF : IsFrameJ ε e f wf z0) : GH k r ≃* Formalism.REAL.UJ ε where
  toFun g := toUJ (Qm e f wf z0 * g.toM * Qi ε e f wf z0) (conjQ_UJ hF g.toM_mem)
  invFun s := ofM (Qi ε e f wf z0 * uMat s * Qm e f wf z0) (conj_mem_UH hF (uMat_mem s))
  left_inv g := by
    ext1
    rw [toM_ofM, uMat_toUJ]
    exact Qi_Qm_conj hF _
  right_inv s := by
    apply uMat_ext
    rw [uMat_toUJ, toM_ofM]
    simp only [← Matrix.mul_assoc, Qm_mul_Qi hF, Matrix.one_mul]
    rw [Matrix.mul_assoc, Qm_mul_Qi hF, Matrix.mul_one]
  map_mul' g h := by
    apply uMat_ext
    rw [uMat_mul, uMat_toUJ, uMat_toUJ, uMat_toUJ, toM_mul]
    calc Qm e f wf z0 * (g.toM * h.toM) * Qi ε e f wf z0
        = Qm e f wf z0 * g.toM * (Qi ε e f wf z0 * Qm e f wf z0) * h.toM * Qi ε e f wf z0 := by
          rw [Qi_mul_Qm hF, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = _ := by simp only [Matrix.mul_assoc]

theorem continuous_psiF (hF : IsFrameJ ε e f wf z0) : Continuous (psiF hF) := by
  rw [(Formalism.REAL.isClosedEmbeddingMatrix _ ε).1.isEmbedding.continuous_iff]
  show Continuous (fun g : GH k r => Qm e f wf z0 * g.toM * Qi ε e f wf z0)
  exact (continuous_const.matrix_mul continuous_toM).matrix_mul continuous_const

theorem continuous_psiF_symm (hF : IsFrameJ ε e f wf z0) : Continuous (psiF hF).symm := by
  rw [continuous_iff_toM]
  have e1 : (fun s : Formalism.REAL.UJ ε => ((psiF hF).symm s).toM) = fun s => Qi ε e f wf z0 * uMat s * Qm e f wf z0 := by
    funext s; exact toM_ofM _ (conj_mem_UH hF (uMat_mem s))
  rw [e1]
  exact (continuous_const.matrix_mul continuous_uMat).matrix_mul continuous_const

theorem inS_psiF_iff {T : ℝ} {z : Fin (2 * r + k + 1) → ℂ} (hF : IsFrameJ ε e f wf (z0v T z)) (hT : 0 < T) (g : GH k r) :
    InS e z (uMat (psiF hF g)) ↔ g.toM ∈ Formalism.QuantumDeterminants.Sset k r (zBv k r T) := by
  have hz := Qm_zB (e := e) (f := f) (wf := wf) hT z
  have key : psiF hF g ∈ HNset ε e f wf (z0v T z) (zBv k r T) ↔ g.toM ∈ Formalism.QuantumDeterminants.Sset k r (zBv k r T) := by
    show Qi ε e f wf (z0v T z) * uMat (psiF hF g) * Qm e f wf (z0v T z) ∈ Formalism.QuantumDeterminants.Sset k r (zBv k r T) ↔ _
    show Qi ε e f wf (z0v T z) * (Qm e f wf (z0v T z) * g.toM * Qi ε e f wf (z0v T z)) * Qm e f wf (z0v T z) ∈ _ ↔ _
    rw [Qi_Qm_conj hF]
  rw [← key]
  constructor
  · intro hs
    exact HNset_of_inS (fun k r T hT s hs h1 h2 => bessel_levi_formula k r T hT s hs h1 h2) hF hT hz hs
  · intro hs
    exact inS_of_HNset hF hz (inWb_zB T) ⟨_, rfl⟩ hs

theorem isFolner_Sinf {ι : Type} [Fintype ι] {εv : ι → Fin (2 * r + k + 1) → Bool}
    (ev fv : ι → Fin r → Fin (2 * r + k + 1) → ℂ) (wv : ι → Fin k → Fin (2 * r + k + 1) → ℂ)
    (zv : ι → Fin (2 * r + k + 1) → ℂ) (T : ι → ℝ) (hT : ∀ v, 0 < T v)
    (hF : ∀ v, IsFrameJ (εv v) (ev v) (fv v) (wv v) (z0v (T v) (zv v)))
    (μS : Measure (∀ v, Formalism.REAL.UJ (εv v)))
    (hμ : IsHaarSub {s : ∀ v, Formalism.REAL.UJ (εv v) | ∀ v, InS (ev v) (zv v) (uMat (s v))} μS) :
    IsFolner {s : ∀ v, Formalism.REAL.UJ (εv v) | ∀ v, InS (ev v) (zv v) (uMat (s v))} μS := by
  let Φ : (ι → GH k r) ≃* (∀ v, Formalism.REAL.UJ (εv v)) := MulEquiv.piCongrRight fun v => psiF (hF v)
  have hΦ : Continuous Φ := continuous_pi fun v => (continuous_psiF (hF v)).comp (continuous_apply v)
  have hΦ' : Continuous Φ.symm := continuous_pi fun v => (continuous_psiF_symm (hF v)).comp (continuous_apply v)
  have hset : Φ ⁻¹' {s : ∀ v, Formalism.REAL.UJ (εv v) | ∀ v, InS (ev v) (zv v) (uMat (s v))} =
      SP (fun v => zBv k r (T v)) := by
    ext x
    show (∀ v, InS (ev v) (zv v) (uMat (psiF (hF v) (x v)))) ↔ ∀ v, (x v).toM ∈ PI.QuotSetU.Sset k r (zBv k r (T v))
    exact forall_congr' fun v => inS_psiF_iff (hF v) (hT v) (x v)
  refine isFolner_of_equiv Φ hΦ hΦ' hμ ?_
  have hμ' := isHaarSub_comap Φ hΦ hΦ' hμ
  rw [hset] at hμ' ⊢
  exact isFolner_pi (z := fun v => zBv k r (T v)) (fun v => inWb_zB (T v))
    (fun v => by show 0 < Formalism.QuantumDeterminants.Tz k r (zBv k r (T v)); rw [Tz_zB (hT v).le]; exact hT v) _ hμ'

end Formalism.L2.S.Pv.FolnerJ
