import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJABddKapTP
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NFRadRedLocSec

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField
open scoped ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

theorem kap_Dw_emb (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) :
    PI.UnitaryGroupMassFormula.GsFr.Dw k r * B2.embWb k r μ = B2.embWb k r μ * PI.UnitaryGroupMassFormula.GsFr.Dw k r := by
  ext i j
  simp only [PI.UnitaryGroupMassFormula.GsFr.Dw, Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases hi : TwoByOneBlock.mid k r i <;> by_cases hj : TwoByOneBlock.mid k r j
  · have hi' : (r ≤ i.val ∧ i.val ≤ r + k) := hi
    have hj' : (r ≤ j.val ∧ j.val ≤ r + k) := hj
    simp [hi', hj']
  · have hi' : (r ≤ i.val ∧ i.val ≤ r + k) := hi
    have hj' : ¬(r ≤ j.val ∧ j.val ≤ r + k) := hj
    have hij : i ≠ j := fun h => hj (h ▸ hi)
    rw [TwoByOneBlock.emb_out_col μ i j hj]
    simp [hi', hj', hij]
  · have hi' : ¬(r ≤ i.val ∧ i.val ≤ r + k) := hi
    have hj' : (r ≤ j.val ∧ j.val ≤ r + k) := hj
    have hij : i ≠ j := fun h => hi (h ▸ hj)
    rw [TwoByOneBlock.emb_out_row μ i j hi]
    simp [hi', hj', hij]
  · have hi' : ¬(r ≤ i.val ∧ i.val ≤ r + k) := hi
    have hj' : ¬(r ≤ j.val ∧ j.val ≤ r + k) := hj
    simp [hi', hj']

theorem wbP_mulVec {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) {h : B.Mat k r}
    (hh : h ∈ UWset k r z) (v : Fin (2 * r + k + 1) → ℂ) :
    SSn.wbP k r (h *ᵥ v) = h *ᵥ SSn.wbP k r v := by
  obtain ⟨η, -, -, rfl⟩ := (TwoByOneBlock.UWset_iff hz h).1 hh
  have e : ∀ w, SSn.wbP k r w = PI.UnitaryGroupMassFormula.GsFr.Dw k r *ᵥ w := fun w => by
    rw [PI.UnitaryGroupMassFormula.GsFr.Dw_mulVec]; rfl
  rw [e, e, Matrix.mulVec_mulVec, kap_Dw_emb, ← Matrix.mulVec_mulVec]

theorem kap_prWv_mulVec {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) {h : B.Mat k r}
    (hh : h ∈ UWset k r z) (v : Fin (2 * r + k + 1) → ℂ) :
    SSn.prWv k r z (h *ᵥ v) = h *ᵥ SSn.prWv k r z v := by
  have hz' : h *ᵥ z = z := hh.2.2
  have hherm : herm (Hpk k r) (h *ᵥ SSn.wbP k r v) z = herm (Hpk k r) (SSn.wbP k r v) z := by
    conv_lhs => rw [← hz']
    exact Formalism.FourierDecayAlt.P.Qx2.herm_uh hh.1 _ _
  unfold SSn.prWv
  rw [wbP_mulVec hz hh, Matrix.mulVec_add, Matrix.mulVec_smul, hz', hherm]

theorem kap_nrmW_mulVec {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) {h : B.Mat k r}
    (hh : h ∈ UWset k r z) (a : Fin (2 * r + k + 1) → ℂ) :
    PRho.nrmW k r z (h *ᵥ a) = PRho.nrmW k r z a := by
  unfold PRho.nrmW
  rw [kap_prWv_mulVec hz hh, Formalism.FourierDecayAlt.P.Qx2.herm_uh hh.1]

theorem kap_mulVec_contDiff {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun a : Fin n → ℂ => M *ᵥ a) := by
  have h := ((LinearMap.toContinuousLinearMap (Matrix.mulVecLin M)).contDiff
    (n := ((⊤ : ℕ∞) : WithTop ℕ∞))).restrict_scalars ℝ
  convert h using 1
  funext a
  rfl

theorem kap_herm_contDiff {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun u : Fin n → ℂ => herm H u u) := by
  have hconj : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (starRingEnd ℂ) := Complex.conjCLE.contDiff
  have e : (fun u : Fin n → ℂ => herm H u u) = fun u => ∑ i, starRingEnd ℂ (u i) * (H *ᵥ u) i := by
    funext u; simp [herm, dotProduct, Complex.star_def]
  rw [e]
  refine ContDiff.sum fun i _ => ?_
  exact (hconj.comp (contDiff_apply ℝ ℂ i)).mul ((contDiff_apply ℝ ℂ i).comp (kap_mulVec_contDiff H))

theorem kap_nrmW_contDiff (z : Fin (2 * r + k + 1) → ℂ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun a => PRho.nrmW k r z a) := by
  have e : (fun a => PRho.nrmW k r z a) =
      fun a => (herm (Hpk k r) (PI.UnitaryGroupMassFormula.GsFr.Pm k r z *ᵥ a) (PI.UnitaryGroupMassFormula.GsFr.Pm k r z *ᵥ a)).re := by
    funext a; unfold PRho.nrmW; rw [PI.UnitaryGroupMassFormula.GsFr.Pm_mulVec]; rfl
  rw [e]
  exact Complex.reCLM.contDiff.comp ((kap_herm_contDiff (Hpk k r)).comp (kap_mulVec_contDiff _))

theorem weighted_norm_facts_hold : NrmWFacts := fun k r z hz _ =>
  ⟨kap_nrmW_contDiff z, fun _ hh a => kap_nrmW_mulVec hz hh a⟩

end

end Formalism.FourierDecayAlt.P.CutMP.JA
