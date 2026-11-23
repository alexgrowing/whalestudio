import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConnFormSmul

open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm GlobalTheory.TorsionForm.Gauge
open scoped ContDiff

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.TorsionForm.Gauge

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {g n : ℕ}

theorem fderiv_mul_smul_apply {ρ : Pt E g → ℂ} {s : Pt E g → Ext (n + n + g)} {P : Pt E g}
    (hρ : DifferentiableAt ℝ ρ P) (hs : DifferentiableAt ℝ s P) (v : Pt E g) :
    fderiv ℝ (fun Q => ρ Q • s Q) P v = ρ P • fderiv ℝ s P v + fderiv ℝ ρ P v • s P := by
  rw [show (fun Q => ρ Q • s Q) = ρ • s from rfl, (hρ.hasFDerivAt.smul hs.hasFDerivAt).fderiv]; simp

theorem d10_smul {ρ : Pt E g → ℂ} {s : Pt E g → Ext (n + n + g)} {P : Pt E g}
    (hρ : DifferentiableAt ℝ ρ P) (hs : DifferentiableAt ℝ s P) (v : Pt E g) :
    d10 (fun Q => ρ Q • s Q) P v = ρ P • d10 s P v + d10 ρ P v • s P := by
  simp only [d10, fderiv_mul_smul_apply hρ hs, smul_eq_mul]
  module

theorem d01_smul {ρ : Pt E g → ℂ} {s : Pt E g → Ext (n + n + g)} {P : Pt E g}
    (hρ : DifferentiableAt ℝ ρ P) (hs : DifferentiableAt ℝ s P) (v : Pt E g) :
    d01 (fun Q => ρ Q • s Q) P v = ρ P • d01 s P v + d01 ρ P v • s P := by
  simp only [d01, fderiv_mul_smul_apply hρ hs, smul_eq_mul]
  module

theorem connection_smul (h : Pt E g → ℝ) {ρ : Pt E g → ℂ} {s : Pt E g → Ext (n + n + g)} {P : Pt E g}
    (hρ : DifferentiableAt ℝ ρ P) (hs : DifferentiableAt ℝ s P) (v : Pt E g) :
    pointDifference h (fun Q => ρ Q • s Q) P v = ρ P • pointDifference h s P v + d10 ρ P v • s P := by
  simp only [pointDifference, d10_smul hρ hs]
  module

end GlobalTheory.TorsionForm.Gauge

namespace GlobalTheory.TorsionForm.Gauge

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {g n : ℕ}

theorem nablaE_smul (τ : E → Matrix (Fin g) (Fin g) ℂ) (h : Pt E g → ℝ) (β : Fin n → E)
    {ρ : Pt E g → ℂ} {s : Pt E g → Ext (n + n + g)} {P : Pt E g}
    (hρ : DifferentiableAt ℝ ρ P) (hs : DifferentiableAt ℝ s P) :
    nablaE τ h β (fun Q => ρ Q • s Q) P = ρ P • nablaE τ h β s P +
      ∑ i, (d10 ρ P (hor τ P (β i)) • wedge (dt g i) (s P) +
        d01 ρ P (hor τ P (β i)) • wedge (dtb g i) (s P)) := by
  simp only [nablaE, Finset.smul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [connection_smul h hρ hs, d01_smul hρ hs, connForm_smul]
  simp only [wedge_add, wedge_smul]
  module

theorem dbarV_smul {ρ : Pt E g → ℂ} {s : Pt E g → Ext (n + n + g)} {P : Pt E g}
    (hρ : DifferentiableAt ℝ ρ P) (hs : DifferentiableAt ℝ s P) :
    dbarV (fun Q => ρ Q • s Q) P = ρ P • dbarV s P +
      ∑ a, d01 ρ P (vert E a) • wedge (dzb n a) (s P) := by
  simp only [dbarV, Finset.smul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [d01_smul hρ hs, wedge_add, wedge_smul, wedge_smul]

theorem dbarAdj_smul (τ : E → Matrix (Fin g) (Fin g) ℂ) (h : Pt E g → ℝ)
    {ρ : Pt E g → ℂ} {s : Pt E g → Ext (n + n + g)} {P : Pt E g}
    (hρ : DifferentiableAt ℝ ρ P) (hs : DifferentiableAt ℝ s P) :
    dbarAdj τ h (fun Q => ρ Q • s Q) P = ρ P • dbarAdj τ h s P -
      ∑ a, ∑ c, (2 * imPart τ P.1 a c * d10 ρ P (vert E a)) • contr (dzb n c) (s P) := by
  simp only [dbarAdj, smul_neg, sub_eq_add_neg, ← neg_add, Finset.smul_sum, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
  rw [connection_smul h hρ hs, contr_add, contr_smul, contr_smul]
  simp only [smul_add, smul_smul]
  congr 2; ring

theorem superconn_smul (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (g n : ℕ)
    (τ : E → Matrix (Fin g) (Fin g) ℂ) (h : Pt E g → ℝ) (β : Fin n → E) (u : ℝ)
    (ρ : Pt E g → ℂ) (s : Pt E g → Ext (n + n + g)) (P : Pt E g) :
    DifferentiableAt ℝ ρ P → DifferentiableAt ℝ s P →
      superconn τ h β u (fun Q => ρ Q • s Q) P = ρ P • superconn τ h β u s P + commOp τ β u ρ P (s P) := by
  intro hρ hs
  rw [superconn, superconn, commOp, nablaE_smul τ h β hρ hs, dbarV_smul hρ hs, dbarAdj_smul τ h hρ hs]
  module

end GlobalTheory.TorsionForm.Gauge
