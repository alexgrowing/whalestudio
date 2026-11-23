import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TranslationInv

set_option autoImplicit false

noncomputable section

open Matrix Set Filter Topology
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe

namespace GlobalTheory.TorsionForm.Pullback

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {g n : ℕ}

def nabHol (τ : E → Matrix (Fin g) (Fin g) ℂ) (h : Pt E g → ℝ) (s : Pt E g → Ext (n + n + g))
    (Q : Pt E g) (v : E) : Ext (n + n + g) :=
  pointDifference h s Q (hor τ Q v)

def nabAnti (τ : E → Matrix (Fin g) (Fin g) ℂ) (s : Pt E g → Ext (n + n + g))
    (Q : Pt E g) (v : E) : Ext (n + n + g) :=
  d01 s Q (hor τ Q v) + connForm τ Q.1 v (s Q)

def nabPiece (τ : E → Matrix (Fin g) (Fin g) ℂ) (h : Pt E g → ℝ) (s : Pt E g → Ext (n + n + g))
    (Q : Pt E g) (i : Fin n) (v : E) : Ext (n + n + g) :=
  wedge (dt g i) (nabHol τ h s Q v) + wedge (dtb g i) (nabAnti τ s Q v)

theorem nablaE_eq_sum (τ : E → Matrix (Fin g) (Fin g) ℂ) (h : Pt E g → ℝ) (β : Fin n → E)
    (s : Pt E g → Ext (n + n + g)) (Q : Pt E g) :
    nablaE τ h β s Q = ∑ i, nabPiece τ h s Q i (β i) := rfl

theorem wedge_add {m : ℕ} (i : Fin m) (w w' : Ext m) : wedge i (w + w') = wedge i w + wedge i w' := by
  funext S; simp only [wedge, Pi.add_apply]; split_ifs <;> ring

theorem wedge_smul {m : ℕ} (i : Fin m) (c : ℂ) (w : Ext m) : wedge i (c • w) = c • wedge i w := by
  funext S; simp only [wedge, Pi.smul_apply, smul_eq_mul]; split_ifs <;> ring

theorem wedge_real {m : ℕ} (i : Fin m) (r : ℝ) (w : Ext m) : wedge i (r • w) = r • wedge i w := by
  funext S; simp only [wedge, Pi.smul_apply, Complex.real_smul]; split_ifs <;> ring

theorem wedge_zero {m : ℕ} (i : Fin m) : wedge i (0 : Ext m) = 0 := by
  funext S; simp [wedge]

theorem contr_add {m : ℕ} (i : Fin m) (w w' : Ext m) : contr i (w + w') = contr i w + contr i w' := by
  funext S; simp only [contr, Pi.add_apply]; split_ifs <;> ring

theorem contr_zero {m : ℕ} (i : Fin m) : contr i (0 : Ext m) = 0 := by
  funext S; simp [contr]

section Lin

variable {m : ℕ}

theorem dz_add_vector (f : Pt E g → Ext m) (P v w : Pt E g) : d10 f P (v + w) = d10 f P v + d10 f P w := by
  simp only [d10, map_add, smul_add]; module

theorem dz_add_vector_scalar (f : Pt E g → ℂ) (P v w : Pt E g) : d10 f P (v + w) = d10 f P v + d10 f P w := by
  simp only [d10, map_add, smul_add, smul_eq_mul]; ring

theorem dbar_add_vector (f : Pt E g → Ext m) (P v w : Pt E g) : d01 f P (v + w) = d01 f P v + d01 f P w := by
  simp only [d01, map_add, smul_add]; module

theorem dbar_add_vector_scalar (f : E → ℂ) (b v w : E) : d01 f b (v + w) = d01 f b v + d01 f b w := by
  simp only [d01, map_add, smul_add, smul_eq_mul]; ring

theorem dz_smul_I (f : Pt E g → Ext m) (P v : Pt E g) :
    d10 f P (Complex.I • v) = Complex.I • d10 f P v := by
  simp only [d10, smul_smul, Complex.I_mul_I, neg_one_smul, map_neg]
  match_scalars <;> ring_nf <;> simp only [Complex.I_sq] <;> ring

theorem dz_smul_I_scalar (f : Pt E g → ℂ) (P v : Pt E g) :
    d10 f P (Complex.I • v) = Complex.I • d10 f P v := by
  simp only [d10, smul_smul, Complex.I_mul_I, neg_one_smul, map_neg, smul_eq_mul]; ring_nf
  simp only [Complex.I_sq]; ring

theorem dbar_smul_I (f : Pt E g → Ext m) (P v : Pt E g) :
    d01 f P (Complex.I • v) = -Complex.I • d01 f P v := by
  simp only [d01, smul_smul, Complex.I_mul_I, neg_one_smul, map_neg]
  match_scalars <;> ring_nf <;> simp only [Complex.I_sq] <;> ring

theorem dbar_smul_I_scalar (f : E → ℂ) (b v : E) :
    d01 f b (Complex.I • v) = -Complex.I • d01 f b v := by
  simp only [d01, smul_smul, Complex.I_mul_I, neg_one_smul, map_neg, smul_eq_mul]; ring_nf
  simp only [Complex.I_sq]; ring

theorem dz_real_smul (f : Pt E g → Ext m) (P v : Pt E g) (r : ℝ) :
    d10 f P (r • v) = r • d10 f P v := by
  simp only [d10, smul_comm Complex.I r v, map_smul]; module

theorem dz_real_smul_scalar (f : Pt E g → ℂ) (P v : Pt E g) (r : ℝ) :
    d10 f P (r • v) = r • d10 f P v := by
  simp only [d10, smul_comm Complex.I r v, map_smul, smul_eq_mul, Complex.real_smul]; ring

theorem dbar_real_smul (f : Pt E g → Ext m) (P v : Pt E g) (r : ℝ) :
    d01 f P (r • v) = r • d01 f P v := by
  simp only [d01, smul_comm Complex.I r v, map_smul]; module

theorem dbar_real_smul_scalar (f : E → ℂ) (b v : E) (r : ℝ) :
    d01 f b (r • v) = r • d01 f b v := by
  simp only [d01, smul_comm Complex.I r v, map_smul, smul_eq_mul, Complex.real_smul]; ring

end Lin

section Lin2

variable (τ : E → Matrix (Fin g) (Fin g) ℂ) (h : Pt E g → ℝ)

theorem hor_add (Q : Pt E g) (v w : E) : hor τ Q (v + w) = hor τ Q v + hor τ Q w := by
  simp [hor, map_add]

theorem hor_I (Q : Pt E g) (v : E) : hor τ Q (Complex.I • v) = Complex.I • hor τ Q v := by
  simp [hor, map_smul]

theorem hor_real (Q : Pt E g) (v : E) (r : ℝ) : hor τ Q (r • v) = r • hor τ Q v := by
  simp [hor, ContinuousLinearMap.map_smul_of_tower]

theorem connForm_add_vec (b v v' : E) (w : Ext (n + n + g)) :
    connForm τ b (v + v') w = connForm τ b v w + connForm τ b v' w := by
  unfold connForm
  have e : (Matrix.of fun a e => d01 (fun b' => imPart τ b' a e) b (v + v')) =
      (Matrix.of fun a e => d01 (fun b' => imPart τ b' a e) b v) +
        Matrix.of fun a e => d01 (fun b' => imPart τ b' a e) b v' := by
    ext a e; simp [dbar_add_vector_scalar]
  rw [e, Matrix.add_mul]
  simp only [Matrix.add_apply, add_smul, Finset.sum_add_distrib]

theorem connForm_I_vec (b v : E) (w : Ext (n + n + g)) :
    connForm τ b (Complex.I • v) w = -Complex.I • connForm τ b v w := by
  unfold connForm
  have e : (Matrix.of fun a e => d01 (fun b' => imPart τ b' a e) b (Complex.I • v)) =
      (-Complex.I) • Matrix.of fun a e => d01 (fun b' => imPart τ b' a e) b v := by
    ext a e; simp [dbar_smul_I_scalar]
  rw [e, Matrix.smul_mul]
  simp only [Matrix.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]

theorem connForm_real_vec (b v : E) (r : ℝ) (w : Ext (n + n + g)) :
    connForm τ b (r • v) w = r • connForm τ b v w := by
  unfold connForm
  have e : (Matrix.of fun a e => d01 (fun b' => imPart τ b' a e) b (r • v)) =
      (r : ℂ) • Matrix.of fun a e => d01 (fun b' => imPart τ b' a e) b v := by
    ext a e; simp [dbar_real_smul_scalar, Complex.real_smul]
  rw [e, Matrix.smul_mul]
  simp only [Matrix.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum, Complex.coe_smul]

theorem connForm_add (b v : E) (w w' : Ext (n + n + g)) :
    connForm τ b v (w + w') = connForm τ b v w + connForm τ b v w' := by
  simp only [connForm, contr_add, wedge_add, smul_add, Finset.sum_add_distrib]

theorem connForm_zero (b v : E) : connForm τ b v (0 : Ext (n + n + g)) = 0 := by
  simp [connForm, contr_zero, wedge_zero]

variable (s : Pt E g → Ext (n + n + g)) (Q : Pt E g)

theorem nabHol_add (v w : E) : nabHol τ h s Q (v + w) = nabHol τ h s Q v + nabHol τ h s Q w := by
  simp only [nabHol, pointDifference, hor_add, dz_add_vector, dz_add_vector_scalar, add_smul]; abel

theorem nabHol_I (v : E) : nabHol τ h s Q (Complex.I • v) = Complex.I • nabHol τ h s Q v := by
  simp only [nabHol, pointDifference, hor_I, dz_smul_I, dz_smul_I_scalar, smul_eq_mul, mul_smul, smul_add]

theorem nabHol_real (v : E) (r : ℝ) : nabHol τ h s Q (r • v) = r • nabHol τ h s Q v := by
  simp only [nabHol, pointDifference, hor_real, dz_real_smul, dz_real_smul_scalar, smul_add, smul_assoc]

theorem nabAnti_add (v w : E) : nabAnti τ s Q (v + w) = nabAnti τ s Q v + nabAnti τ s Q w := by
  simp only [nabAnti, hor_add, dbar_add_vector, connForm_add_vec]; abel

theorem nabAnti_I (v : E) : nabAnti τ s Q (Complex.I • v) = -Complex.I • nabAnti τ s Q v := by
  simp only [nabAnti, hor_I, dbar_smul_I, connForm_I_vec, smul_add]

theorem nabAnti_real (v : E) (r : ℝ) : nabAnti τ s Q (r • v) = r • nabAnti τ s Q v := by
  simp only [nabAnti, hor_real, dbar_real_smul, connForm_real_vec, smul_add]

theorem nabPiece_add (i : Fin n) (v w : E) :
    nabPiece τ h s Q i (v + w) = nabPiece τ h s Q i v + nabPiece τ h s Q i w := by
  simp only [nabPiece, nabHol_add, nabAnti_add, wedge_add]; abel

theorem nabPiece_real (i : Fin n) (v : E) (r : ℝ) :
    nabPiece τ h s Q i (r • v) = r • nabPiece τ h s Q i v := by
  simp only [nabPiece, nabHol_real, nabAnti_real, wedge_real, smul_add]

theorem isLinearMap_nabPiece (i : Fin n) : IsLinearMap ℝ (nabPiece τ h s Q i) :=
  ⟨nabPiece_add τ h s Q i, fun r v => nabPiece_real τ h s Q i v r⟩

theorem nabPiece_zero (i : Fin n) : nabPiece τ h s Q i 0 = 0 := by
  have := nabPiece_add τ h s Q i 0 0
  simpa using this

theorem superconn_add_vec (β δ : Fin n → E) (u : ℝ) :
    superconn τ h (fun i => β i + δ i) u s Q =
      superconn τ h β u s Q + ∑ i, nabPiece τ h s Q i (δ i) := by
  simp only [superconn, nablaE_eq_sum, nabPiece_add, Finset.sum_add_distrib]; abel

theorem superconn_congr (β : Fin n → E) (u : ℝ) {s t : Pt E g → Ext (n + n + g)} {P : Pt E g}
    (hst : s =ᶠ[𝓝 P] t) : superconn τ h β u s P = superconn τ h β u t P := by
  simp only [superconn, nablaE, dbarV, dbarAdj, pointDifference, d10, d01, hst.fderiv_eq, hst.eq_of_nhds]

end Lin2

section Add

variable {s t : Pt E g → Ext (n + n + g)} {P : Pt E g}

theorem dz_add_function (hs : DifferentiableAt ℝ s P) (ht : DifferentiableAt ℝ t P) (v : Pt E g) :
    d10 (fun Q => s Q + t Q) P v = d10 s P v + d10 t P v := by
  simp only [d10, fderiv_fun_add hs ht, ContinuousLinearMap.add_apply]; module

theorem dbar_add_function (hs : DifferentiableAt ℝ s P) (ht : DifferentiableAt ℝ t P) (v : Pt E g) :
    d01 (fun Q => s Q + t Q) P v = d01 s P v + d01 t P v := by
  simp only [d01, fderiv_fun_add hs ht, ContinuousLinearMap.add_apply]; module

theorem superconn_add (τ : E → Matrix (Fin g) (Fin g) ℂ) (h : Pt E g → ℝ) (β : Fin n → E) (u : ℝ)
    (hs : DifferentiableAt ℝ s P) (ht : DifferentiableAt ℝ t P) :
    superconn τ h β u (fun Q => s Q + t Q) P = superconn τ h β u s P + superconn τ h β u t P := by
  simp only [superconn, nablaE, dbarV, dbarAdj, pointDifference, dz_add_function hs ht, dbar_add_function hs ht,
    connForm_add, contr_add, wedge_add, smul_add, Finset.sum_add_distrib, neg_add, add_smul]
  abel

end Add

end GlobalTheory.TorsionForm.Pullback
