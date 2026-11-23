import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightBoundConst
open Matrix Filter Topology Set GlobalTheory.HermFrame GlobalTheory.IndefiniteRowSideFullHecke.HermitianInterpolation GlobalTheory.InterpCurv
open scoped ComplexOrder ContDiff

namespace GlobalTheory.InterpDiff

theorem mdel_interp {ι n : Type} [Fintype ι] [Fintype n] [DecidableEq n]
    {H₀ H : (ι → ℂ) → Matrix n n ℂ} {s : (ι → ℂ) → ℝ} {z : ι → ℂ}
    (h0 : MContDiffAt 1 H₀ z) (h1 : MContDiffAt 1 H z) (hs : DifferentiableAt ℝ s z) (ξ : ι → ℂ) :
    mdel (interp H₀ H s) z ξ = mdel H₀ z ξ + ((s z : ℂ) • (mdel H z ξ + -mdel H₀ z ξ) +
      GlobalTheory.del (fun x => (s x : ℂ)) z ξ • (H z + -H₀ z)) := by
  have hs' : DifferentiableAt ℝ (fun x => (s x : ℂ)) z :=
    Complex.ofRealCLM.differentiableAt.comp z hs
  have hd : MContDiffAt 1 (fun x => H x + -H₀ x) z := h1.add h0.neg
  have e := mdel_smul hs' hd ξ
  rw [mdel_add h1 h0.neg, mdel_neg] at e
  rw [← e]
  ext a b
  have e2 : (fun x => interp H₀ H s x a b) =
      fun x => H₀ x a b + (s x : ℂ) * ((H x + -H₀ x) a b) := by
    funext x
    simp only [interp, Matrix.add_apply, Matrix.smul_apply, Matrix.neg_apply, smul_eq_mul]
    push_cast
    ring
  rw [mdel_apply, e2, GlobalTheory.del_add (h0.diff a b) (hs'.fun_mul (hd.diff a b))]
  rfl

theorem form_conn_mulVec {ι n : Type} [Fintype ι] [Fintype n] [DecidableEq n]
    {K : (ι → ℂ) → Matrix n n ℂ} {z : ι → ℂ} (hu : IsUnit (K z).det) (ξ : ι → ℂ) (v w : n → ℂ) :
    form (K z) (conn K z ξ *ᵥ v) w = form (mdel K z ξ) v w := by
  rw [← conn_transpose_mul hu, form, form, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec v, Matrix.vecMul_transpose]

theorem form_conn_interp_sub : ∀ {ι n : Type} [Fintype ι] [Fintype n] [DecidableEq n] {H₀ H : (ι → ℂ) → Matrix n n ℂ} {s : (ι → ℂ) → ℝ} {z : ι → ℂ}, MContDiffAt 1 H₀ z → MContDiffAt 1 H z → DifferentiableAt ℝ s z → IsUnit (H₀ z).det → IsUnit (H z).det → IsUnit (interp H₀ H s z).det → ∀ (ξ : ι → ℂ) (v w : n → ℂ), form (interp H₀ H s z) ((conn (interp H₀ H s) z ξ - conn H₀ z ξ) *ᵥ v) w = (s z : ℂ) * form (H z) ((conn H z ξ - conn H₀ z ξ) *ᵥ v) w + GlobalTheory.del (fun x => (s x : ℂ)) z ξ * (form (H z) v w - form (H₀ z) v w) := by
  intro ι n _ _ _ H₀ H s z h0 h1 hs u0 u1 u ξ v w
  have e1 := form_conn_mulVec u ξ v w
  have e2 := form_conn_mulVec u0 ξ v w
  have e3 := form_conn_mulVec u1 ξ v w
  rw [mdel_interp h0 h1 hs] at e1
  simp only [form, Matrix.sub_mulVec, sub_dotProduct, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.neg_mulVec, dotProduct_add, dotProduct_smul, dotProduct_neg, smul_eq_mul] at e1 e2 e3 ⊢
  rw [e1]
  simp only [interp, Matrix.add_mulVec, Matrix.smul_mulVec, dotProduct_add, dotProduct_smul, smul_eq_mul]
  push_cast
  linear_combination (s z - 1) * e2 - (s z) * e3

end GlobalTheory.InterpDiff
