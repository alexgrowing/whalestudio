import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PolyRep
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.GoodTopChernForm
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ChernWeilNumbers

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry MvPolynomial GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open ReciprocityTheory.L2DbarEstimates (V)
open Filter Topology
open scoped Matrix

namespace GlobalTheory.GoodMetric

section General

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]

omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] in

theorem contDiffAt_aeval_int {σ : Type} {k : WithTop ℕ∞} {f : E → σ → ℂ} {z : E}
    (hf : ∀ s, ContDiffAt ℝ k (fun x => f x s) z) (P : MvPolynomial σ ℤ) :
    ContDiffAt ℝ k (fun x => aeval (f x) P) z := by
  induction P using MvPolynomial.induction_on with
  | C a => simp only [aeval_C]; exact contDiffAt_const
  | add p q hp hq => simp only [map_add]; exact hp.add hq
  | mul_X p s hp => simp only [map_mul, aeval_X]; exact hp.mul (hf s)

theorem del_aeval_int {σ : Type} [Fintype σ] {f : E → σ → ℂ} {z : E}
    (hf : ∀ s, ContDiffAt ℝ 1 (fun x => f x s) z) (P : MvPolynomial σ ℤ) (ξ : E) :
    del (fun x => aeval (f x) P) z ξ = ∑ s, aeval (f z) (pderiv s P) * del (fun x => f x s) z ξ := by
  classical
  have hd : ∀ Q : MvPolynomial σ ℤ, DifferentiableAt ℝ (fun x => aeval (f x) Q) z :=
    fun Q => (contDiffAt_aeval_int hf Q).differentiableAt one_ne_zero
  induction P using MvPolynomial.induction_on with
  | C a => simp only [aeval_C, pderiv_C, del_const]; simp
  | add p q hp hq =>
    simp only [map_add, add_mul, Finset.sum_add_distrib, ← hp, ← hq]
    rw [del_add (hd p) (hd q)]; rfl
  | mul_X p s hp =>
    simp only [map_mul, aeval_X]
    rw [del_mul (hd p) ((hf s).differentiableAt one_ne_zero), hp]
    simp only [Derivation.leibniz, pderiv_X, smul_eq_mul, map_add, map_mul, aeval_X, add_mul,
      Finset.sum_add_distrib, Finset.sum_mul, Pi.single_apply]
    congr 1
    · rw [Finset.sum_eq_single s] <;> simp +contextual [eq_comm]
    · exact Finset.sum_congr rfl fun _ _ => by ring

variable {ι : Type} [Fintype ι] {m : ι → ℕ} (ρ : PolyRep m)

theorem PolyRep.conn_ev {G : E → Mat m ℂ} {u : E} (h : ∀ τ, MContDiffAt 1 (fun w => G w τ) u)
    (hu : ∀ τ, (G u τ).det ≠ 0) (ξ : E) :
    conn (fun w => ρ.ev (G w)) u ξ = ρ.lie (fun τ => conn (fun w => G w τ) u ξ) := by
  set B : Mat m ℂ := (fun τ => (G u τ)ᵀ)⁻¹ with hB
  have hBu : B * (fun τ => (G u τ)ᵀ) = 1 := Mat.inv_mul fun τ => by rw [Matrix.det_transpose]; exact hu τ
  have hev : ∀ w, ρ.ev (B * fun τ => (G w τ)ᵀ) = ρ.ev B * (ρ.ev (G w))ᵀ := fun w => by
    rw [PolyRep.ev, ρ.mul, ρ.transp]; rfl
  have hinv : (ρ.ev (G u))ᵀ⁻¹ = ρ.ev B :=
    Matrix.inv_eq_left_inv (by rw [← hev, hBu]; exact ρ.one ℂ)
  have hρ : MContDiffAt 1 (fun w => ρ.ev (G w)) u := fun i j =>
    contDiffAt_aeval_int (f := fun w (v : EntIx m) => G w v.1 v.2.1 v.2.2) (fun v => h v.1 v.2.1 v.2.2) _
  have hK : ∀ τ, MContDiffAt 1 (fun w => B τ * (G w τ)ᵀ) u := fun τ =>
    (mContDiffAt_const _).mul (h τ).transpose
  have e1 : conn (fun w => ρ.ev (G w)) u ξ = mdel (fun w => ρ.ev (B * fun τ => (G w τ)ᵀ)) u ξ := by
    simp only [hev]
    rw [mdel_mul (mContDiffAt_const _) hρ.transpose, mdel_const, Matrix.zero_mul, add_zero, conn, hinv]
    rfl
  have e2 : ∀ τ, conn (fun w => G w τ) u ξ = mdel (fun w => B τ * (G w τ)ᵀ) u ξ := fun τ => by
    rw [mdel_mul (mContDiffAt_const _) (h τ).transpose, mdel_const, Matrix.zero_mul, add_zero, conn]
    rfl
  rw [e1]
  simp only [e2]
  ext i j
  refine (del_aeval_int (f := fun w (v : EntIx m) => (B * fun τ => (G w τ)ᵀ : Mat m ℂ) v.1 v.2.1 v.2.2)
    (fun v => hK v.1 v.2.1 v.2.2) (ρ.ent i j) ξ).trans ?_
  rw [hBu]
  rfl

theorem PolyRep.mdbar_lie {A : E → Mat m ℂ} {u : E} (h : ∀ τ, MContDiffAt 1 (fun w => A w τ) u) (η : E) :
    mdbar (fun w => ρ.lie (A w)) u η = ρ.lie (fun τ => mdbar (fun w => A w τ) u η) := by
  ext i j
  simp only [mdbar_apply, PolyRep.lie, Matrix.of_apply]
  rw [dbar_sum fun v _ => (differentiableAt_const _).fun_mul ((h v.1).diff v.2.1 v.2.2),
    ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [dbar_mul (differentiableAt_const _) ((h v.1).diff v.2.1 v.2.2)]
  simp

theorem PolyRep.eventually_conn_ev {G : E → Mat m ℂ} {v : E} (h : ∀ τ, MContDiffAt 2 (fun w => G w τ) v)
    (hv : ∀ τ, (G v τ).det ≠ 0) :
    ∀ᶠ u in 𝓝 v, ∀ ξ, conn (fun w => ρ.ev (G w)) u ξ = ρ.lie (fun τ => conn (fun w => G w τ) u ξ) := by
  filter_upwards [eventually_all.2 fun τ => (h τ).eventually_two,
    eventually_all.2 fun τ => (h τ).eventually_isUnit (hv τ).isUnit] with u h1 h2 ξ
  exact ρ.conn_ev (fun τ => (h1 τ).of_le one_le_two) (fun τ => (h2 τ).ne_zero) ξ

theorem PolyRep.curv_ev {G : E → Mat m ℂ} {v : E} (h : ∀ τ, MContDiffAt 2 (fun w => G w τ) v)
    (hv : ∀ τ, (G v τ).det ≠ 0) (ξ η : E) :
    curv (fun w => ρ.ev (G w)) v ξ η = ρ.lie (fun τ => curv (fun w => G w τ) v ξ η) := by
  rw [curv, mdbar_congr ((ρ.eventually_conn_ev h hv).mono fun u hu => hu ξ),
    ρ.mdbar_lie (A := fun u τ => conn (fun w => G w τ) u ξ)
      (fun τ => (h τ).conn (hv τ).isUnit (by norm_num) ξ)]
  ext i j
  simp [PolyRep.lie, curv]

end General

theorem PolyRep.lie_sum_C_mul_X {ι κ : Type} [Fintype ι] [Fintype κ] {m : ι → ℕ} (ρ : PolyRep m)
    (F : κ → κ → Mat m ℂ) :
    (Matrix.of fun i j => ∑ a, ∑ b, C (ρ.lie (F a b) i j) * X (a, b) : Matrix _ _ (MvPolynomial (κ × κ) ℂ)) =
      ρ.lie fun τ => Matrix.of fun i j => ∑ a, ∑ b, C (F a b τ i j) * X (a, b) := by
  have hc : ∀ (S : Type) [CommRing S] (φ : ℂ →+* S) (P : MvPolynomial (EntIx m) ℤ),
      aeval (fun w : EntIx m => (1 : Mat m S) w.1 w.2.1 w.2.2) P =
        φ (aeval (fun w : EntIx m => (1 : Mat m ℂ) w.1 w.2.1 w.2.2) P) := fun S _ φ P => by
    induction P using MvPolynomial.induction_on with
    | C a => rw [aeval_C, aeval_C, eq_intCast, eq_intCast, map_intCast]
    | add p q hp hq => rw [map_add, map_add, map_add, hp, hq]
    | mul_X p s hp =>
      rw [map_mul, map_mul, map_mul, hp, aeval_X, aeval_X, Pi.one_apply, Pi.one_apply, Matrix.one_apply,
        Matrix.one_apply]
      split_ifs
      · rw [map_one]
      · rw [map_zero]
  refine Matrix.ext fun i j => ?_
  have key : ∀ (c : EntIx m → ℂ) (f : κ → κ → EntIx m → ℂ),
      (∑ a, ∑ b, C (∑ v, c v * f a b v) * X (a, b) : MvPolynomial (κ × κ) ℂ) =
        ∑ v, C (c v) * ∑ a, ∑ b, C (f a b v) * X (a, b) := fun c f => by
    simp only [map_sum, map_mul, Finset.sum_mul, Finset.mul_sum, mul_assoc]
    rw [eq_comm, Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_comm
  simp only [PolyRep.lie, Matrix.of_apply]
  rw [key]
  exact Finset.sum_congr rfl fun v _ => by rw [hc _ C]

theorem conn_curvPoly_ev : ∀ (ι : Type) [Fintype ι] (m : ι → ℕ) (ρ : PolyRep m) (n : ℕ) (G : V n → Mat m ℂ) (v : V n),
    (∀ τ, MContDiffAt 2 (fun u => G u τ) v) → (∀ τ, (G v τ).det ≠ 0) →
    (∀ᶠ u in nhds v, ∀ ξ, conn (fun w => ρ.ev (G w)) u ξ = ρ.lie (fun τ => conn (fun w => G w τ) u ξ)) ∧
      curvPoly (fun w => ρ.ev (G w)) v = ρ.lie (fun τ => curvPoly (fun w => G w τ) v) := by
  intro ι _ m ρ n G v h hv
  refine ⟨ρ.eventually_conn_ev h hv, ?_⟩
  simp only [curvPoly, ρ.curv_ev h hv]
  exact ρ.lie_sum_C_mul_X fun a b τ => curv (fun w => G w τ) v (coordVec a) (coordVec b)

end GlobalTheory.GoodMetric

end
