import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.AwayInB

noncomputable section

open scoped Matrix ComplexConjugate SchwartzMap ComplexOrder
open Matrix

namespace PositivityTheory.Rg.Sw.Glob.AwayPf

theorem diag_eq {m n : ℕ} (A : Matrix (Fin m) (Fin m) ℂ) (M : Matrix (Fin m) (Fin n) ℂ) (j : Fin n) :
    (Mᴴ * A * M) j j = star (fun a => M a j) ⬝ᵥ (A *ᵥ fun a => M a j) := by
  simp only [Matrix.mul_apply, dotProduct, mulVec, Matrix.conjTranspose_apply, Pi.star_apply, Finset.mul_sum,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
  ring

theorem tr_re_nonneg {m n : ℕ} {A : Matrix (Fin m) (Fin m) ℂ} (hA : A.PosDef) (M : Matrix (Fin m) (Fin n) ℂ) :
    0 ≤ (trace (Mᴴ * A * M)).re ∧ (M ≠ 0 → 0 < (trace (Mᴴ * A * M)).re) := by
  have hsum : (trace (Mᴴ * A * M)).re = ∑ j, (star (fun a => M a j) ⬝ᵥ (A *ᵥ fun a => M a j)).re := by
    rw [Matrix.trace, Complex.re_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Matrix.diag_apply, diag_eq]
  have hnn : ∀ j, 0 ≤ (star (fun a => M a j) ⬝ᵥ (A *ᵥ fun a => M a j)).re := by
    intro j
    by_cases hv : (fun a => M a j) = 0
    · rw [hv]
      simp
    · exact (hA.re_dotProduct_pos hv).le
  refine ⟨hsum ▸ Finset.sum_nonneg (fun j _ => hnn j), fun hM => ?_⟩
  obtain ⟨j, hj⟩ : ∃ j, (fun a => M a j) ≠ 0 := by
    by_contra hc
    push_neg at hc
    apply hM
    ext a j
    exact congrFun (hc j) a
  rw [hsum]
  exact Finset.sum_pos' (fun j _ => hnn j) ⟨j, Finset.mem_univ _, hA.re_dotProduct_pos hj⟩

theorem tr_re_symm {m n : ℕ} {A : Matrix (Fin m) (Fin m) ℂ} (hA : A.IsHermitian) (M N : Matrix (Fin m) (Fin n) ℂ) :
    (trace (Mᴴ * A * N)).re = (trace (Nᴴ * A * M)).re := by
  have h : (Mᴴ * A * N)ᴴ = Nᴴ * A * M := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hA.eq,
      Matrix.mul_assoc]
  rw [← h, Matrix.trace_conjTranspose]
  simp

theorem tr_im_zero {m n : ℕ} {A : Matrix (Fin m) (Fin m) ℂ} (hA : A.IsHermitian) (M : Matrix (Fin m) (Fin n) ℂ) :
    trace (Mᴴ * A * M) = ((trace (Mᴴ * A * M)).re : ℂ) := by
  have h : star (trace (Mᴴ * A * M)) = trace (Mᴴ * A * M) := by
    rw [← Matrix.trace_conjTranspose]
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hA.eq, Matrix.mul_assoc]
  have him : (trace (Mᴴ * A * M)).im = 0 := by
    have := congrArg Complex.im h
    simp at this
    linarith
  apply Complex.ext <;> simp [him]

section
variable {T : Type} [Fintype T] [DecidableEq T] {m n : ℕ} (τ : T)

def qf (A : T → Matrix (Fin m) (Fin m) ℂ) (w : T → ℝ) (b b' : Bsp τ m n) : ℝ :=
  ∑ t : {τ' : T // τ' ≠ τ}, w t.1 * (trace ((of (b t))ᴴ * A t.1 * of (b' t))).re

def Qf (A : T → Matrix (Fin m) (Fin m) ℂ) (w : T → ℝ) : LinearMap.BilinForm ℝ (Bsp τ m n) :=
  LinearMap.mk₂ ℝ (fun b b' => 2 * qf τ A w b b')
    (fun b₁ b₂ b' => by
      simp only [qf, ← mul_add, ← Finset.sum_add_distrib]
      congr 1
      refine Finset.sum_congr rfl (fun t _ => ?_)
      congr 1
      rw [← Complex.add_re, ← Matrix.trace_add, ← Matrix.add_mul, ← Matrix.add_mul, ← Matrix.conjTranspose_add]
      rfl)
    (fun r b b' => by
      simp only [qf, Finset.mul_sum, smul_eq_mul]
      refine Finset.sum_congr rfl (fun t _ => ?_)
      have : (of ((r • b) t))ᴴ = (r : ℂ) • (of (b t))ᴴ := by
        rw [show of ((r • b) t) = (r : ℂ) • of (b t) from by ext i j; simp [Complex.real_smul]]
        rw [Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal]
      rw [this, Matrix.smul_mul, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul]
      ring)
    (fun b b₁ b₂ => by
      simp only [qf, ← mul_add, ← Finset.sum_add_distrib]
      congr 1
      refine Finset.sum_congr rfl (fun t _ => ?_)
      congr 1
      rw [← Complex.add_re, ← Matrix.trace_add, ← Matrix.mul_add]
      rfl)
    (fun r b b' => by
      simp only [qf, Finset.mul_sum, smul_eq_mul]
      refine Finset.sum_congr rfl (fun t _ => ?_)
      have : of ((r • b') t) = (r : ℂ) • of (b' t) := by ext i j; simp [Complex.real_smul]
      rw [this, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul]
      ring)

theorem Qf_apply (A : T → Matrix (Fin m) (Fin m) ℂ) (w : T → ℝ) (b b' : Bsp τ m n) :
    Qf τ A w b b' = 2 * qf τ A w b b' := rfl

theorem Qf_symm (A : T → Matrix (Fin m) (Fin m) ℂ) (hA : ∀ t, t ≠ τ → (A t).IsHermitian) (w : T → ℝ)
    (b b' : Bsp τ m n) : Qf τ A w b b' = Qf τ A w b' b := by
  rw [Qf_apply, Qf_apply]
  congr 1
  unfold qf
  refine Finset.sum_congr rfl (fun t _ => ?_)
  rw [tr_re_symm (hA t.1 t.2)]

theorem Qf_pos (A : T → Matrix (Fin m) (Fin m) ℂ) (hA : ∀ t, t ≠ τ → (A t).PosDef) (w : T → ℝ)
    (hw : ∀ t, t ≠ τ → 0 < w t) (b : Bsp τ m n) (hb : b ≠ 0) : 0 < Qf τ A w b b := by
  rw [Qf_apply]
  have hnn : ∀ t : {τ' : T // τ' ≠ τ}, 0 ≤ w t.1 * (trace ((of (b t))ᴴ * A t.1 * of (b t))).re :=
    fun t => mul_nonneg (hw t.1 t.2).le (tr_re_nonneg (hA t.1 t.2) _).1
  obtain ⟨t, ht⟩ : ∃ t, b t ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hb (funext hc)
  have hof : of (b t) ≠ 0 := by
    intro h0
    apply ht
    funext i j
    exact congrFun (congrFun h0 i) j
  have hpos : 0 < qf τ A w b b :=
    Finset.sum_pos' (fun t _ => hnn t)
      ⟨t, Finset.mem_univ _, mul_pos (hw t.1 t.2) ((tr_re_nonneg (hA t.1 t.2) _).2 hof)⟩
  linarith

theorem exists_gauss (A : T → Matrix (Fin m) (Fin m) ℂ) (hA : ∀ t, t ≠ τ → (A t).PosDef) (w : T → ℝ)
    (hw : ∀ t, t ≠ τ → 0 < w t) :
    ∃ G : 𝓢(Bsp τ m n, ℂ), ∀ b, G b = Complex.exp (-(Real.pi : ℂ) * ((2 * qf τ A w b b : ℝ) : ℂ)) := by
  obtain ⟨G, hG⟩ := GlobalTheory.ThK.EvAt0.GaussForm.exists_schwartz_gauss_form (Qf τ A w)
    (Qf_symm τ A (fun t ht => (hA t ht).isHermitian) w) (fun b hb => Qf_pos τ A hA w hw b hb)
  refine ⟨G, fun b => ?_⟩
  rw [(hG b).1, Qf_apply]

end

end PositivityTheory.Rg.Sw.Glob.AwayPf
