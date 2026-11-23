import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.InfInvA

noncomputable section

open MeasureTheory Matrix Filter Topology
open scoped ContDiff ComplexConjugate

namespace PositivityTheory.Rg.Sw.LVs.II

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

def rmulL (x : M2 n) : M2 n →L[ℝ] M2 n :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => M * x
      map_add' := fun _ _ => Matrix.add_mul _ _ _
      map_smul' := fun c M => by simp }

theorem deriv_piece (Θ : M2 n → ℂ) (x : M2 n) (hΘ : DifferentiableAt ℂ Θ x)
    (γ : ℝ → M2 n) (Y : M2 n) (hγ : HasDerivAt γ Y 0) (hγ0 : γ 0 = 1)
    (f : ℝ → ℂ) (r : ℂ) (hf : HasDerivAt f r 0)
    (hlaw : ∀ᶠ t in 𝓝 (0 : ℝ), Θ (γ t * x) = f t * Θ x) :
    fderiv ℂ Θ x (Y * x) = r * Θ x := by
  have h1 : HasDerivAt (fun t => γ t * x) (Y * x) 0 := by
    have := (rmulL x).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hγ
    exact this
  have hx : γ 0 * x = x := by simp [hγ0]
  have hF : HasFDerivAt Θ ((fderiv ℂ Θ x).restrictScalars ℝ) (γ 0 * x) := by
    rw [hx]; exact hΘ.hasFDerivAt.restrictScalars ℝ
  have h2 : HasDerivAt (fun t => Θ (γ t * x)) (fderiv ℂ Θ x (Y * x)) 0 := by
    have := hF.comp_hasDerivAt (0 : ℝ) h1
    exact this
  have h3 : HasDerivAt (fun t => Θ (γ t * x)) (r * Θ x) 0 :=
    (hf.mul_const (Θ x)).congr_of_eventuallyEq hlaw
  exact h2.unique h3

theorem one_add_smul_fromBlocks (t : ℝ) (A B C D : Matrix (Fin n) (Fin n) ℂ) :
    (1 : M2 n) + t • fromBlocks A B C D = fromBlocks (1 + t • A) (t • B) (t • C) (1 + t • D) := by
  rw [← Matrix.fromBlocks_one, Matrix.fromBlocks_smul, Matrix.fromBlocks_add]; simp

theorem inG_one_add (P : M2 n) (h1 : Pᴴ * JJ n + JJ n * P = 0) (h2 : Pᴴ * JJ n * P = 0) (t : ℝ) :
    InG ((1 : M2 n) + t • P) := by
  unfold InG
  have key : ((1 : M2 n) + t • P)ᴴ * JJ n * (1 + t • P)
      = JJ n + t • (Pᴴ * JJ n + JJ n * P) + (t * t) • (Pᴴ * JJ n * P) := by
    rw [Matrix.conjTranspose_add, Matrix.conjTranspose_one, Matrix.conjTranspose_smul, star_trivial]
    simp only [add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, smul_add,
      smul_smul, Matrix.mul_assoc]
    abel
  rw [key, h1, h2]
  simp

theorem inG_fromBlocks_diag (a d : Matrix (Fin n) (Fin n) ℂ) (h1 : aᴴ * d = 1) (h2 : dᴴ * a = 1) :
    InG (fromBlocks a 0 0 d) := by
  unfold InG JJ
  rw [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp [h1, h2]

theorem det_one_add_smul_single_same (i : Fin n) (s : ℂ) :
    ((1 : Matrix (Fin n) (Fin n) ℂ) + s • Matrix.single i i 1).det = 1 + s := by
  have h : (1 : Matrix (Fin n) (Fin n) ℂ) + s • Matrix.single i i 1 =
      Matrix.diagonal (fun j => if j = i then 1 + s else 1) := by
    ext a b
    by_cases hab : a = b
    · subst hab
      by_cases hai : a = i
      · subst hai
        simp [Matrix.single_apply]
      · simp [Matrix.single_apply, hai, Ne.symm hai]
    · have hn : ¬ (i = a ∧ i = b) := fun h => hab (h.1.symm.trans h.2)
      simp [Matrix.single_apply, hn, hab, Matrix.one_apply_ne hab]
  rw [h, Matrix.det_diagonal]
  simp

def LawH (Θ : M2 n → ℂ) : Prop :=
  ∀ p x, InG p → p.toBlocks₂₁ = 0 → InG x → Θ (p * x) = ((‖(p.toBlocks₂₂).det‖ ^ (-(2 * (n : ℤ))) : ℝ) : ℂ) * Θ x

def lam (Y : M2 n) : ℂ := (n : ℂ) * (Y.toBlocks₁₁.trace - Y.toBlocks₂₂.trace)

theorem hasDerivAt_affine (P : M2 n) : HasDerivAt (fun t : ℝ => (1 : M2 n) + t • P) P 0 := by
  exact (((hasDerivAt_id (0 : ℝ)).smul_const P).const_add (1 : M2 n)).congr_deriv (one_smul ℝ P)

theorem pieceN (Θ : M2 n → ℂ) (hl : LawH Θ) (x : M2 n) (hx : InG x) (hd : DifferentiableAt ℂ Θ x)
    (β : Matrix (Fin n) (Fin n) ℂ) (hβ : βᴴ = β) :
    fderiv ℂ Θ x (fromBlocks 0 β 0 0 * x) = lam (fromBlocks 0 β 0 0) * Θ x := by
  have hc1 : (fromBlocks 0 β 0 0 : M2 n)ᴴ * JJ n + JJ n * fromBlocks 0 β 0 0 = 0 := by
    simp [JJ, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_add, hβ]
  have hc2 : (fromBlocks 0 β 0 0 : M2 n)ᴴ * JJ n * fromBlocks 0 β 0 0 = 0 := by
    simp [JJ, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, hβ]
  have key := deriv_piece Θ x hd (fun t : ℝ => 1 + t • (fromBlocks 0 β 0 0 : M2 n)) _
    (hasDerivAt_affine _) (by simp) (fun _ => (1 : ℂ)) 0 (hasDerivAt_const _ _)
    (Filter.Eventually.of_forall fun t => by
      have h21 : ((1 : M2 n) + t • (fromBlocks 0 β 0 0 : M2 n)).toBlocks₂₁ = 0 := by
        rw [one_add_smul_fromBlocks]
        simp
      rw [hl _ x (inG_one_add _ hc1 hc2 t) h21 hx, one_add_smul_fromBlocks]
      simp)
  rw [key]
  simp [lam]

def Pij (c : ℂ) (i j : Fin n) : M2 n := fromBlocks (c • Matrix.single i j 1) 0 0 (-(conj c) • Matrix.single j i 1)

theorem pieceOff (Θ : M2 n → ℂ) (hl : LawH Θ) (x : M2 n) (hx : InG x) (hd : DifferentiableAt ℂ Θ x)
    (c : ℂ) (i j : Fin n) (hij : i ≠ j) :
    fderiv ℂ Θ x (Pij c i j * x) = lam (Pij c i j) * Θ x := by
  have hc1 : (Pij c i j)ᴴ * JJ n + JJ n * Pij c i j = 0 := by
    simp [Pij, JJ, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_add,
      Matrix.conjTranspose_smul, Matrix.conjTranspose_single, Complex.star_def]
  have hc2 : (Pij c i j)ᴴ * JJ n * Pij c i j = 0 := by
    simp [Pij, JJ, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply,
      Matrix.conjTranspose_smul, Matrix.conjTranspose_single, Complex.star_def,
      Matrix.single_mul_single_of_ne, hij, Ne.symm hij]
  have hdet : ∀ t : ℝ, ((1 : Matrix (Fin n) (Fin n) ℂ) + t • (-(conj c) • Matrix.single j i 1)).det = 1 := by
    intro t
    rw [← smul_assoc, Matrix.smul_single, smul_eq_mul, mul_one]
    exact Matrix.det_transvection_of_ne j i (Ne.symm hij) _
  have key := deriv_piece Θ x hd (fun t : ℝ => 1 + t • Pij c i j) _
    (hasDerivAt_affine _) (by simp) (fun _ => (1 : ℂ)) 0 (hasDerivAt_const _ _)
    (Filter.Eventually.of_forall fun t => by
      have h21 : ((1 : M2 n) + t • Pij c i j).toBlocks₂₁ = 0 := by
        rw [Pij, one_add_smul_fromBlocks]
        simp
      rw [hl _ x (inG_one_add _ hc1 hc2 t) h21 hx, Pij, one_add_smul_fromBlocks,
        Matrix.toBlocks_fromBlocks₂₂, hdet]
      simp)
  rw [key]
  simp [lam, Pij, Matrix.trace_smul, Matrix.trace_single_eq_of_ne _ _ _ hij,
    Matrix.trace_single_eq_of_ne _ _ _ (Ne.symm hij)]

theorem one_add_smul_single_mul (i : Fin n) (u v : ℂ) :
    ((1 : Matrix (Fin n) (Fin n) ℂ) + u • Matrix.single i i 1) * (1 + v • Matrix.single i i 1) =
      1 + (u + v + u * v) • Matrix.single i i 1 := by
  simp only [add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, smul_add, smul_smul,
    Matrix.single_mul_single_same, add_smul]
  simp only [mul_comm v u]
  abel

private theorem one_add_smul_single_conjTranspose_mul_eq_one (a b : ℂ) (h : (1 + star a) * (1 + b) = 1) (i : Fin n) :
    ((1 : Matrix (Fin n) (Fin n) ℂ) + a • Matrix.single i i 1)ᴴ * (1 + b • Matrix.single i i 1) = 1 := by
  rw [Matrix.conjTranspose_add, Matrix.conjTranspose_one, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_single, star_one, one_add_smul_single_mul]
  have h0 : star a + b + star a * b = 0 := by linear_combination h
  rw [h0, zero_smul, add_zero]

theorem pieceDiag (Θ : M2 n → ℂ) (hl : LawH Θ) (x : M2 n) (hx : InG x) (hd : DifferentiableAt ℂ Θ x)
    (c : ℂ) (i : Fin n) :
    fderiv ℂ Θ x (Pij c i i * x) = lam (Pij c i i) * Θ x := by
  have e : ∀ w : ℂ, (1 : ℂ) + (w - 1) = w := fun w => by ring
  have hu : HasDerivAt (fun t : ℝ => Complex.exp (↑t * c) - 1) c 0 := by
    have h := (((hasDerivAt_id' (0 : ℝ)).ofReal_comp).mul_const c).cexp.sub_const 1
    exact h.congr_deriv (by simp)
  have hv : HasDerivAt (fun t : ℝ => Complex.exp (-↑t * conj c) - 1) (-(conj c)) 0 := by
    have h := (((hasDerivAt_id' (0 : ℝ)).ofReal_comp).neg.mul_const (conj c)).cexp.sub_const 1
    exact h.congr_deriv (by simp)
  have hγ : HasDerivAt (fun t : ℝ => (1 : M2 n) +
      ((Complex.exp (↑t * c) - 1) • (fromBlocks (Matrix.single i i 1) 0 0 0 : M2 n) +
        (Complex.exp (-↑t * conj c) - 1) • (fromBlocks 0 0 0 (Matrix.single i i 1) : M2 n)))
      (Pij c i i) 0 := by
    have h := ((hu.smul_const (fromBlocks (Matrix.single i i 1) 0 0 0 : M2 n)).add
      (hv.smul_const (fromBlocks 0 0 0 (Matrix.single i i 1) : M2 n))).const_add (1 : M2 n)
    refine h.congr_deriv ?_
    rw [Pij, Matrix.fromBlocks_smul, Matrix.fromBlocks_smul, Matrix.fromBlocks_add]
    simp
  have hform : ∀ t : ℝ, (1 : M2 n) +
      ((Complex.exp (↑t * c) - 1) • (fromBlocks (Matrix.single i i 1) 0 0 0 : M2 n) +
        (Complex.exp (-↑t * conj c) - 1) • (fromBlocks 0 0 0 (Matrix.single i i 1) : M2 n)) =
      fromBlocks (1 + (Complex.exp (↑t * c) - 1) • Matrix.single i i 1) 0 0
        (1 + (Complex.exp (-↑t * conj c) - 1) • Matrix.single i i 1) := by
    intro t
    rw [← Matrix.fromBlocks_one, Matrix.fromBlocks_smul, Matrix.fromBlocks_smul,
      Matrix.fromBlocks_add, Matrix.fromBlocks_add]
    simp
  have hG : ∀ t : ℝ, InG (fromBlocks (1 + (Complex.exp (↑t * c) - 1) • Matrix.single i i 1) 0 0
      (1 + (Complex.exp (-↑t * conj c) - 1) • Matrix.single i i 1) : M2 n) := by
    intro t
    apply inG_fromBlocks_diag
    · apply one_add_smul_single_conjTranspose_mul_eq_one
      rw [star_sub, star_one, e, e, Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add,
        show (conj (↑t * c) + -↑t * conj c : ℂ) = 0 by rw [map_mul, Complex.conj_ofReal]; ring,
        Complex.exp_zero]
    · apply one_add_smul_single_conjTranspose_mul_eq_one
      rw [star_sub, star_one, e, e, Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add,
        show (conj (-↑t * conj c) + ↑t * c : ℂ) = 0 by
          rw [map_mul, map_neg, Complex.conj_ofReal, Complex.conj_conj]; ring,
        Complex.exp_zero]
  have hf := (((hasDerivAt_id' (0 : ℝ)).const_mul (2 * (n : ℝ) * c.re)).exp).ofReal_comp
  have key := deriv_piece Θ x hd _ _ hγ (by simp) _ _ hf
    (Filter.Eventually.of_forall fun t => by
      have h21 : ((1 : M2 n) +
          ((Complex.exp (↑t * c) - 1) • (fromBlocks (Matrix.single i i 1) 0 0 0 : M2 n) +
            (Complex.exp (-↑t * conj c) - 1) • (fromBlocks 0 0 0 (Matrix.single i i 1) : M2 n))).toBlocks₂₁ = 0 := by
        rw [hform]
        simp
      rw [hl _ x (by rw [hform]; exact hG t) h21 hx, hform, Matrix.toBlocks_fromBlocks₂₂,
        det_one_add_smul_single_same, e, Complex.norm_exp]
      congr 2
      rw [← Real.rpow_intCast, ← Real.exp_mul]
      congr 1
      simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.ofReal_im, Complex.neg_im,
        Complex.conj_re, Complex.conj_im]
      push_cast
      ring)
  rw [key]
  congr 1
  simp [lam, Pij, Matrix.trace_smul]
  apply Complex.ext <;> simp <;> ring

theorem lam_add (Y Y' : M2 n) : lam (Y + Y') = lam Y + lam Y' := by
  have e1 : (Y + Y').toBlocks₁₁ = Y.toBlocks₁₁ + Y'.toBlocks₁₁ := by ext; rfl
  have e2 : (Y + Y').toBlocks₂₂ = Y.toBlocks₂₂ + Y'.toBlocks₂₂ := by ext; rfl
  simp only [lam, e1, e2, Matrix.trace_add]
  ring

theorem lam_smul (c : ℂ) (Y : M2 n) : lam (c • Y) = c * lam Y := by
  simp only [lam]
  have h1 : (c • Y).toBlocks₁₁ = c • Y.toBlocks₁₁ := by ext; simp [Matrix.toBlocks₁₁]
  have h2 : (c • Y).toBlocks₂₂ = c • Y.toBlocks₂₂ := by ext; simp [Matrix.toBlocks₂₂]
  rw [h1, h2, Matrix.trace_smul, Matrix.trace_smul]; simp only [smul_eq_mul]; ring

def Gen (n : ℕ) : Set (M2 n) :=
  {Y | (∃ β : Matrix (Fin n) (Fin n) ℂ, βᴴ = β ∧ Y = fromBlocks 0 β 0 0) ∨ ∃ c i j, Y = Pij c i j}

theorem sum_single_mem (W : Submodule ℂ (M2 n)) (Φ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] M2 n)
    (h : ∀ i j a, Φ (Matrix.single i j a) ∈ W) (M : Matrix (Fin n) (Fin n) ℂ) : Φ M ∈ W := by
  rw [Matrix.matrix_eq_sum_single M, map_sum]
  exact Submodule.sum_mem _ fun i _ => by rw [map_sum]; exact Submodule.sum_mem _ fun j _ => h i j _

def fb11 (n : ℕ) : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] M2 n where
  toFun A := fromBlocks A 0 0 0
  map_add' A B := by rw [Matrix.fromBlocks_add]; simp
  map_smul' c A := by rw [Matrix.fromBlocks_smul]; simp

def fb22 (n : ℕ) : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] M2 n where
  toFun A := fromBlocks 0 0 0 A
  map_add' A B := by rw [Matrix.fromBlocks_add]; simp
  map_smul' c A := by rw [Matrix.fromBlocks_smul]; simp

theorem mem_span_gen (Y : M2 n) (hY : Y.toBlocks₂₁ = 0) : Y ∈ Submodule.span ℂ (Gen n) := by
  have hE1 : ∀ i j (a : ℂ), (fromBlocks (Matrix.single i j a) 0 0 0 : M2 n) ∈ Submodule.span ℂ (Gen n) := by
    intro i j a
    have h : (fromBlocks (Matrix.single i j a) 0 0 0 : M2 n) =
        (a / 2) • (Pij 1 i j - Complex.I • Pij Complex.I i j) := by
      ext (p|p) (q|q)
      all_goals simp [Pij, Matrix.single_apply]
      all_goals split_ifs
      all_goals ring_nf
      all_goals simp [Complex.I_sq]
    rw [h]
    exact Submodule.smul_mem _ _ (Submodule.sub_mem _
      (Submodule.subset_span (Or.inr ⟨1, i, j, rfl⟩))
      (Submodule.smul_mem _ _ (Submodule.subset_span (Or.inr ⟨Complex.I, i, j, rfl⟩))))
  have hE2 : ∀ i j (a : ℂ), (fromBlocks 0 0 0 (Matrix.single i j a) : M2 n) ∈ Submodule.span ℂ (Gen n) := by
    intro i j a
    have h : (fromBlocks 0 0 0 (Matrix.single i j a) : M2 n) =
        (-a / 2) • (Pij 1 j i + Complex.I • Pij Complex.I j i) := by
      ext (p|p) (q|q)
      all_goals simp [Pij, Matrix.single_apply]
      all_goals split_ifs
      all_goals ring_nf
      all_goals simp [Complex.I_sq]
    rw [h]
    exact Submodule.smul_mem _ _ (Submodule.add_mem _
      (Submodule.subset_span (Or.inr ⟨1, j, i, rfl⟩))
      (Submodule.smul_mem _ _ (Submodule.subset_span (Or.inr ⟨Complex.I, j, i, rfl⟩))))
  have hA : ∀ A, fb11 n A ∈ Submodule.span ℂ (Gen n) :=
    sum_single_mem _ (fb11 n) (fun i j a => hE1 i j a)
  have hD : ∀ D, fb22 n D ∈ Submodule.span ℂ (Gen n) :=
    sum_single_mem _ (fb22 n) (fun i j a => hE2 i j a)
  have hB : ∀ B : Matrix (Fin n) (Fin n) ℂ, (fromBlocks 0 B 0 0 : M2 n) ∈ Submodule.span ℂ (Gen n) := by
    intro B
    have hH1 : ((1 / 2 : ℂ) • (B + Bᴴ))ᴴ = (1 / 2 : ℂ) • (B + Bᴴ) := by
      ext p q
      simp [Matrix.conjTranspose_apply]
      ring
    have hH2 : ((-Complex.I / 2) • (B - Bᴴ))ᴴ = (-Complex.I / 2) • (B - Bᴴ) := by
      ext p q
      simp [Matrix.conjTranspose_apply]
      ring
    have hsplit : (fromBlocks 0 B 0 0 : M2 n) = fromBlocks 0 ((1 / 2 : ℂ) • (B + Bᴴ)) 0 0 +
        Complex.I • fromBlocks 0 ((-Complex.I / 2) • (B - Bᴴ)) 0 0 := by
      ext (p|p) (q|q)
      all_goals simp
      ring_nf
      simp [Complex.I_sq]
      ring
    rw [hsplit]
    exact Submodule.add_mem _ (Submodule.subset_span (Or.inl ⟨_, hH1, rfl⟩))
      (Submodule.smul_mem _ _ (Submodule.subset_span (Or.inl ⟨_, hH2, rfl⟩)))
  have hYe : Y = fb11 n Y.toBlocks₁₁ + fromBlocks 0 Y.toBlocks₁₂ 0 0 + fb22 n Y.toBlocks₂₂ := by
    conv_lhs => rw [← Matrix.fromBlocks_toBlocks Y, hY]
    simp [fb11, fb22, Matrix.fromBlocks_add]
  rw [hYe]
  exact Submodule.add_mem _ (Submodule.add_mem _ (hA _) (hB _)) (hD _)

theorem lawDeriv : LawDeriv := by
  intro n Θ Ω hΩ hsub hdiff hlaw x hx Y hY
  have hd : DifferentiableAt ℂ Θ x := hdiff.differentiableAt (hΩ.mem_nhds (hsub hx))
  show fderiv ℂ Θ x (Y * x) = lam Y * Θ x
  refine Submodule.span_induction (p := fun Y _ => fderiv ℂ Θ x (Y * x) = lam Y * Θ x)
    ?_ ?_ ?_ ?_ (mem_span_gen Y hY)
  · intro Z hZ
    rcases hZ with ⟨β, hβ, rfl⟩ | ⟨c, i, j, rfl⟩
    · exact pieceN Θ hlaw x hx hd β hβ
    · by_cases hij : i = j
      · subst hij
        exact pieceDiag Θ hlaw x hx hd c i
      · exact pieceOff Θ hlaw x hx hd c i j hij
  · have h0 : lam (0 : M2 n) = 0 := by simpa using lam_smul 0 (0 : M2 n)
    rw [zero_mul, map_zero, h0, zero_mul]
  · intro a b _ _ ha hb
    rw [add_mul, map_add, ha, hb, lam_add, add_mul]
  · intro a b _ hb
    rw [smul_mul_assoc, map_smul, hb, lam_smul, smul_eq_mul, mul_assoc]

end PositivityTheory.Rg.Sw.LVs.II
