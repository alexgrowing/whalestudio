import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DBoundA

noncomputable section

open Matrix Topology Filter
open scoped ComplexOrder

namespace PositivityTheory.Rg.Sw.Glob

def DBoundPQ : Prop :=
  ∀ (m n : ℕ) (ε : Fin m → Bool) (t c : ℝ) (e : ℤ) (p q : ℕ) (X : Fin n → ℝ), 0 < c → |t| = c →
    (∀ y u, DifferentiableOn ℂ (fun z => famPQ ε t c e p q y X z u) (stripS X)) ∧
    ContinuousOn (fun p' : GR n × ℂ × (Fin m → Fin n → ℂ) => famPQ ε t c e p q p'.1 X p'.2.1 p'.2.2)
      (Set.univ ×ˢ (stripS X ×ˢ Set.univ)) ∧
    ∀ (y₀ : GR n) (z₀ : ℂ), z₀ ∈ stripS X → ∃ (N : Set (GR n × ℂ)) (δ C : ℝ), N ∈ 𝓝 (y₀, z₀) ∧ 0 < δ ∧
      ∀ p' ∈ N, p'.2 ∈ stripS X → ∀ u, ‖famPQ ε t c e p q p'.1 X p'.2 u‖ ≤ C * Real.exp (-(δ * ∑ a, ∑ j, ‖u a j‖ ^ 2))

namespace DBoundBH

open DBoundH DBoundAH

variable {n : ℕ}

theorem isOpen_stripS (X : Fin n → ℝ) : IsOpen (stripS X) := by
  have : stripS X = ⋂ j, {z : ℂ | |z.im * X j| < Real.pi / 4} := by ext z; simp [stripS]
  rw [this]
  exact isOpen_iInter_of_finite fun j =>
    isOpen_lt ((continuous_abs.comp (Complex.continuous_im.mul continuous_const))) continuous_const

private theorem entC_mR_mul_aC_univ_prod_stripS (X : Fin n → ℝ) :
    EntC (Set.univ ×ˢ stripS X) (fun p : GR n × ℂ => mR p.1 * aC X p.2) := by
  apply entC_mul
  · intro i j
    exact (Continuous.matrix_elem (mR_cont.comp continuous_fst) i j).continuousOn
  · intro i j
    apply Continuous.continuousOn
    rcases i with i | i <;> rcases j with j | j <;>
      by_cases h : i = j <;> simp [aC, Matrix.diagonal_apply, h] <;> fun_prop

theorem ptZ_entC (X : Fin n → ℝ) (s : ℂ) (hs : s = Complex.I ∨ s = -Complex.I) :
    EntC (Set.univ ×ˢ stripS X) (fun p : GR n × ℂ => ptZ p.1 X p.2 s) := by
  have hM := entC_mR_mul_aC_univ_prod_stripS X
  have h11 : EntC (Set.univ ×ˢ stripS X) (fun p : GR n × ℂ => (mR p.1 * aC X p.2).toBlocks₁₁) :=
    fun i j => hM (Sum.inl i) (Sum.inl j)
  have h12 : EntC (Set.univ ×ˢ stripS X) (fun p : GR n × ℂ => (mR p.1 * aC X p.2).toBlocks₁₂) :=
    fun i j => hM (Sum.inl i) (Sum.inr j)
  have h21 : EntC (Set.univ ×ˢ stripS X) (fun p : GR n × ℂ => (mR p.1 * aC X p.2).toBlocks₂₁) :=
    fun i j => hM (Sum.inr i) (Sum.inl j)
  have h22 : EntC (Set.univ ×ˢ stripS X) (fun p : GR n × ℂ => (mR p.1 * aC X p.2).toBlocks₂₂) :=
    fun i j => hM (Sum.inr i) (Sum.inr j)
  have hden : ∀ p ∈ Set.univ ×ˢ stripS X,
      ((mR p.1 * aC X p.2).toBlocks₂₁ * s • 1 + (mR p.1 * aC X p.2).toBlocks₂₂).det ≠ 0 := by
    intro p hp
    rcases hs with rfl | rfl
    · exact (dSieg n p.1 X p.2 hp.2).2.2.1
    · exact (dSieg n p.1 X p.2 hp.2).2.2.2
  exact entC_mul (entC_add (entC_mul h11 (entC_const _ _)) h12)
    (entC_inv (entC_add (entC_mul h21 (entC_const _ _)) h22) hden)

private theorem entC_toBlocks_smul_add_univ_prod_stripS (X : Fin n → ℝ) (s : ℂ) :
    EntC (Set.univ ×ˢ stripS X) (fun p : GR n × ℂ =>
      (mR p.1 * aC X p.2).toBlocks₂₁ * s • 1 + (mR p.1 * aC X p.2).toBlocks₂₂) := by
  have hM := entC_mR_mul_aC_univ_prod_stripS X
  have h21 : EntC (Set.univ ×ˢ stripS X) (fun p : GR n × ℂ => (mR p.1 * aC X p.2).toBlocks₂₁) :=
    fun i j => hM (Sum.inr i) (Sum.inl j)
  have h22 : EntC (Set.univ ×ˢ stripS X) (fun p : GR n × ℂ => (mR p.1 * aC X p.2).toBlocks₂₂) :=
    fun i j => hM (Sum.inr i) (Sum.inr j)
  exact entC_add (entC_mul h21 (entC_const _ _)) h22

theorem jC_contOn (X : Fin n → ℝ) (e : ℤ) (p q : ℕ) :
    ContinuousOn (fun p' : GR n × ℂ => jC e p q p'.1 X p'.2) (Set.univ ×ˢ stripS X) := by
  have h0 : ContinuousOn (fun x : GR n × ℂ => (mR x.1 * aC X x.2).det ^ e) (Set.univ ×ˢ stripS X) :=
    (det_cont (entC_mR_mul_aC_univ_prod_stripS X)).zpow₀ _ fun x _ => Or.inl (det_bigM_ne x.1 X x.2)
  have h1 : ContinuousOn (fun x : GR n × ℂ =>
      ((mR x.1 * aC X x.2).toBlocks₂₁ * Complex.I • 1 + (mR x.1 * aC X x.2).toBlocks₂₂).det ^ (-(p : ℤ)))
      (Set.univ ×ˢ stripS X) :=
    (det_cont (entC_toBlocks_smul_add_univ_prod_stripS X Complex.I)).zpow₀ _ fun x hx => Or.inl (dSieg n x.1 X x.2 hx.2).2.2.1
  have h2 : ContinuousOn (fun x : GR n × ℂ =>
      ((mR x.1 * aC X x.2).toBlocks₂₁ * -Complex.I • 1 + (mR x.1 * aC X x.2).toBlocks₂₂).det ^ (-(q : ℤ)))
      (Set.univ ×ˢ stripS X) :=
    (det_cont (entC_toBlocks_smul_add_univ_prod_stripS X (-Complex.I))).zpow₀ _ fun x hx => Or.inl (dSieg n x.1 X x.2 hx.2).2.2.2
  exact (h0.mul h1).mul h2

private theorem re_I_mul_ofReal_mul_eq_neg_mul_im (c : ℝ) (w : ℂ) : (Complex.I * c * w).re = -(c * w.im) := by
  simp [Complex.mul_re, Complex.mul_im]

private theorem sum_norm_sq_rowC_eq_sum_norm_sq {m : ℕ} (u : Fin m → Fin n → ℂ) (a : Fin m) :
    ∑ j, ‖rowC u a j‖ ^ 2 = ∑ j, ‖u a j‖ ^ 2 := by
  simp [rowC, norm_star]

theorem re_bound {m : ℕ} (ε : Fin m → Bool) (t c : ℝ) (hc : 0 < c) (Z Z' : Matrix (Fin n) (Fin n) ℂ)
    (δ₁ δ₂ : ℝ) (hδ₁ : 0 < δ₁) (hδ₂ : 0 < δ₂)
    (h1 : ∀ w : Fin n → ℂ, δ₁ * ∑ j, ‖w j‖ ^ 2 ≤ (star w ⬝ᵥ (((-(Complex.I / 2)) • (Z - Zᴴ)) *ᵥ w)).re)
    (h2 : ∀ w : Fin n → ℂ, δ₂ * ∑ j, ‖w j‖ ^ 2 ≤ (star w ⬝ᵥ (((-(Complex.I / 2)) • (Z'ᴴ - Z')) *ᵥ w)).re)
    (u : Fin m → Fin n → ℂ) :
    (Complex.I * c * (Z * gramB (epsT t ε) true u).trace - Complex.I * c * (Z' * gramB (epsT t ε) false u).trace).re ≤
      -(c * min δ₁ δ₂ * ∑ a, ∑ j, ‖u a j‖ ^ 2) := by
  set S : Fin m → ℝ := fun a => ∑ j, ‖u a j‖ ^ 2 with hSdef
  have hS : ∀ a, 0 ≤ S a := fun a => by positivity
  have hT : ∀ a, c * min δ₁ δ₂ * S a ≤
      c * (star (rowC u a) ⬝ᵥ Z *ᵥ rowC u a).im := by
    intro a
    have e1 := h1 (rowC u a)
    rw [sum_norm_sq_rowC_eq_sum_norm_sq, ← im_eq_re] at e1
    have hm : min δ₁ δ₂ * S a ≤ δ₁ * S a := mul_le_mul_of_nonneg_right (min_le_left _ _) (hS a)
    have := mul_le_mul_of_nonneg_left e1 hc.le
    have := mul_le_mul_of_nonneg_left hm hc.le
    simp only [hSdef] at *
    nlinarith
  have hF : ∀ a, c * min δ₁ δ₂ * S a ≤
      -(c * (star (rowC u a) ⬝ᵥ Z' *ᵥ rowC u a).im) := by
    intro a
    have e2 := h2 (rowC u a)
    have hflip : (star (rowC u a) ⬝ᵥ (-(Complex.I / 2) • (Z'ᴴ - Z')) *ᵥ rowC u a)
        = -(star (rowC u a) ⬝ᵥ (-(Complex.I / 2) • (Z' - Z'ᴴ)) *ᵥ rowC u a) := by
      rw [← neg_sub Z' Z'ᴴ, smul_neg, Matrix.neg_mulVec, dotProduct_neg]
    rw [hflip, Complex.neg_re, ← im_eq_re, sum_norm_sq_rowC_eq_sum_norm_sq] at e2
    have hm : min δ₁ δ₂ * S a ≤ δ₂ * S a := mul_le_mul_of_nonneg_right (min_le_right _ _) (hS a)
    have := mul_le_mul_of_nonneg_left e2 hc.le
    have := mul_le_mul_of_nonneg_left hm hc.le
    simp only [hSdef] at *
    nlinarith
  have hsplit : ∑ a, S a = ∑ a with epsT t ε a = true, S a + ∑ a with epsT t ε a = false, S a := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun a => epsT t ε a = true) S]
    simp only [Bool.not_eq_true]
  rw [trace_gramB, trace_gramB, Finset.mul_sum, Finset.mul_sum, Complex.sub_re, Complex.re_sum,
    Complex.re_sum]
  simp only [re_I_mul_ofReal_mul_eq_neg_mul_im]
  have A : ∑ a with epsT t ε a = true, c * min δ₁ δ₂ * S a ≤
      ∑ a with epsT t ε a = true, c * (star (rowC u a) ⬝ᵥ Z *ᵥ rowC u a).im :=
    Finset.sum_le_sum fun a _ => hT a
  have B : ∑ a with epsT t ε a = false, c * min δ₁ δ₂ * S a ≤
      ∑ a with epsT t ε a = false, -(c * (star (rowC u a) ⬝ᵥ Z' *ᵥ rowC u a).im) :=
    Finset.sum_le_sum fun a _ => hF a
  rw [← Finset.mul_sum] at A B
  rw [Finset.sum_neg_distrib] at B ⊢
  rw [Finset.sum_neg_distrib]
  have hall : ∑ a, ∑ j, ‖u a j‖ ^ 2 = ∑ a, S a := rfl
  rw [hall, hsplit]
  nlinarith

end DBoundBH

open DBoundH DBoundAH DBoundBH in
theorem dBoundPQ : DBoundPQ := by
  intro m n ε t c e p q X hc _
  refine ⟨fun y u => famPQ_holo ε t c e p q X y u, famPQ_cont ε t c e p q X, ?_⟩
  intro y₀ z₀ hz₀
  have hopen : IsOpen (Set.univ ×ˢ stripS X : Set (GR n × ℂ)) := isOpen_univ.prod (isOpen_stripS X)
  have hmem : Set.univ ×ˢ stripS X ∈ 𝓝 ((y₀, z₀) : GR n × ℂ) := hopen.mem_nhds ⟨trivial, hz₀⟩
  have cZ : ∀ s : ℂ, (s = Complex.I ∨ s = -Complex.I) → ∀ i j,
      ContinuousAt (fun x : GR n × ℂ => ptZ x.1 X x.2 s i j) (y₀, z₀) :=
    fun s hs i j => (ptZ_entC X s hs i j).continuousAt hmem
  obtain ⟨δ₁, hδ₁, ev1⟩ := posDef_unif (p₀ := ((y₀, z₀) : GR n × ℂ))
    (fun x : GR n × ℂ => (-(Complex.I / 2)) • (ptZ x.1 X x.2 Complex.I - (ptZ x.1 X x.2 Complex.I)ᴴ))
    (fun i j => by
      simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.conjTranspose_apply, smul_eq_mul]
      exact continuousAt_const.mul ((cZ _ (Or.inl rfl) i j).sub (cZ _ (Or.inl rfl) j i).star))
    (dSieg n y₀ X z₀ hz₀).1
  have hpd2 : ((-(Complex.I / 2)) • ((ptZ y₀ X z₀ (-Complex.I))ᴴ - ptZ y₀ X z₀ (-Complex.I))).PosDef := by
    have h := (dSieg n y₀ X z₀ hz₀).2.1
    unfold IsSiegel at h
    rwa [Matrix.conjTranspose_conjTranspose] at h
  obtain ⟨δ₂, hδ₂, ev2⟩ := posDef_unif (p₀ := ((y₀, z₀) : GR n × ℂ))
    (fun x : GR n × ℂ => (-(Complex.I / 2)) • ((ptZ x.1 X x.2 (-Complex.I))ᴴ - ptZ x.1 X x.2 (-Complex.I)))
    (fun i j => by
      simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.conjTranspose_apply, smul_eq_mul]
      exact continuousAt_const.mul ((cZ _ (Or.inr rfl) j i).star.sub (cZ _ (Or.inr rfl) i j)))
    hpd2
  have evJ : ∀ᶠ x in 𝓝 ((y₀, z₀) : GR n × ℂ),
      ‖jC e p q x.1 X x.2‖ < ‖jC e p q y₀ X z₀‖ + 1 :=
    ((jC_contOn X e p q).continuousAt hmem).norm.eventually_lt continuousAt_const (lt_add_one _)
  obtain ⟨N, hN, hNp⟩ := (ev1.and (ev2.and evJ)).exists_mem
  refine ⟨N, c * min δ₁ δ₂, ‖jC e p q y₀ X z₀‖ + 1, hN, by positivity, ?_⟩
  intro x hx _ u
  obtain ⟨b1, b2, bJ⟩ := hNp x hx
  have hr := re_bound ε t c hc (ptZ x.1 X x.2 Complex.I) (ptZ x.1 X x.2 (-Complex.I)) δ₁ δ₂ hδ₁ hδ₂ b1 b2 u
  show ‖jC e p q x.1 X x.2 * gC ε t c (ptZ x.1 X x.2 Complex.I) (ptZ x.1 X x.2 (-Complex.I)) u‖ ≤ _
  rw [norm_mul, gC, Complex.norm_exp]
  exact mul_le_mul bJ.le (Real.exp_le_exp.2 hr) (Real.exp_pos _).le (by positivity)

theorem dBound : DBound := by
  intro m n ε t c e X hc ht
  exact dBoundPQ m n ε t c e (cnt (epsT t ε) true) (cnt (epsT t ε) false) X hc ht

end PositivityTheory.Rg.Sw.Glob
