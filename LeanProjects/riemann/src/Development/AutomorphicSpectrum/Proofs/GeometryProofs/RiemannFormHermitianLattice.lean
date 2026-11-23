import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ExistsAdaptedUnimodular

open Filter Topology Matrix

namespace GlobalTheory.CompanionTheory.RiemannForm

theorem dot_mulVec_symm {g : ℕ} (A : Matrix (Fin g) (Fin g) ℝ) (hA : Aᵀ = A) (a b : Fin g → ℝ) :
    a ⬝ᵥ A *ᵥ b = (A *ᵥ a) ⬝ᵥ b := by
  have h : a ᵥ* A = A *ᵥ a := by rw [← vecMul_transpose, hA]
  rw [dotProduct_mulVec, h]

theorem exists_mulVec_eq_of_orthogonal_ker {g : ℕ} (A : Matrix (Fin g) (Fin g) ℝ) (hA : Aᵀ = A)
    (y : Fin g → ℝ) (hy : ∀ m, A *ᵥ m = 0 → y ⬝ᵥ m = 0) : ∃ w, A *ᵥ w = y := by
  by_contra hne
  have hnot : y ∉ LinearMap.range A.mulVecLin := by
    rintro ⟨w, hw⟩
    exact hne ⟨w, by simpa using hw⟩
  obtain ⟨φ, hφy, hφ⟩ := Submodule.exists_le_ker_of_notMem hnot
  let m : Fin g → ℝ := fun i => φ (fun j => if i = j then 1 else 0)
  have hφm : ∀ x, φ x = m ⬝ᵥ x := by
    intro x
    rw [LinearMap.pi_apply_eq_sum_univ φ x]
    simp only [dotProduct, smul_eq_mul, m]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hAm : A *ᵥ m = 0 := by
    apply dotProduct_eq_zero_iff.1 ?_
    intro w
    rw [← dot_mulVec_symm A hA, ← hφm]
    exact hφ ⟨w, by simp⟩
  exact hφy (by rw [hφm, dotProduct_comm]; exact hy m hAm)

theorem mem_span_integer_kernel {g : ℕ} (Bs : Matrix (Fin g) (Fin g) ℤ)
    (hB : (Bs.map (fun x : ℤ => (x : ℝ))).PosSemidef) (n : Fin g → ℝ)
    (hn : Bs.map (fun x : ℤ => (x : ℝ)) *ᵥ n = 0) :
    n ∈ Submodule.span ℝ {p : Fin g → ℝ | ∃ v : Fin g → ℤ, Bs *ᵥ v = 0 ∧ p = fun k => (v k : ℝ)} := by
  classical
  obtain ⟨r, s, e, Q, hQ, hz, hP⟩ :=
    ToricBasis.exists_adapted_unimodular g Unit (fun _ => Bs) (fun _ => hB)
  simp only [Finset.univ_unique, Finset.sum_const, Finset.card_singleton, one_smul] at hP
  have hz' := fun k l => (hz () k l).1
  have hz'' := fun k l => (hz () k l).2
  let Qr : Matrix (Fin g) (Fin g) ℝ := Q.map (fun x : ℤ => (x : ℝ))
  have hdet : IsUnit Qr.det := by
    have h : Qr.det = ((Q.det : ℤ) : ℝ) := by
      have := (Int.castRingHom ℝ).map_det Q
      simpa [RingHom.mapMatrix_apply] using this.symm
    rw [h]
    exact hQ.map (Int.castRingHom ℝ)
  let w := Qr⁻¹ *ᵥ n
  have hw : Qr *ᵥ w = n := by
    simp only [w, mulVec_mulVec, mul_nonsing_inv _ hdet, one_mulVec]
  let q : Fin r ⊕ Fin s → Fin g → ℤ := fun a i => Q i (e a)
  have hent : ∀ a c, ((Qᵀ * Bs * Q).submatrix e e) a c = q a ⬝ᵥ Bs *ᵥ q c := by
    intro a c
    rw [Matrix.mul_assoc]
    simp only [submatrix_apply, mul_apply, transpose_apply, q, dotProduct, mulVec]
  have hnsum : n = ∑ a, w (e a) • (fun i => (q a i : ℝ)) := by
    rw [← hw]
    funext i
    simp only [mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Qr, map_apply, q]
    rw [← Equiv.sum_comp e]
    exact Finset.sum_congr rfl fun a _ => mul_comm _ _
  have hcast : ∀ a c, (fun i => (q a i : ℝ)) ⬝ᵥ (Bs.map (fun x : ℤ => (x : ℝ))) *ᵥ (fun i => (q c i : ℝ))
      = ((q a ⬝ᵥ Bs *ᵥ q c : ℤ) : ℝ) := by
    intro a c
    simp [dotProduct, mulVec]
  let x : Fin r → ℝ := fun l => w (e (Sum.inl l))
  have hPx : ((((Qᵀ * Bs * Q).submatrix e e).toBlocks₁₁).map (fun x : ℤ => (x : ℝ))) *ᵥ x = 0 := by
    funext l
    have h0 : (fun i => (q (Sum.inl l) i : ℝ)) ⬝ᵥ (Bs.map (fun x : ℤ => (x : ℝ))) *ᵥ n = 0 := by
      rw [hn, dotProduct_zero]
    rw [hnsum, mulVec_sum, dotProduct_sum, Fintype.sum_sum_type] at h0
    simp only [mulVec_smul, dotProduct_smul, hcast, ← hent, smul_eq_mul, hz'', Int.cast_zero,
      mul_zero, Finset.sum_const_zero, add_zero] at h0
    simp only [mulVec, dotProduct, map_apply, toBlocks₁₁, of_apply, Pi.zero_apply]
    refine Eq.trans (Finset.sum_congr rfl fun a _ => ?_) h0
    simp only [x]
    ring
  have hx : x = 0 := by
    by_contra hx
    have := hP.dotProduct_mulVec_pos hx
    rw [hPx, dotProduct_zero] at this
    exact lt_irrefl _ this
  rw [hnsum, Fintype.sum_sum_type]
  have hl : ∀ l, w (e (Sum.inl l)) = 0 := fun l => congrFun hx l
  simp only [hl, zero_smul, Finset.sum_const_zero, zero_add]
  refine Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨q (Sum.inr k), ?_, rfl⟩)
  apply ToricBasis.mulVec_eq_zero_of_quad hB
  rw [← hent]
  exact hz' k _

theorem real_form {g : ℕ} (Br S Y : Matrix (Fin g) (Fin g) ℝ) (c : ℝ) (hc : 0 < c) (hS : Sᵀ = S)
    (hBr : Brᵀ = Br)
    (hpos : ∀ v, Br *ᵥ v = 0 → c * (v ⬝ᵥ v) ≤ v ⬝ᵥ Y *ᵥ v)
    (hSY : ∀ n, Br *ᵥ n = 0 → S *ᵥ (Y *ᵥ n) = n)
    (hBS : ∀ y, Br *ᵥ (S *ᵥ y) = 0) (y : Fin g → ℝ) :
    0 ≤ y ⬝ᵥ S *ᵥ y ∧ c * (y ⬝ᵥ S *ᵥ y) ≤ y ⬝ᵥ y ∧
      (y ⬝ᵥ S *ᵥ y = 0 → ∃ w, Br *ᵥ w = y) := by
  have hn := hBS y
  have h2 : y ⬝ᵥ S *ᵥ y = (S *ᵥ y) ⬝ᵥ Y *ᵥ (S *ᵥ y) := by
    rw [← dot_mulVec_symm S hS, hSY _ hn]
  have h3 := hpos _ hn
  rw [← h2] at h3
  have hself : ∀ a : Fin g → ℝ, 0 ≤ a ⬝ᵥ a := fun a =>
    Finset.sum_nonneg fun i _ => mul_self_nonneg _
  have hnn := hself (S *ᵥ y)
  have h4 := hself (y - c • (S *ᵥ y))
  have h5 : (y - c • (S *ᵥ y)) ⬝ᵥ (y - c • (S *ᵥ y)) =
      y ⬝ᵥ y - 2 * c * (y ⬝ᵥ S *ᵥ y) + c ^ 2 * ((S *ᵥ y) ⬝ᵥ (S *ᵥ y)) := by
    simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul, smul_eq_mul,
      dotProduct_comm (S *ᵥ y) y]
    ring
  rw [h5] at h4
  refine ⟨le_trans (mul_nonneg hc.le hnn) h3, ?_, fun h0 => ?_⟩
  · nlinarith [mul_le_mul_of_nonneg_left h3 hc.le]
  · have hnz : S *ᵥ y = 0 := by
      have : (S *ᵥ y) ⬝ᵥ (S *ᵥ y) = 0 := by
        rw [h0] at h3
        nlinarith
      exact dotProduct_self_eq_zero.1 this
    refine exists_mulVec_eq_of_orthogonal_ker Br hBr y fun m hm => ?_
    rw [← hSY m hm, dot_mulVec_symm S hS, hnz, zero_dotProduct]

theorem form_bounds : ∀ (g : ℕ) (Bs : Matrix (Fin g) (Fin g) ℤ) (τ G : Matrix (Fin g) (Fin g) ℂ) (c : ℝ), 0 < c → (Bs.map (fun x : ℤ => (x : ℝ))).PosSemidef → τᵀ = τ → (∀ v : Fin g → ℝ, Bs.map (fun x : ℤ => (x : ℝ)) *ᵥ v = 0 → c * (v ⬝ᵥ v) ≤ v ⬝ᵥ ((τ.map Complex.im) *ᵥ v)) → G.IsHermitian → (∀ u u' v v' : Fin g → ℤ, Bs *ᵥ v = 0 → Bs *ᵥ v' = 0 → (((fun k => (u k : ℂ)) + τ *ᵥ (fun k => (v k : ℂ))) ⬝ᵥ G *ᵥ star ((fun k => (u' k : ℂ)) + τ *ᵥ (fun k => (v' k : ℂ)))).im = ((v ⬝ᵥ u' - u ⬝ᵥ v' : ℤ) : ℝ)) → (∀ u : Fin g → ℤ, (∀ v : Fin g → ℤ, Bs *ᵥ v = 0 → u ⬝ᵥ v = 0) → G *ᵥ (fun k => (u k : ℂ)) = 0) → ∀ y : Fin g → ℂ, 0 ≤ (y ⬝ᵥ G *ᵥ star y).re ∧ (y ⬝ᵥ G *ᵥ star y).re ≤ c⁻¹ * ∑ i, ‖y i‖ ^ 2 ∧ ((y ⬝ᵥ G *ᵥ star y).re = 0 → y ∈ Submodule.span ℂ {p : Fin g → ℂ | ∃ u : Fin g → ℤ, (∀ v : Fin g → ℤ, Bs *ᵥ v = 0 → u ⬝ᵥ v = 0) ∧ p = fun k => (u k : ℂ)}) := by
  intro g Bs τ G c hc hB hτ hpos hG hrel hker y
  classical
  have hBs : Bsᵀ = Bs := ToricBasis.symm_of_posSemidef hB
  set Br : Matrix (Fin g) (Fin g) ℝ := Bs.map (fun x : ℤ => (x : ℝ)) with hBrdef
  let S : Matrix (Fin g) (Fin g) ℝ := G.map Complex.re
  let Y : Matrix (Fin g) (Fin g) ℝ := τ.map Complex.im
  have hBr : Brᵀ = Br := by
    ext i j
    have := congrFun (congrFun hBs i) j
    simp only [transpose_apply] at this
    simp [hBrdef, this]

  have him : ∀ i j, (G i j).im = 0 := by
    intro i j
    have h := hrel (Pi.single i 1) (Pi.single j 1) 0 0 (by simp) (by simp)
    have e1 : ∀ a : Fin g, (fun k => (((Pi.single a 1 : Fin g → ℤ) k : ℤ) : ℂ)) = Pi.single a 1 := by
      intro a
      funext k
      by_cases hk : k = a
      · subst hk; simp
      · simp [Pi.single_eq_of_ne hk]
    have e0 : (fun k => (((0 : Fin g → ℤ) k : ℤ) : ℂ)) = 0 := by
      funext k
      simp
    simp only [e1, e0, mulVec_zero, add_zero] at h
    simpa using h
  have hGS : ∀ i j, G i j = (S i j : ℂ) := fun i j =>
    Complex.ext (by simp [S]) (by simp [S, him])
  have hS : Sᵀ = S := by
    ext i j
    have := hG.apply i j
    simp only [transpose_apply, S, map_apply]
    rw [← this]
    simp

  have hGim : ∀ (z : Fin g → ℂ) i, ((G *ᵥ z) i).im = (S *ᵥ (fun j => (z j).im)) i := by
    intro z i
    simp only [mulVec, dotProduct, Complex.im_sum, hGS, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, add_zero]
  have hGre : ∀ (z : Fin g → ℂ) i, ((G *ᵥ z) i).re = (S *ᵥ (fun j => (z j).re)) i := by
    intro z i
    simp only [mulVec, dotProduct, Complex.re_sum, hGS, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero]

  have hSYK : ∀ v : Fin g → ℤ, Bs *ᵥ v = 0 →
      S *ᵥ (Y *ᵥ (fun k => (v k : ℝ))) = fun k => (v k : ℝ) := by
    intro v hv
    funext i
    have h := hrel (Pi.single i 1) 0 0 v (by simp) hv
    have e1 : (fun k => (((Pi.single i 1 : Fin g → ℤ) k : ℤ) : ℂ)) = Pi.single i 1 := by
      funext k
      by_cases hk : k = i
      · subst hk; simp
      · simp [Pi.single_eq_of_ne hk]
    have e2 : (fun j => ((star (τ *ᵥ (fun k => (v k : ℂ)))) j).im) =
        -(Y *ᵥ (fun k => (v k : ℝ))) := by
      funext j
      simp [mulVec, dotProduct, Y, Complex.im_sum]
    simp only [e1] at h
    simp only [Pi.zero_apply, Int.cast_zero, Complex.ofReal_zero] at h
    have e3 : (fun _ : Fin g => (0 : ℂ)) = 0 := rfl
    simp only [e3, mulVec_zero, add_zero, zero_add, single_one_dotProduct, zero_dotProduct,
      zero_sub] at h
    rw [hGim, e2, mulVec_neg] at h
    simp only [Pi.neg_apply, Int.cast_neg, neg_inj] at h
    rw [h]
  have hSY : ∀ n, Br *ᵥ n = 0 → S *ᵥ (Y *ᵥ n) = n := by
    intro n hn
    have hmem := mem_span_integer_kernel Bs hB n hn
    clear hn
    induction hmem using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨v, hv, rfl⟩ := hx
      exact hSYK v hv
    | zero => simp only [mulVec_zero]
    | add a b _ _ ha hb => simp only [mulVec_add, ha, hb]
    | smul t a _ ha => simp only [mulVec_smul, ha]

  have horth : ∀ j, ∀ v : Fin g → ℤ, Bs *ᵥ v = 0 → (fun k => Bs k j) ⬝ᵥ v = 0 := by
    intro j v hv
    have h := congrFun hv j
    have hs : ∀ k, Bs k j = Bs j k := fun k => congrFun (congrFun hBs j) k
    simpa [mulVec, dotProduct, hs] using h
  have hmul : S * Br = 0 := by
    ext i j
    have h := congrArg Complex.re (congrFun (hker _ (horth j)) i)
    rw [hGre] at h
    simpa [mulVec, dotProduct, mul_apply, hBrdef] using h
  have hmul' : Br * S = 0 := by
    have h := congrArg transpose hmul
    rwa [transpose_mul, hS, hBr, transpose_zero] at h
  have hBS : ∀ y, Br *ᵥ (S *ᵥ y) = 0 := by
    intro y
    rw [mulVec_mulVec, hmul', zero_mulVec]

  let a : Fin g → ℝ := fun i => (y i).re
  let b : Fin g → ℝ := fun i => (y i).im
  have hQ : (y ⬝ᵥ G *ᵥ star y).re = a ⬝ᵥ S *ᵥ a + b ⬝ᵥ S *ᵥ b := by
    have e1 : (fun j => ((star y) j).re) = a := by
      funext j
      simp [a]
    have e2 : (fun j => ((star y) j).im) = -b := by
      funext j
      simp [b]
    simp only [dotProduct, Complex.re_sum, Complex.mul_re, hGre, hGim, e1, e2, mulVec_neg,
      Pi.neg_apply, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [a, b]
    ring
  have hN : ∑ i, ‖y i‖ ^ 2 = a ⬝ᵥ a + b ⬝ᵥ b := by
    simp only [dotProduct, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.sq_norm, Complex.normSq_apply]
  obtain ⟨a0, a1, a2⟩ := real_form Br S Y c hc hS hBr hpos hSY hBS a
  obtain ⟨b0, b1, b2⟩ := real_form Br S Y c hc hS hBr hpos hSY hBS b
  have hspan : ∀ x : Fin g → ℝ, (∃ w, Br *ᵥ w = x) → (fun k => (x k : ℂ)) ∈
      Submodule.span ℂ {p : Fin g → ℂ | ∃ u : Fin g → ℤ,
        (∀ v : Fin g → ℤ, Bs *ᵥ v = 0 → u ⬝ᵥ v = 0) ∧ p = fun k => (u k : ℂ)} := by
    rintro _ ⟨w, rfl⟩
    have h : (fun k => (((Br *ᵥ w) k : ℝ) : ℂ)) =
        ∑ j, (w j : ℂ) • (fun k => ((Bs k j : ℤ) : ℂ)) := by
      funext k
      simp [mulVec, dotProduct, hBrdef, Finset.sum_apply, mul_comm]
    rw [h]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _
      (Submodule.subset_span ⟨fun k => Bs k j, horth j, rfl⟩)
  rw [hQ, hN]
  refine ⟨by linarith, ?_, fun h0 => ?_⟩
  · rw [le_inv_mul_iff₀ hc, mul_add]
    linarith
  · have ha0 : a ⬝ᵥ S *ᵥ a = 0 := by linarith
    have hb0 : b ⬝ᵥ S *ᵥ b = 0 := by linarith
    have hy : y = (fun k => (a k : ℂ)) + Complex.I • (fun k => (b k : ℂ)) := by
      funext k
      apply Complex.ext <;> simp [a, b]
    rw [hy]
    exact add_mem (hspan a (a2 ha0)) (Submodule.smul_mem _ _ (hspan b (b2 hb0)))

end GlobalTheory.CompanionTheory.RiemannForm
