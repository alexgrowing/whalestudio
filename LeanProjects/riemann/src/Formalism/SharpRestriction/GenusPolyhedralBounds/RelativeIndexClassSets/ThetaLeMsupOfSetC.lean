import Formalism.SharpRestriction.Divisibility.WeightAlgebra

noncomputable section

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain

namespace Formalism.MainNotions.Gaps.T0

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ}

theorem wt_ext {w w' : WeightFamilies.Wt D j} (h1 : ∀ τ i, w.aP τ i = w'.aP τ i) (h2 : ∀ τ i, w.aM τ i = w'.aM τ i)
    (h3 : w.n = w'.n) : w = w' := by
  obtain ⟨aP, aM, _, _, n, _⟩ := w
  obtain ⟨aP', aM', _, _, n', _⟩ := w'
  have e1 : aP = aP' := funext fun τ => funext fun i => h1 τ i
  have e2 : aM = aM' := funext fun τ => funext fun i => h2 τ i
  have e3 : n = n' := h3
  subst e1 e2 e3
  rfl

theorem wadd_wsmul_zero (wL w : WeightFamilies.Wt D j) : wadd (wsmul 0 wL) w = w := by
  apply wt_ext <;> intros <;> simp [wadd, wsmul]

theorem wadd_wsmul_succ (n : ℕ) (wL w : WeightFamilies.Wt D j) :
    wadd (wsmul n wL) (wadd wL w) = wadd (wsmul (n + 1) wL) w := by
  apply wt_ext <;> intros <;> simp only [wadd, wsmul] <;> ring

theorem emb_mono (X : PJ D B P j) (w : WeightFamilies.Wt D j) {N N' : Submodule (𝓞 B.KO) (B.Cusp j w)} (h : N ≤ N') :
    X.emb w N ≤ X.emb w N' :=
  Submodule.map_mono h

theorem mlat_mul (X : PJ D B P j) (w w' : WeightFamilies.Wt D j) {F : B.Cusp j w} {G : B.Cusp j w'}
    (hF : F ∈ B.Mlat j w) (hG : G ∈ B.Mlat j w') :
    ∃ H ∈ B.Mlat j (wadd w w'), X.inc w F * X.inc w' G = X.inc (wadd w w') H := by
  obtain ⟨H, hH⟩ := X.inc_mul w w' F G
  refine ⟨H, (X.Mlat_eq _ H).2 fun la y => ?_, hH⟩
  rw [← hH, X.vAt_mul]
  exact add_nonneg ((X.Mlat_eq w F).1 hF la y) ((X.Mlat_eq w' G).1 hG la y)

theorem msup_mul_le (X : PJ D B P j) (w w' : WeightFamilies.Wt D j) :
    X.Msup w * X.Msup w' ≤ X.Msup (wadd w w') := by
  rw [Submodule.mul_le]
  rintro _ ⟨F, hF, rfl⟩ _ ⟨G, hG, rfl⟩
  obtain ⟨H, hH, e⟩ := mlat_mul X w w' hF hG
  exact ⟨H, hH, e.symm⟩

private lemma smul_le_lemma_2 {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
    {M N P Q : Submodule R A} (h1 : M ≤ P) (h2 : N ≤ Q) : M * N ≤ P * Q :=
  Submodule.mul_le.2 fun _ hm _ hn => Submodule.mul_mem_mul (h1 hm) (h2 hn)

theorem msup_pow_mul_le (X : PJ D B P j) (wL : WeightFamilies.Wt D j) (n : ℕ) :
    ∀ w : WeightFamilies.Wt D j, X.Msup wL ^ n * X.Msup w ≤ X.Msup (wadd (wsmul n wL) w) := by
  induction n with
  | zero => intro w; rw [pow_zero, one_mul, wadd_wsmul_zero]
  | succ n ih =>
    intro w
    rw [pow_succ, mul_assoc, ← wadd_wsmul_succ]
    exact (smul_le_lemma_2 le_rfl (msup_mul_le X wL w)).trans (ih _)

private lemma spow_le_lemma {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
    {M N : Submodule R A} (h : M ≤ N) (n : ℕ) : M ^ n ≤ N ^ n := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact smul_le_lemma_2 ih h

theorem emb_pow_mul_le (X : PJ D B P j) (wL w : WeightFamilies.Wt D j) (n : ℕ)
    {NL : Submodule (𝓞 B.KO) (B.Cusp j wL)} {N : Submodule (𝓞 B.KO) (B.Cusp j w)}
    (hL : NL ≤ B.Mlat j wL) (hN : N ≤ B.Mlat j w) :
    X.emb wL NL ^ n * X.emb w N ≤ X.Msup (wadd (wsmul n wL) w) :=
  (smul_le_lemma_2 (spow_le_lemma (emb_mono X wL hL) n) (emb_mono X w hN)).trans
    (msup_pow_mul_le X wL n w)

theorem wt_first {ka wL wF : WeightFamilies.Wt D j} {T nP nW : ℕ} (hF : IsF' ka wL wF T nP) (hL : wL.n = nW)
    (hn : ka.n = nP + T * nW) : wadd (wsmul T wL) wF = ka := by
  obtain ⟨e1, e2, e3⟩ := hF
  apply wt_ext
  · intro τ i
    have := e2 τ i
    simp only [wadd, wsmul]
    zify
    linarith
  · intro τ i
    have := e3 τ i
    simp only [wadd, wsmul]
    zify
    linarith
  · simp only [wadd, wsmul]
    rw [e1, hL, hn]
    ring

theorem wt_second (X : PJ D B P j) {ka wL wF : WeightFamilies.Wt D j} {T nP nW : ℕ} (hF : IsF' ka wL wF T nP)
    (hL : wL.n = nW) (hn : ka.n = nP + T * nW) (hD : WeightFamilies.dimY D j ≤ T) :
    wadd (wsmul (T - WeightFamilies.dimY D j) wL) (X.wF0 wL wF) = ka := by
  rw [← wt_first hF hL hn]
  obtain ⟨c, hc⟩ := Nat.exists_eq_add_of_le hD
  apply wt_ext <;> intros <;> simp only [PJ.wF0, wadd, wsmul, hc, Nat.add_sub_cancel_left] <;> ring

theorem theta_first_le (X : PJ D B P j) (S : Scal B) {ka wL wF : WeightFamilies.Wt D j} {T nP nW : ℕ}
    (hW : X.WWc S.sW wL ≤ B.Mlat j wL) (hT : X.Thc S.sF wF ≤ B.Mlat j wF)
    (hF : IsF' ka wL wF T nP) (hL : wL.n = nW) (hn : ka.n = nP + T * nW) :
    X.emb wL (X.WWc S.sW wL) ^ T * X.emb wF (X.Thc S.sF wF) ≤ X.Msup ka := by
  have h := emb_pow_mul_le X wL wF T hW hT
  rwa [wt_first hF hL hn] at h

theorem theta_second_le (X : PJ D B P j) (S : Scal B) {ka wL wF : WeightFamilies.Wt D j} {T nP nW : ℕ}
    (hW : X.WWc S.sW wL ≤ B.Mlat j wL) (hT : X.Thc S.s0 (X.wF0 wL wF) ≤ B.Mlat j (X.wF0 wL wF))
    (hF : IsF' ka wL wF T nP) (hL : wL.n = nW) (hn : ka.n = nP + T * nW) (hD : WeightFamilies.dimY D j ≤ T) :
    X.emb wL (X.WWc S.sW wL) ^ (T - WeightFamilies.dimY D j) * X.emb (X.wF0 wL wF) (X.Thc S.s0 (X.wF0 wL wF)) ≤
      X.Msup ka := by
  have h := emb_pow_mul_le X wL (X.wF0 wL wF) (T - WeightFamilies.dimY D j) hW hT
  rwa [wt_second X hF hL hn hD] at h

theorem theta_third_le (X : PJ D B P j) (S : Scal B) {ka : WeightFamilies.Wt D j}
    (hT : X.Thc S.sK ka ≤ B.Mlat j ka) : X.emb ka (X.Thc S.sK ka) ≤ X.Msup ka :=
  emb_mono X ka hT

theorem theta_le_msup (X : PJ D B P j) (S : Scal B) {ka wL wF : WeightFamilies.Wt D j} {T nP nW : ℕ}
    (h2 : H2 X S ka wL wF) (hF : IsF' ka wL wF T nP) (hL : wL.n = nW) (hn : ka.n = nP + T * nW)
    (hD : WeightFamilies.dimY D j ≤ T) : X.Theta S ka wL wF T ≤ X.Msup ka := by
  unfold PJ.Theta
  exact sup_le (sup_le (theta_first_le X S h2.1 h2.2.1 hF hL hn)
    (theta_second_le X S h2.1 h2.2.2.1 hF hL hn hD)) (theta_third_le X S h2.2.2.2)

theorem theta_le_msup_of_setC {large₂ : SizeData₂ D} (X : PJ D B P j) (S : Scal B) {CK C1 A1 : ℝ}
    {ka wL wF : WeightFamilies.Wt D j} {T nP nW : ℕ} {h0 : ℝ} (h2 : H2 X S ka wL wF)
    (hC : SetC large₂ X CK C1 A1 ka wL wF T nP nW h0) : X.Theta S ka wL wF T ≤ X.Msup ka := by
  obtain ⟨c0, -, -, -, -, -, -, -, -, -, -, -, -, c13, c14, c15, -, -, c18, -⟩ := hC
  exact theta_le_msup X S h2 c15 c14.1 (c0.trans c13) c18

theorem theta_le_msup_of_hyp {large₂ : SizeData₂ D} (X : PJ D B P j) {H : KHyp} {C2 A2 CR Bx CT : ℝ} (S : Scal B)
    {ka wL wF : WeightFamilies.Wt D j} {T nP nW : ℕ} {h0 : ℝ} {nus : HeightOneSpectrum (𝓞 B.KO) → ℝ}
    (h : Hyp large₂ X H C2 A2 CR Bx CT S ka wL wF T nP nW h0 nus) : X.Theta S ka wL wF T ≤ X.Msup ka :=
  theta_le_msup_of_setC X S h.2.2.2.2.1 h.2.1

end Formalism.MainNotions.Gaps.T0

end
