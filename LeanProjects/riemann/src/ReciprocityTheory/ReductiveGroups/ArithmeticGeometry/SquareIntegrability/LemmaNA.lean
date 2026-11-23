import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GCauchyStatement

namespace ReciprocityTheory.ChartRestriction.G.I2

open Complex

noncomputable section

section Herm

variable {ι : Type} [Fintype ι]

lemma nA_Hf_add_left (u v w : EuclideanSpace ℂ ι) : Hf (u + v) w = Hf u w + Hf v w := by
  simp [Hf, add_mul, Finset.sum_add_distrib]

lemma nA_Hf_add_right (u v w : EuclideanSpace ℂ ι) : Hf u (v + w) = Hf u v + Hf u w := by
  simp [Hf, mul_add, Finset.sum_add_distrib]

lemma nA_Hf_sub_left (u v w : EuclideanSpace ℂ ι) : Hf (u - v) w = Hf u w - Hf v w := by
  simp [Hf, sub_mul, Finset.sum_sub_distrib]

lemma nA_Hf_sub_right (u v w : EuclideanSpace ℂ ι) : Hf u (v - w) = Hf u v - Hf u w := by
  simp [Hf, mul_sub, Finset.sum_sub_distrib]

lemma nA_Hf_smul_left (c : ℂ) (v w : EuclideanSpace ℂ ι) : Hf (c • v) w = c * Hf v w := by
  simp [Hf, Finset.mul_sum, mul_assoc]

lemma nA_Hf_smul_right (c : ℂ) (v w : EuclideanSpace ℂ ι) :
    Hf v (c • w) = (starRingEnd ℂ) c * Hf v w := by
  simp only [Hf, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [map_mul]; ring

lemma nA_Hf_conj (v w : EuclideanSpace ℂ ι) : (starRingEnd ℂ) (Hf v w) = Hf w v := by
  simp [Hf, map_sum, mul_comm]

lemma nA_Hf_self_im (v : EuclideanSpace ℂ ι) : (Hf v v).im = 0 := by
  have h := nA_Hf_conj v v
  have := congrArg Complex.im h
  simp at this
  linarith

variable {n : ℕ}

lemma nA_HC_add_left (u v w : Fin n → EuclideanSpace ℂ ι) : HC (u + v) w = HC u w + HC v w := by
  simp [HC, nA_Hf_add_left, Finset.sum_add_distrib]

lemma nA_HC_add_right (u v w : Fin n → EuclideanSpace ℂ ι) : HC u (v + w) = HC u v + HC u w := by
  simp [HC, nA_Hf_add_right, Finset.sum_add_distrib]

lemma nA_HC_sub_left (u v w : Fin n → EuclideanSpace ℂ ι) : HC (u - v) w = HC u w - HC v w := by
  simp [HC, nA_Hf_sub_left, Finset.sum_sub_distrib]

lemma nA_HC_sub_right (u v w : Fin n → EuclideanSpace ℂ ι) : HC u (v - w) = HC u v - HC u w := by
  simp [HC, nA_Hf_sub_right, Finset.sum_sub_distrib]

lemma nA_HC_conj (v w : Fin n → EuclideanSpace ℂ ι) : (starRingEnd ℂ) (HC v w) = HC w v := by
  simp [HC, map_sum, nA_Hf_conj]

lemma nA_HC_self_im (v : Fin n → EuclideanSpace ℂ ι) : (HC v v).im = 0 := by
  simp [HC, Complex.im_sum, nA_Hf_self_im]

lemma nA_HC_re_symm (v w : Fin n → EuclideanSpace ℂ ι) : (HC w v).re = (HC v w).re := by
  rw [← nA_HC_conj v w, Complex.conj_re]

lemma nA_HC_self_ofReal (v : Fin n → EuclideanSpace ℂ ι) : HC v v = ((HC v v).re : ℂ) := by
  apply Complex.ext <;> simp [nA_HC_self_im]

lemma nA_HC_sub_sub_re (v a : Fin n → EuclideanSpace ℂ ι) :
    (HC (v - a) (v - a)).re = (HC v v).re - 2 * (HC v a).re + (HC a a).re := by
  rw [nA_HC_sub_left, nA_HC_sub_right, nA_HC_sub_right, Complex.sub_re, Complex.sub_re,
    Complex.sub_re, nA_HC_re_symm v a]
  ring

lemma nA_HC_add_add_re (v a : Fin n → EuclideanSpace ℂ ι) :
    (HC (v + a) (v + a)).re = (HC v v).re + 2 * (HC v a).re + (HC a a).re := by
  rw [nA_HC_add_left, nA_HC_add_right, nA_HC_add_right, Complex.add_re, Complex.add_re,
    Complex.add_re, nA_HC_re_symm v a]
  ring

lemma nA_exp_mul_conj (z : ℂ) : cexp z * (starRingEnd ℂ) (cexp z) = ((Real.exp (2 * z.re) : ℝ) : ℂ) := by
  rw [← Complex.exp_conj, ← Complex.exp_add, Complex.add_conj, Complex.ofReal_exp]

end Herm

section PTAlg

variable {E : Type} [Field E] [NumberField E] (X : PT E)

lemma nA_re_U (q : ℕ) {n : ℕ} (v a : Fin n → Vsp X.dim) :
    ((q : ℂ) * Real.pi * HC v a - q * Real.pi * HC a a / 2).re =
      q * Real.pi * (HC v a).re - q * Real.pi * (HC a a).re / 2 := by
  simp [Complex.mul_re, Complex.sub_re]

lemma nA_re_S (q : ℕ) {n : ℕ} (v a : Fin n → Vsp X.dim) :
    ((q : ℂ) * Real.pi * HC v a + q * Real.pi * HC a a / 2).re =
      q * Real.pi * (HC v a).re + q * Real.pi * (HC a a).re / 2 := by
  simp [Complex.mul_re, Complex.add_re]

lemma nA_ip_U (q : ℕ) {n : ℕ} (a : Fin n → Vsp X.dim) (F G : (Fin n → Vsp X.dim) → ℂ)
    (v : Fin n → Vsp X.dim) :
    X.U q a F v * (starRingEnd ℂ) (X.U q a G v) * ((Real.exp (-(q * Real.pi) * (HC v v).re) : ℝ) : ℂ) =
      F (v - a) * (starRingEnd ℂ) (G (v - a)) *
        ((Real.exp (-(q * Real.pi) * (HC (v - a) (v - a)).re) : ℝ) : ℂ) := by
  unfold PT.U
  set z : ℂ := (q : ℂ) * Real.pi * HC v a - q * Real.pi * HC a a / 2 with hz
  have hre : 2 * z.re + (-(q * Real.pi) * (HC v v).re) = -(q * Real.pi) * (HC (v - a) (v - a)).re := by
    rw [hz, nA_re_U, nA_HC_sub_sub_re]; ring
  calc cexp z * F (v - a) * (starRingEnd ℂ) (cexp z * G (v - a)) *
        ((Real.exp (-(q * Real.pi) * (HC v v).re) : ℝ) : ℂ)
      = (cexp z * (starRingEnd ℂ) (cexp z)) * (F (v - a) * (starRingEnd ℂ) (G (v - a))) *
          ((Real.exp (-(q * Real.pi) * (HC v v).re) : ℝ) : ℂ) := by rw [map_mul]; ring
    _ = _ := by
      rw [nA_exp_mul_conj, ← hre, Real.exp_add, Complex.ofReal_mul]; ring

lemma pointwiseNormSq_translate (q : ℕ) {n : ℕ} (a : Fin n → Vsp X.dim) (F : (Fin n → Vsp X.dim) → ℂ)
    (v : Fin n → Vsp X.dim) : X.ptN2 q (X.U q a F) v = X.ptN2 q F (v - a) := by
  unfold PT.ptN2 PT.U
  set z : ℂ := (q : ℂ) * Real.pi * HC v a - q * Real.pi * HC a a / 2 with hz
  have hre : 2 * z.re + (-(q * Real.pi) * (HC v v).re) = -(q * Real.pi) * (HC (v - a) (v - a)).re := by
    rw [hz, nA_re_U, nA_HC_sub_sub_re]; ring
  rw [norm_mul, Complex.norm_exp, mul_pow, ← hre, Real.exp_add, sq (Real.exp z.re), ← Real.exp_add]
  ring_nf

lemma nA_eps_sq {x : Vsp X.dim} (hx : x ∈ X.L) : ((X.eps x : ℂ)) ^ 2 = 1 := by
  rcases X.eps_pm x hx with h | h <;> simp [h]

lemma nA_epsprod_sq {n : ℕ} {γ : Fin n → Vsp X.dim} (hγ : ∀ k, γ k ∈ X.L) :
    (∏ k, (X.eps (γ k) : ℂ)) ^ 2 = 1 := by
  rw [← Finset.prod_pow]
  exact Finset.prod_eq_one fun k _ => nA_eps_sq X (hγ k)

lemma nA_epsprod_conj {n : ℕ} (γ : Fin n → Vsp X.dim) :
    (starRingEnd ℂ) (∏ k, (X.eps (γ k) : ℂ)) = ∏ k, (X.eps (γ k) : ℂ) := by
  rw [map_prod]; simp

lemma nA_epsprod_norm {n : ℕ} {γ : Fin n → Vsp X.dim} (hγ : ∀ k, γ k ∈ X.L) :
    ‖∏ k, (X.eps (γ k) : ℂ)‖ = 1 := by
  rw [norm_prod]
  refine Finset.prod_eq_one fun k _ => ?_
  rcases X.eps_pm (γ k) (hγ k) with h | h <;> simp [h]

lemma nA_ip_periodic {q n : ℕ} {F G : (Fin n → Vsp X.dim) → ℂ} (hF : F ∈ X.Sec q n) (hG : G ∈ X.Sec q n)
    {γ : Fin n → Vsp X.dim} (hγ : ∀ k, γ k ∈ X.L) (v : Fin n → Vsp X.dim) :
    F (v + γ) * (starRingEnd ℂ) (G (v + γ)) *
        ((Real.exp (-(q * Real.pi) * (HC (v + γ) (v + γ)).re) : ℝ) : ℂ) =
      F v * (starRingEnd ℂ) (G v) * ((Real.exp (-(q * Real.pi) * (HC v v).re) : ℝ) : ℂ) := by
  rw [hF.2 γ hγ v, hG.2 γ hγ v]
  set e : ℂ := ∏ k, (X.eps (γ k) : ℂ) with he
  set z : ℂ := (q : ℂ) * Real.pi * HC v γ + q * Real.pi * HC γ γ / 2 with hz
  have hre : 2 * z.re + (-(q * Real.pi) * (HC (v + γ) (v + γ)).re) = -(q * Real.pi) * (HC v v).re := by
    rw [hz, nA_re_S, nA_HC_add_add_re]; ring
  have hee : e ^ q * (starRingEnd ℂ) (e ^ q) = 1 := by
    rw [map_pow, he, nA_epsprod_conj X, ← mul_pow, ← sq, nA_epsprod_sq X hγ, one_pow]
  calc e ^ q * cexp z * F v * (starRingEnd ℂ) (e ^ q * cexp z * G v) *
        ((Real.exp (-(q * Real.pi) * (HC (v + γ) (v + γ)).re) : ℝ) : ℂ)
      = (e ^ q * (starRingEnd ℂ) (e ^ q)) * (cexp z * (starRingEnd ℂ) (cexp z)) *
          (F v * (starRingEnd ℂ) (G v)) *
          ((Real.exp (-(q * Real.pi) * (HC (v + γ) (v + γ)).re) : ℝ) : ℂ) := by
        simp only [map_mul]; ring
    _ = _ := by
      rw [hee, nA_exp_mul_conj, ← hre, Real.exp_add, Complex.ofReal_mul]; ring

lemma pointwiseNormSq_add_period {q n : ℕ} {F : (Fin n → Vsp X.dim) → ℂ} (hF : F ∈ X.Sec q n)
    {γ : Fin n → Vsp X.dim} (hγ : ∀ k, γ k ∈ X.L) (v : Fin n → Vsp X.dim) :
    X.ptN2 q F (v + γ) = X.ptN2 q F v := by
  unfold PT.ptN2
  rw [hF.2 γ hγ v]
  set z : ℂ := (q : ℂ) * Real.pi * HC v γ + q * Real.pi * HC γ γ / 2 with hz
  have hre : 2 * z.re + (-(q * Real.pi) * (HC (v + γ) (v + γ)).re) = -(q * Real.pi) * (HC v v).re := by
    rw [hz, nA_re_S, nA_HC_add_add_re]; ring
  rw [norm_mul, norm_mul, norm_pow, nA_epsprod_norm X hγ, one_pow, one_mul, Complex.norm_exp,
    mul_pow, ← hre, Real.exp_add, sq (Real.exp z.re), ← Real.exp_add]
  ring_nf

end PTAlg

section PTSec

variable {E : Type} [Field E] [NumberField E] (X : PT E)

lemma nA_int_im {q n : ℕ} {γ b : Fin n → Vsp X.dim} (hγ : ∀ k, γ k ∈ X.L)
    (hb : ∀ k, (q : ℂ) • b k ∈ X.L) : ∃ m : ℤ, (q : ℝ) * (HC γ b).im = m := by
  choose m hm using fun k => X.integral (γ k) ((q : ℂ) • b k) (hγ k) (hb k)
  refine ⟨∑ k, m k, ?_⟩
  rw [HC, Complex.im_sum, Finset.mul_sum, Int.cast_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← hm k, nA_Hf_smul_right]
  simp [Complex.mul_im]

lemma nA_exp_antisymm_eq_one {n : ℕ} (q : ℕ) (γ b : Fin n → Vsp X.dim) (m : ℤ)
    (hm : (q : ℝ) * (HC γ b).im = m) :
    cexp ((q : ℂ) * Real.pi * (HC γ b - HC b γ)) = 1 := by
  rw [← nA_HC_conj γ b, Complex.sub_conj]
  have : (q : ℂ) * Real.pi * (((2 * (HC γ b).im : ℝ) : ℂ) * I) = (m : ℂ) * (2 * Real.pi * I) := by
    have hm' : ((q : ℝ) : ℂ) * (((HC γ b).im : ℝ) : ℂ) = (m : ℂ) := by
      rw [← Complex.ofReal_mul, hm]; simp
    push_cast at hm' ⊢
    linear_combination (2 * Real.pi * I) * hm'
  rw [this, Complex.exp_int_mul_two_pi_mul_I]

lemma nA_U_mem {q n : ℕ} {F : (Fin n → Vsp X.dim) → ℂ} (hF : F ∈ X.Sec q n)
    {b : Fin n → Vsp X.dim} (hb : ∀ k, (q : ℂ) • b k ∈ X.L) : X.U q b F ∈ X.Sec q n := by
  refine ⟨?_, fun γ hγ v => ?_⟩
  · unfold PT.U
    have h1 : Differentiable ℂ (fun v : Fin n → Vsp X.dim => F (v - b)) :=
      hF.1.comp (differentiable_id.sub_const b)
    have h2 : Differentiable ℂ (fun v : Fin n → Vsp X.dim =>
        (q : ℂ) * Real.pi * HC v b - q * Real.pi * HC b b / 2) := by
      unfold HC Hf
      fun_prop
    exact (h2.cexp).mul h1
  · unfold PT.U
    have e1 : v + γ - b = (v - b) + γ := by abel
    rw [e1, hF.2 γ hγ (v - b)]
    obtain ⟨m, hm⟩ := nA_int_im X hγ hb
    have h1 := nA_exp_antisymm_eq_one X q γ b m hm
    have hsplit : (q : ℂ) * Real.pi * HC (v + γ) b - q * Real.pi * HC b b / 2 +
        ((q : ℂ) * Real.pi * HC (v - b) γ + q * Real.pi * HC γ γ / 2) =
        ((q : ℂ) * Real.pi * HC v γ + q * Real.pi * HC γ γ / 2) +
        ((q : ℂ) * Real.pi * HC v b - q * Real.pi * HC b b / 2) +
        (q : ℂ) * Real.pi * (HC γ b - HC b γ) := by
      rw [nA_HC_add_left, nA_HC_sub_left]; ring
    calc cexp ((q : ℂ) * Real.pi * HC (v + γ) b - q * Real.pi * HC b b / 2) *
          ((∏ k, (X.eps (γ k) : ℂ)) ^ q * cexp ((q : ℂ) * Real.pi * HC (v - b) γ +
            q * Real.pi * HC γ γ / 2) * F (v - b))
        = (∏ k, (X.eps (γ k) : ℂ)) ^ q *
            cexp ((q : ℂ) * Real.pi * HC (v + γ) b - q * Real.pi * HC b b / 2 +
              ((q : ℂ) * Real.pi * HC (v - b) γ + q * Real.pi * HC γ γ / 2)) * F (v - b) := by
          simp only [Complex.exp_add]; ring
      _ = _ := by
          rw [hsplit, Complex.exp_add, Complex.exp_add, h1]; ring

lemma nA_pi_diff {q n : ℕ} {π : Vsp X.dim →ₗ[ℂ] Vsp X.dim} (k : Fin n) :
    Differentiable ℂ (fun v : Fin n → Vsp X.dim => fun _ : Fin 1 => π (v k)) := by
  have hc : Differentiable ℂ (fun w : Vsp X.dim => π w) :=
    (LinearMap.toContinuousLinearMap π).differentiable
  exact differentiable_pi.mpr fun _ => hc.comp (differentiable_apply k)

lemma pullbackSection_mem_thetaSpace {q n : ℕ} {π : Vsp X.dim →ₗ[ℂ] Vsp X.dim} (hπ : IsPi X q π)
    {s : (Fin 1 → Vsp X.dim) → ℂ} (hs : s ∈ X.Sec 1 1) : s0 X (n := n) π s ∈ X.Sec q n := by
  refine ⟨?_, fun γ hγ v => ?_⟩
  · unfold s0
    have hk : ∀ k : Fin n, Differentiable ℂ (fun v : Fin n → Vsp X.dim => s fun _ => π (v k)) :=
      fun k => hs.1.comp (nA_pi_diff X (q := q) k)
    have hp : ∀ t : Finset (Fin n),
        Differentiable ℂ (fun v : Fin n → Vsp X.dim => ∏ k ∈ t, s fun _ => π (v k)) := by
      intro t
      induction t using Finset.induction_on with
      | empty => simp
      | insert a t ha ih =>
        simp only [Finset.prod_insert ha]
        exact (hk a).mul ih
    exact hp Finset.univ
  · have key : ∀ k, s (fun _ => π ((v + γ) k)) = (X.eps (γ k) : ℂ) ^ q *
        cexp ((q : ℂ) * Real.pi * Hf (v k) (γ k) + q * Real.pi * Hf (γ k) (γ k) / 2) *
          s (fun _ => π (v k)) := by
      intro k
      have h := hs.2 (fun _ => π (γ k)) (fun _ => hπ.2.1 _ (hγ k)) (fun _ => π (v k))
      have e1 : (fun _ : Fin 1 => π ((v + γ) k)) = (fun _ => π (v k)) + (fun _ => π (γ k)) := by
        funext; simp [map_add]
      rw [e1, h]
      simp only [HC, Finset.univ_unique, Finset.sum_singleton, Finset.prod_singleton, hπ.2.2.1,
        hπ.2.2.2 _ (hγ k), pow_one]
      push_cast
      ring_nf
    unfold s0
    simp_rw [key]
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_pow, ← Complex.exp_sum]
    congr 3
    simp only [HC, Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_div]

lemma translate_pullbackSection {q n : ℕ} {π : Vsp X.dim →ₗ[ℂ] Vsp X.dim} (hπ : IsPi X q π)
    {s : (Fin 1 → Vsp X.dim) → ℂ} (hs : s ∈ X.Sec 1 1) {k : Fin n → Vsp X.dim}
    (hk : ∀ j, π (k j) ∈ X.L) (v : Fin n → Vsp X.dim) :
    X.U q k (s0 X π s) v = (∏ j, (X.eps (π (k j)) : ℂ)) * s0 X π s v := by
  have key : ∀ j, s (fun _ => π ((v - k) j)) = (X.eps (π (k j)) : ℂ) *
      cexp (-((q : ℂ) * Real.pi * Hf ((v - k) j) (k j) + q * Real.pi * Hf (k j) (k j) / 2)) *
        s (fun _ => π (v j)) := by
    intro j
    have h := hs.2 (fun _ => π (k j)) (fun _ => hk j) (fun _ => π ((v - k) j))
    have e1 : (fun _ : Fin 1 => π ((v - k) j)) + (fun _ => π (k j)) = (fun _ => π (v j)) := by
      funext; simp [← map_add]
    rw [e1] at h
    simp only [HC, Finset.univ_unique, Finset.sum_singleton, Finset.prod_singleton, hπ.2.2.1,
      pow_one] at h
    rw [h]
    have he : (X.eps (π (k j)) : ℂ) * X.eps (π (k j)) = 1 := by
      rw [← sq]; exact nA_eps_sq X (hk j)
    set A : ℂ := (q : ℂ) * Real.pi * Hf ((v - k) j) (k j) + q * Real.pi * Hf (k j) (k j) / 2
    have hA : ((1 : ℕ) : ℂ) * Real.pi * ((q : ℂ) * Hf ((v - k) j) (k j)) +
        ((1 : ℕ) : ℂ) * Real.pi * ((q : ℂ) * Hf (k j) (k j)) / 2 = A := by
      push_cast; ring
    rw [hA]
    calc s (fun _ => π ((v - k) j))
        = ((X.eps (π (k j)) : ℂ) * X.eps (π (k j))) * (cexp (-A) * cexp A) *
            s (fun _ => π ((v - k) j)) := by
          rw [he, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero]; ring
      _ = _ := by ring
  unfold PT.U s0
  simp_rw [key]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, ← Complex.exp_sum]
  have hz : (q : ℂ) * Real.pi * HC v k - q * Real.pi * HC k k / 2 +
      ∑ j, -((q : ℂ) * Real.pi * Hf ((v - k) j) (k j) + q * Real.pi * Hf (k j) (k j) / 2) = 0 := by
    have : ∑ j, -((q : ℂ) * Real.pi * Hf ((v - k) j) (k j) + q * Real.pi * Hf (k j) (k j) / 2) =
        -((q : ℂ) * Real.pi * HC (v - k) k + q * Real.pi * HC k k / 2) := by
      simp only [HC, Finset.mul_sum, Finset.sum_div, ← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
    rw [this, nA_HC_sub_left]; ring
  calc cexp ((q : ℂ) * Real.pi * HC v k - q * Real.pi * HC k k / 2) *
        ((∏ j, (X.eps (π (k j)) : ℂ)) *
          cexp (∑ j, -((q : ℂ) * Real.pi * Hf ((v - k) j) (k j) + q * Real.pi * Hf (k j) (k j) / 2)) *
          ∏ j, s fun _ => π (v j))
      = (∏ j, (X.eps (π (k j)) : ℂ)) *
          cexp ((q : ℂ) * Real.pi * HC v k - q * Real.pi * HC k k / 2 +
            ∑ j, -((q : ℂ) * Real.pi * Hf ((v - k) j) (k j) + q * Real.pi * Hf (k j) (k j) / 2)) *
          ∏ j, s fun _ => π (v j) := by rw [Complex.exp_add]; ring
    _ = _ := by rw [hz, Complex.exp_zero, mul_one]

lemma nA_U_comm (q : ℕ) {n : ℕ} (k b : Fin n → Vsp X.dim) (F : (Fin n → Vsp X.dim) → ℂ)
    (v : Fin n → Vsp X.dim) :
    X.U q k (X.U q b F) v = cexp ((q : ℂ) * Real.pi * (HC b k - HC k b)) * X.U q b (X.U q k F) v := by
  unfold PT.U
  rw [sub_right_comm v k b, nA_HC_sub_left, nA_HC_sub_left]
  simp only [← mul_assoc, ← Complex.exp_add]
  congr 2
  ring

lemma nA_U_smul (q : ℕ) {n : ℕ} (a : Fin n → Vsp X.dim) (c : ℂ) (F : (Fin n → Vsp X.dim) → ℂ) :
    X.U q a (fun v => c * F v) = fun v => c * X.U q a F v := by
  funext v; unfold PT.U; ring

end PTSec

end

end ReciprocityTheory.ChartRestriction.G.I2
