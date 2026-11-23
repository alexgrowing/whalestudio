import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.FunctionalCalculusLaws

noncomputable section

open Matrix Finset ReciprocityTheory.ChartRestriction.DS

namespace PositivityTheory.CW

namespace FormEigenMonotone

lemma phi_nonneg (s : ℕ) (R x : ℝ) : 0 ≤ phiR s R x := le_max_right _ _

lemma phi_zero {s : ℕ} {R x : ℝ} (hR : 0 < R) (hx : R ≤ x) : phiR s R x = 0 := by
  unfold phiR
  apply max_eq_right
  have h1 : (0:ℝ) < (1+R)^s := by positivity
  have h2 : (1+R)^s ≤ (1+x)^s := pow_le_pow_left₀ (by linarith) (by linarith) s
  have := inv_anti₀ h1 h2
  linarith

lemma phi_le_one {s : ℕ} {R x : ℝ} (hR : 0 < R) (hx : 0 ≤ x) : phiR s R x ≤ 1 := by
  unfold phiR
  apply max_le _ zero_le_one
  have h1 : (1:ℝ) ≤ (1+x)^s := one_le_pow₀ (by linarith)
  have h2 : ((1+x)^s)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ h1
  have h3 : 0 ≤ ((1+R)^s)⁻¹ := by positivity
  linarith

lemma phi_eq {s : ℕ} {R x : ℝ} (hx : 0 ≤ x) (hxR : x < R) :
    phiR s R x = ((1+x)^s)⁻¹ - ((1+R)^s)⁻¹ := by
  unfold phiR
  apply max_eq_left
  have h1 : (0:ℝ) < (1+x)^s := by positivity
  have h2 : (1+x)^s ≤ (1+R)^s := pow_le_pow_left₀ (by linarith) (by linarith) s
  have := inv_anti₀ h1 h2
  linarith

variable {n : ℕ} {ε : Fin n → Bool} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {E : Fin n → Fin n → Module.End ℂ V} {ι : Type} {b : Module.Basis ι ℂ V} {μ : ι → ℝ}

lemma beta_add (A B : Module.End ℂ V) (v w : V) :
    beta ε E (A + B) v w = beta ε E A v w + beta ε E B v w := by
  simp only [beta, LinearMap.add_apply, inner_add_right, Finset.sum_add_distrib]

lemma re_inner_smul_self (r : ℝ) (v : V) : (inner ℂ v ((r : ℂ) • v)).re = r * ‖v‖ ^ 2 := by
  rw [inner_smul_right, Complex.re_ofReal_mul]
  congr 1
  exact inner_self_eq_norm_sq (𝕜 := ℂ) v

lemma beta_const_re (r : ℝ) (v : V) :
    (beta ε E ((r : ℂ) • 1) v v).re = r * ∑ p ∈ nc ε, ‖E p.1 p.2 v‖ ^ 2 := by
  simp only [beta, LinearMap.smul_apply, Module.End.one_apply, Complex.re_sum, re_inner_smul_self,
    Finset.mul_sum]

lemma beta_mono
    (hmono : ∀ φ ψ : ℝ → ℝ, (∀ x, 0 ≤ x → φ x ≤ ψ x) → ∀ w,
      (inner ℂ w (fc b μ φ w)).re ≤ (inner ℂ w (fc b μ ψ w)).re)
    (φ ψ : ℝ → ℝ) (h : ∀ x, 0 ≤ x → φ x ≤ ψ x) (v : V) :
    (beta ε E (fc b μ φ) v v).re ≤ (beta ε E (fc b μ ψ) v v).re := by
  simp only [beta, Complex.re_sum]
  exact Finset.sum_le_sum fun p _ => hmono φ ψ h _

lemma norm_fib (hb : Orthonormal ℂ b) (f : V →ₗ[ℂ] ℂ) (F : Finset ι) :
    ‖∑ j ∈ F, starRingEnd ℂ (f (b j)) • b j‖ ^ 2 = ∑ j ∈ F, ‖f (b j)‖ ^ 2 := by
  rw [@norm_sq_eq_re_inner ℂ, hb.inner_sum, RCLike.re_to_complex, Complex.re_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.conj_conj, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]

lemma eig_fib (hb : ∀ i, Eig ε E (μ i) (b i)) (ν : ℝ) (F : Finset ι) (hF : ∀ j ∈ F, μ j = ν)
    (a : ι → ℂ) : Eig ε E ν (∑ j ∈ F, a j • b j) := by
  unfold Eig
  rw [map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [map_smul, hb j, hF j hj, smul_comm]

lemma key {κ c x₀ R : ℝ} {s : ℕ}
    (hA0 : ∀ w, ∑ p ∈ nc ε, ‖E p.1 p.2 w‖ ^ 2 = (inner ℂ w (casimirK ε E w)).re - κ * ‖w‖ ^ 2)
    (hmono : ∀ φ ψ : ℝ → ℝ, (∀ x, 0 ≤ x → φ x ≤ ψ x) → ∀ w,
      (inner ℂ w (fc b μ φ w)).re ≤ (inner ℂ w (fc b μ ψ w)).re)
    (hadd : ∀ φ ψ : ℝ → ℝ, fc b μ (fun x => φ x + ψ x) = fc b μ φ + fc b μ ψ)
    (hconst : ∀ c : ℝ, fc b μ (fun _ => c) = (c : ℂ) • 1)
    (hA12 : ∀ ν v, x₀ ≤ ν → Eig ε E ν v →
      ((1 + ν) ^ s)⁻¹ * (ν - κ + c) * ‖v‖ ^ 2 ≤ (beta ε E (fc b μ fun x => ((1 + x) ^ s)⁻¹) v v).re)
    (hc : 0 ≤ c) (hR : 0 < R) (ν : ℝ) (hν : 0 ≤ ν) (h : V) (hh : Eig ε E ν h) :
    phiR s R ν * (ν - κ + c) * ‖h‖ ^ 2 - (if ν < x₀ then x₀ + |κ| + c else 0) * ‖h‖ ^ 2 ≤
      (beta ε E (fc b μ (phiR s R)) h h).re := by
  have hN : ∀ w, 0 ≤ (beta ε E (fc b μ (phiR s R)) w w).re := by
    intro w
    have h0 := beta_mono (ε := ε) (E := E) hmono (fun _ => (0:ℝ)) (phiR s R)
      (fun x _ => phi_nonneg s R x) w
    rw [hconst 0, beta_const_re] at h0
    simpa using h0
  have hd0 : (0:ℝ) ≤ ((1 + R) ^ s)⁻¹ := inv_nonneg.mpr (pow_nonneg (by linarith) _)
  have hS : ∑ p ∈ nc ε, ‖E p.1 p.2 h‖ ^ 2 = (ν - κ) * ‖h‖ ^ 2 := by
    rw [hA0 h, show casimirK ε E h = (ν : ℂ) • h from hh, re_inner_smul_self]
    ring
  have hlow : (beta ε E (fc b μ fun x => ((1 + x) ^ s)⁻¹) h h).re - ((1 + R) ^ s)⁻¹ * ((ν - κ) * ‖h‖ ^ 2)
      ≤ (beta ε E (fc b μ (phiR s R)) h h).re := by
    have e : fc b μ (fun x => ((1 + x) ^ s)⁻¹ + -((1 + R) ^ s)⁻¹)
        = fc b μ (fun x => ((1 + x) ^ s)⁻¹) + fc b μ (fun _ => -((1 + R) ^ s)⁻¹) := hadd _ _
    have h1 := beta_mono (ε := ε) (E := E) hmono (fun x => ((1 + x) ^ s)⁻¹ + -((1 + R) ^ s)⁻¹)
      (phiR s R) (fun x _ => by
        simp only [phiR]
        linarith [le_max_left (((1 + x) ^ s)⁻¹ - ((1 + R) ^ s)⁻¹) 0]) h
    rw [e, beta_add, hconst (-((1 + R) ^ s)⁻¹), Complex.add_re, beta_const_re, hS] at h1
    linarith
  have hn : 0 ≤ ‖h‖ ^ 2 := by positivity
  by_cases hx : ν < x₀
  · rw [if_pos hx]
    have hp0 := phi_nonneg s R ν
    have hp1 := phi_le_one (s := s) hR hν
    have hbd : phiR s R ν * (ν - κ + c) ≤ x₀ + |κ| + c := by
      rcases le_total 0 (ν - κ + c) with h0 | h0
      · nlinarith [neg_le_abs κ, mul_le_mul_of_nonneg_right hp1 h0]
      · nlinarith [abs_nonneg κ, mul_nonpos_of_nonneg_of_nonpos hp0 h0]
    have := mul_le_mul_of_nonneg_right hbd hn
    linarith [hN h]
  · rw [if_neg hx]
    have hA := hA12 ν h (not_lt.mp hx) hh
    by_cases hνR : ν < R
    · rw [phi_eq hν hνR]
      nlinarith [hlow, mul_nonneg (mul_nonneg hd0 hc) hn]
    · rw [phi_zero hR (not_lt.mp hνR)]
      simpa using hN h

end FormEigenMonotone

theorem basis_form_sum_of_gain : A0 → FunctionalCalculusLaws → A12 → BasisSumAsFormValues → A13 := by
  intro hA0 hA11 hA12 hA13a
  unfold A0 FunctionalCalculusLaws A12 BasisSumAsFormValues A13 ForBas ForMod at *
  intro n ε V i1 i2 E hM ι b μ hEB κ hκ c hc
  obtain ⟨-, -, hmono, hadd, -, hconst, -⟩ := hA11 n ε V E hM ι b μ hEB
  obtain ⟨s, x₀, hs, hx₀, hb12⟩ := hA12 n ε V E hM ι b μ hEB κ hκ c hc
  have hA0' := fun w => ((hA0 n ε V E hM).2.2.2 κ hκ w).2.1
  have hK : 0 ≤ x₀ + |κ| + c := by linarith [abs_nonneg κ]
  refine ⟨s, x₀, x₀ + |κ| + c, hs, hK, ?_⟩
  intro R f S T hS hT
  have hTb : 0 ≤ (x₀ + |κ| + c) * ∑ i ∈ T, ‖f (b i)‖ ^ 2 :=
    mul_nonneg hK (Finset.sum_nonneg fun i _ => by positivity)
  rcases le_or_gt R 0 with hR | hR
  · have hSe : ∀ i ∈ S, False := fun i hi => by
      have := (hS i).1 hi
      linarith [hEB.nonneg i]
    rw [Finset.sum_eq_zero (s := S) (f := fun i => phiR s R (μ i) * ‖f (b i)‖ ^ 2)
        (fun i hi => (hSe i hi).elim),
      Finset.sum_eq_zero (s := S) (f := fun i => phiR s R (μ i) *
        (∑ p ∈ nc ε, ‖f ((E p.1 p.2) (b i))‖ ^ 2 - (μ i - κ) * ‖f (b i)‖ ^ 2))
        (fun i hi => (hSe i hi).elim)]
    linarith
  · have hφS : ∀ i ∉ S, phiR s R (μ i) = 0 := fun i hi =>
      FormEigenMonotone.phi_zero hR (not_lt.mp fun h => hi ((hS i).2 h))
    obtain ⟨T', hST', hT'⟩ := hA13a n ε V E hM ι b μ hEB (phiR s R) S hφS
    have key1 := hT' f
    have hstep : ∀ ν ∈ Finset.image μ T',
        (phiR s R ν * (ν - κ + c) - (if ν < x₀ then x₀ + |κ| + c else 0)) *
          ∑ j ∈ T' with μ j = ν, ‖f (b j)‖ ^ 2 ≤
        (beta ε E (fc b μ (phiR s R)) (∑ j ∈ T' with μ j = ν, (starRingEnd ℂ) (f (b j)) • b j)
            (∑ j ∈ T' with μ j = ν, (starRingEnd ℂ) (f (b j)) • b j)).re := by
      intro ν hν
      obtain ⟨j0, -, rfl⟩ := Finset.mem_image.1 hν
      have hEig := FormEigenMonotone.eig_fib hEB.eig (μ j0) (T'.filter fun j => μ j = μ j0)
        (fun j hj => (Finset.mem_filter.1 hj).2) (fun j => (starRingEnd ℂ) (f (b j)))
      beta_reduce at hEig
      have hk := FormEigenMonotone.key (b := b) (μ := μ) hA0' hmono hadd hconst hb12 hc hR (μ j0)
        (hEB.nonneg j0) _ hEig
      rw [FormEigenMonotone.norm_fib hEB.on f] at hk
      linarith
    have hsum1 : ∑ ν ∈ Finset.image μ T', (phiR s R ν * (ν - κ + c) - (if ν < x₀ then x₀ + |κ| + c else 0)) *
          ∑ j ∈ T' with μ j = ν, ‖f (b j)‖ ^ 2
        = ∑ j ∈ T', (phiR s R (μ j) * (μ j - κ + c) - (if μ j < x₀ then x₀ + |κ| + c else 0)) *
          ‖f (b j)‖ ^ 2 := by
      apply Finset.sum_image'
      intro i _
      beta_reduce
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [(Finset.mem_filter.1 hj).2]
    have e := Finset.sum_subset hST' (f := fun j => phiR s R (μ j) * (μ j - κ + c) * ‖f (b j)‖ ^ 2)
      (fun j _ hj => by simp only [hφS j hj, zero_mul])
    have hsplit : ∑ j ∈ T', (phiR s R (μ j) * (μ j - κ + c) - (if μ j < x₀ then x₀ + |κ| + c else 0)) *
          ‖f (b j)‖ ^ 2
        = ∑ j ∈ S, phiR s R (μ j) * (μ j - κ) * ‖f (b j)‖ ^ 2 +
            c * ∑ j ∈ S, phiR s R (μ j) * ‖f (b j)‖ ^ 2
          - ∑ j ∈ T', (if μ j < x₀ then x₀ + |κ| + c else 0) * ‖f (b j)‖ ^ 2 := by
      simp only [sub_mul, Finset.sum_sub_distrib]
      congr 1
      rw [← e, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    have hTb2 : ∑ j ∈ T', (if μ j < x₀ then x₀ + |κ| + c else 0) * ‖f (b j)‖ ^ 2
        ≤ (x₀ + |κ| + c) * ∑ i ∈ T, ‖f (b i)‖ ^ 2 := by
      rw [Finset.mul_sum]
      calc ∑ j ∈ T', (if μ j < x₀ then x₀ + |κ| + c else 0) * ‖f (b j)‖ ^ 2
          = ∑ j ∈ T' with μ j < x₀, (x₀ + |κ| + c) * ‖f (b j)‖ ^ 2 := by
            rw [Finset.sum_filter]
            exact Finset.sum_congr rfl fun j _ => by split_ifs <;> simp
        _ ≤ ∑ i ∈ T, (x₀ + |κ| + c) * ‖f (b i)‖ ^ 2 := by
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · intro j hj
              exact (hT j).2 (Finset.mem_filter.1 hj).2
            · intro j _ _
              exact mul_nonneg hK (by positivity)
    have hle := Finset.sum_le_sum hstep
    rw [hsum1, hsplit, ← key1] at hle
    have hR2 : ∑ i ∈ S, phiR s R (μ i) *
          (∑ p ∈ nc ε, ‖f ((E p.1 p.2) (b i))‖ ^ 2 - (μ i - κ) * ‖f (b i)‖ ^ 2)
        = ∑ i ∈ S, phiR s R (μ i) * ∑ p ∈ nc ε, ‖f ((E p.1 p.2) (b i))‖ ^ 2
          - ∑ i ∈ S, phiR s R (μ i) * (μ i - κ) * ‖f (b i)‖ ^ 2 := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hR2]
    linarith

end PositivityTheory.CW

end
