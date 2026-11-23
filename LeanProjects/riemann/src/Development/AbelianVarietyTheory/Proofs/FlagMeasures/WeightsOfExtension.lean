import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsIsHaarMeasureSUJ
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.DSSU
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.SUWt

variable {n : ℕ}

abbrev dgm (θ : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℂ := Matrix.diagonal fun a => Complex.exp ((θ a : ℂ) * Complex.I)

lemma star_exp_mul (x : ℝ) : star (Complex.exp ((x : ℂ) * Complex.I)) * Complex.exp ((x : ℂ) * Complex.I) = 1 := by
  rw [Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]
  simp [Complex.conj_ofReal]

lemma dgm_mem_Kset (ε : Fin n → Bool) (θ : Fin n → ℝ) : dgm θ ∈ Kset ε := by
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff']
    rw [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
    rw [← Matrix.diagonal_one]
    congr 1
    funext a
    exact star_exp_mul (θ a)
  · simp only [dgm, Jm, Matrix.diagonal_mul_diagonal]
    congr 1
    funext a
    ring

lemma Kset_sub_UJset (ε : Fin n → Bool) {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) : k ∈ UJset ε := by
  obtain ⟨hu, hc⟩ := hk
  show kᴴ * Jm ε * k = Jm ε
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] at hu
  rw [Matrix.mul_assoc, ← hc, ← Matrix.mul_assoc, hu, Matrix.one_mul]

lemma KS_sub_SUset (ε : Fin n → Bool) {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ KS ε) : k ∈ SUset ε :=
  ⟨Kset_sub_UJset ε hk.1, hk.2⟩

lemma dgm_det (θ : Fin n → ℝ) : (dgm θ).det = Complex.exp (((∑ a, θ a : ℝ) : ℂ) * Complex.I) := by
  rw [Matrix.det_diagonal, Complex.ofReal_sum, Finset.sum_mul, Complex.exp_sum]

lemma dgm_mem_KS (ε : Fin n → Bool) (θ : Fin n → ℝ) (h : ∑ a, θ a = 0) : dgm θ ∈ KS ε :=
  ⟨dgm_mem_Kset ε θ, by rw [dgm_det, h]; simp⟩

lemma dgm_split (θ : Fin n → ℝ) (t : ℝ) :
    dgm θ = Complex.exp ((t : ℂ) * Complex.I) • dgm (fun a => θ a - t) := by
  simp only [dgm]
  rw [← Matrix.diagonal_smul]
  congr 1
  funext a
  simp only [Pi.smul_apply, smul_eq_mul, ← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma norm_exp_I (t : ℝ) : ‖Complex.exp ((t : ℂ) * Complex.I)‖ = 1 := Complex.norm_exp_ofReal_mul_I t

end GlobalTheory.SUWt

namespace GlobalTheory.SUWt

variable {n : ℕ}

lemma star_mul_self_of_norm {w : ℂ} (h : ‖w‖ = 1) : star w * w = 1 := by
  rw [Complex.star_def, Complex.conj_mul', h]; simp

lemma norm_det_of_Kset {ε : Fin n → Bool} {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) : ‖k.det‖ = 1 := by
  have hu := hk.1
  rw [Matrix.mem_unitaryGroup_iff'] at hu
  have h1 := congrArg Matrix.det hu
  rw [Matrix.det_mul, Matrix.det_one, Matrix.star_eq_conjTranspose, Matrix.det_conjTranspose, Complex.star_def,
    Complex.conj_mul'] at h1
  have h2 : ‖k.det‖ ^ 2 = 1 := by exact_mod_cast h1
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).1 h2

lemma Kset_decomp (hn : 1 ≤ n) (ε : Fin n → Bool) {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) :
    ∃ z : ℂ, ‖z‖ = 1 ∧ ∃ g ∈ KS ε, k = z • g := by
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq k.det (show 0 < n by omega)
  have hzn : ‖z‖ = 1 := by
    have : ‖z‖ ^ n = 1 := by rw [← norm_pow, hz, norm_det_of_Kset hk]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by omega)).1 this
  have hz0 : z ≠ 0 := by intro h; rw [h, norm_zero] at hzn; exact zero_ne_one hzn
  refine ⟨z, hzn, z⁻¹ • k, ⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · have hu := hk.1
    rw [Matrix.mem_unitaryGroup_iff'] at hu ⊢
    rw [star_smul, smul_mul_smul_comm, hu, star_mul_self_of_norm (by rw [norm_inv, hzn, inv_one]), one_smul]
  · rw [smul_mul_assoc, hk.2, mul_smul_comm]
  · rw [Matrix.det_smul, Fintype.card_fin, inv_pow, hz, inv_mul_cancel₀]
    rw [← hz]; exact pow_ne_zero _ hz0
  · rw [smul_smul, mul_inv_cancel₀ hz0, one_smul]

section
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

lemma ext_eq {ε : Fin n → Bool} {m : ℤ} {π' π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (he : Ext ε m π' π)
    {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ SUset ε) : π g = π' g := by
  have := he 1 (by simp) g hg
  simpa using this

end

end GlobalTheory.SUWt

namespace GlobalTheory.SUWt

variable {n : ℕ}

section
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {ε : Fin n → Bool} {m : ℤ} {π' π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

lemma pi_dgm (he : Ext ε m π' π) (θ : Fin n → ℝ) (t : ℝ) (h : ∑ a, (θ a - t) = 0) :
    π (dgm θ) = Complex.exp (((t * m : ℝ) : ℂ) * Complex.I) • π' (dgm fun a => θ a - t) := by
  rw [dgm_split θ t, he _ (norm_exp_I t) _ (KS_sub_SUset ε (dgm_mem_KS ε _ h)), ← Complex.exp_int_mul]
  congr 2
  push_cast; ring

lemma sum_eq_of_wt (he : Ext ε m π' π) {μ : Fin n → ℝ} {v : H} (hv : v ≠ 0) (hw : IsWtOn (Kset ε) π μ v) :
    ∑ a, μ a = (m : ℝ) := by
  have h0 : π' (dgm fun _ : Fin n => (0 : ℝ)) v = v := by
    have h1 := hw (fun _ => 0) (dgm_mem_Kset ε _)
    rw [ext_eq he (KS_sub_SUset ε (dgm_mem_KS ε _ (by simp)))] at h1
    simpa using h1
  by_contra hne
  have hd : ∑ a, μ a - (m : ℝ) ≠ 0 := sub_ne_zero.2 hne
  set t : ℝ := Real.pi / (∑ a, μ a - m) with ht
  have h2 := hw (fun _ => t) (dgm_mem_Kset ε _)
  rw [pi_dgm he (fun _ => t) t (by simp)] at h2
  simp only [sub_self] at h2
  rw [ContinuousLinearMap.smul_apply, h0] at h2
  have h4 := smul_left_injective ℂ hv h2
  have h5 : Complex.exp (((∑ a, μ a * t - t * m : ℝ) : ℂ) * Complex.I) = 1 := by
    rw [show ((∑ a, μ a * t - t * m : ℝ) : ℂ) * Complex.I =
        ((∑ a, μ a * t : ℝ) : ℂ) * Complex.I - ((t * m : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.exp_sub, ← h4, div_self (Complex.exp_ne_zero _)]
  have h6 : ∑ a, μ a * t - t * m = Real.pi := by
    rw [← Finset.sum_mul, ht]; field_simp
  rw [h6, Complex.exp_pi_mul_I] at h5
  norm_num at h5

end

end GlobalTheory.SUWt

namespace GlobalTheory.SUWt

variable {n : ℕ}

section
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {ε : Fin n → Bool} {m : ℤ} {π' π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

lemma wt_iff (hn : 1 ≤ n) (he : Ext ε m π' π) (μ : Fin n → ℝ) (v : H) (hv : v ≠ 0) :
    IsWtOn (Kset ε) π μ v ↔ ∑ a, μ a = (m : ℝ) ∧ IsWtS π' (fun a => μ a - (m : ℝ) / n) v := by
  constructor
  · intro hw
    refine ⟨sum_eq_of_wt he hv hw, fun θ hθ => ?_⟩
    have h1 := hw θ (dgm_mem_Kset ε θ)
    rw [ext_eq he (KS_sub_SUset ε (dgm_mem_KS ε θ hθ))] at h1
    show π' (dgm θ) v = _
    rw [h1]
    congr 4
    simp only [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum, hθ, mul_zero, sub_zero]
  · rintro ⟨hs, hw⟩ θ _
    have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
    set t : ℝ := (∑ a, θ a) / n with ht
    have hz : ∑ a, (θ a - t) = 0 := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ht]
      field_simp
      ring
    have h2 := hw (fun a => θ a - t) hz
    simp only at h2
    show π (dgm θ) v = _
    rw [pi_dgm he θ t hz, ContinuousLinearMap.smul_apply, h2, smul_smul, ← Complex.exp_add]
    have key : ∑ a, (μ a - (m : ℝ) / n) * (θ a - t) = ∑ a, μ a * θ a - t * m := by
      have : ∑ a, (μ a - (m : ℝ) / n) * (θ a - t) =
          ∑ a, μ a * θ a - t * ∑ a, μ a - (m : ℝ) / n * ∑ a, (θ a - t) := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
        congr 1; funext a; ring
      rw [this, hs, hz]; ring
    rw [key]
    congr 2
    push_cast; ring

end

end GlobalTheory.SUWt

namespace GlobalTheory.SUWt

variable {n : ℕ}

lemma above_shift (P : Fin n → Fin n → Prop) (μ Λ : Fin n → ℝ) (d : ℝ) :
    Above P (fun a => μ a - d) (fun a => Λ a - d) ↔ Above P μ Λ := by
  unfold Above
  refine exists_congr fun c => and_congr_right fun _ => ?_
  constructor
  · intro h; funext a; have := congrFun h a
    simp only [Pi.add_apply, Finset.sum_apply] at this ⊢; linarith
  · intro h; funext a; have := congrFun h a
    simp only [Pi.add_apply, Finset.sum_apply] at this ⊢; linarith

section
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {ε : Fin n → Bool} {m : ℤ} {π' π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

lemma stable_iff (hn : 1 ≤ n) (he : Ext ε m π' π) (S : Submodule ℂ H) :
    Stable (Kset ε) π S ↔ Stable (KS ε) π' S := by
  constructor
  · intro h g hg v hv
    rw [← ext_eq he (KS_sub_SUset ε hg)]
    exact h g hg.1 v hv
  · intro h k hk v hv
    obtain ⟨z, hz, g, hg, rfl⟩ := Kset_decomp hn ε hk
    rw [he z hz g (KS_sub_SUset ε hg), ContinuousLinearMap.smul_apply]
    exact S.smul_mem _ (h g hg v hv)

lemma ktype_iff (hn : 1 ≤ n) (he : Ext ε m π' π) (lam Λ : Fin n → ℝ) (c : ℝ) (S : Submodule ℂ H) :
    IsKTypeU ε lam π Λ S ↔
      ∑ a, Λ a = (m : ℝ) ∧ IsKTypeS ε (fun a => lam a - c) π' (fun a => Λ a - (m : ℝ) / n) S := by
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hsum : ∀ ν : Fin n → ℝ, ∑ a, (ν a - (m : ℝ) / n) = ∑ a, ν a - m := by
    intro ν
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  have hst : ∀ S' : Submodule ℂ H, Stable (Kset ε) π S' ↔ Stable (KS ε) π' S' := stable_iff hn he
  simp only [IsKTypeU, IsKTypeS, sub_lt_sub_iff_right, hst]
  constructor
  · rintro ⟨hfd, hS, hirr, ⟨v, hvS, hv0, hvw⟩, hab⟩
    have hΛ := (wt_iff hn he Λ v hv0).1 hvw
    refine ⟨hΛ.1, by rw [hsum, hΛ.1, sub_self], hfd, hS, hirr, ⟨v, hvS, hv0, hΛ.2⟩, ?_⟩
    intro μ' w hμ' hwS hw0 hww
    have h1 : IsWtOn (Kset ε) π (fun a => μ' a + (m : ℝ) / n) w := by
      rw [wt_iff hn he _ w hw0]
      refine ⟨?_, ?_⟩
      · rw [Finset.sum_add_distrib, hμ', Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_div_cancel₀ _ hn0, zero_add]
      · simpa using hww
    have h2 := hab _ w hwS hw0 h1
    rw [← above_shift _ _ _ ((m : ℝ) / n)] at h2
    simpa using h2
  · rintro ⟨hΛs, -, hfd, hS, hirr, ⟨v, hvS, hv0, hvw⟩, hab⟩
    refine ⟨hfd, hS, hirr, ⟨v, hvS, hv0, (wt_iff hn he Λ v hv0).2 ⟨hΛs, hvw⟩⟩, ?_⟩
    intro μ w hwS hw0 hww
    obtain ⟨hμs, hμw⟩ := (wt_iff hn he μ w hw0).1 hww
    have h3 := hab _ w (by rw [hsum, hμs, sub_self]) hwS hw0 hμw
    exact (above_shift _ _ _ _).1 h3

end

end GlobalTheory.SUWt

open GlobalTheory.SUWt in

theorem GlobalTheory.SUWt.wt_ktype_ext : ∀ (n : ℕ), 1 ≤ n → ∀ (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (m : ℤ) (π' π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), Ext ε m π' π → (∀ (μ : Fin n → ℝ) (v : H), v ≠ 0 → (IsWtOn (Kset ε) π μ v ↔ ∑ a, μ a = (m : ℝ) ∧ IsWtS π' (fun a => μ a - (m : ℝ) / n) v)) ∧ ∀ (lam Λ : Fin n → ℝ) (c : ℝ) (S : Submodule ℂ H), IsKTypeU ε lam π Λ S ↔ ∑ a, Λ a = (m : ℝ) ∧ IsKTypeS ε (fun a => lam a - c) π' (fun a => Λ a - (m : ℝ) / n) S := by
  intro n hn ε H _ _ m π' π he
  exact ⟨fun μ v hv => wt_iff hn he μ v hv, fun lam Λ c S => ktype_iff hn he lam Λ c S⟩
