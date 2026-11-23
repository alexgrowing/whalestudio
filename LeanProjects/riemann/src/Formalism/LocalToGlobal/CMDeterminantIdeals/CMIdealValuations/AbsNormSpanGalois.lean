import Formalism.LocalToGlobal.CMDeterminantIdeals.CoeffMemOfLoc
import Formalism.LocalToGlobal.CMDeterminantIdeals.StatementA
import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.OneLeAbsNormOfLeOne

noncomputable section

namespace Formalism.L2.LamCM

open NumberField IsDedekindDomain
open scoped nonZeroDivisors

private lemma absNorm_le_absNorm_of_le {K : Type} [Field K] [NumberField K] (I J : FractionalIdeal (𝓞 K)⁰ K)
    (hJ : J ≠ 0) (hJI : J ≤ I) : FractionalIdeal.absNorm I ≤ FractionalIdeal.absNorm J := by
  have hI : I ≠ 0 := by
    rintro rfl
    exact hJ (FractionalIdeal.le_zero_iff.mp hJI)
  have h1 : J * I⁻¹ ≤ 1 := by
    rw [← mul_inv_cancel₀ hI, FractionalIdeal.mul_le]
    intro x hx y hy
    exact FractionalIdeal.mul_mem_mul (hJI hx) hy
  obtain ⟨A, hA⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.mp h1
  have hJeq : J = (A : FractionalIdeal (𝓞 K)⁰ K) * I := by
    rw [hA, mul_assoc, inv_mul_cancel₀ hI, mul_one]
  have hA0 : A ≠ ⊥ := by
    rintro rfl
    apply hJ
    rw [hJeq, FractionalIdeal.coeIdeal_bot, zero_mul]
  have hAn : (1:ℚ) ≤ FractionalIdeal.absNorm (A : FractionalIdeal (𝓞 K)⁰ K) := by
    rw [FractionalIdeal.coeIdeal_absNorm]
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hA0)
  have hIn : (0:ℚ) ≤ FractionalIdeal.absNorm I := FractionalIdeal.absNorm_nonneg I
  rw [hJeq, map_mul]
  nlinarith

private lemma prod_norm_embedding_eq_abs_norm {K : Type} [Field K] [NumberField K] (x : K) :
    ∏ σ : K →+* ℂ, ‖σ x‖ = |((Algebra.norm ℚ x : ℚ) : ℝ)| := by
  have h := Algebra.norm_eq_prod_embeddings ℚ ℂ x
  rw [← Fintype.prod_equiv (RingHom.equivRatAlgHom K ℂ) (fun σ => σ x) (fun τ => τ x) (fun σ => rfl)] at h
  rw [← norm_prod, ← h]
  simp

theorem lambda_endomorphism : LamEnd := by
  unfold LamEnd
  intro K _ _ NN cf S B hG hcf hmem hS hB hlen
  have hI0 : NN.I ≠ 0 := hG.1
  have hJ0 : FractionalIdeal.spanSingleton (𝓞 K)⁰ cf ≠ 0 := FractionalIdeal.spanSingleton_eq_zero_iff.not.mpr hcf
  have hJI : FractionalIdeal.spanSingleton (𝓞 K)⁰ cf ≤ NN.I := FractionalIdeal.spanSingleton_le_iff_mem.mpr hmem
  have hle := absNorm_le_absNorm_of_le NN.I _ hJ0 hJI
  rw [FractionalIdeal.absNorm_span_singleton] at hle
  have hNpos : (0:ℝ) < ((FractionalIdeal.absNorm NN.I : ℚ) : ℝ) := by
    have h0 : (0:ℚ) < FractionalIdeal.absNorm NN.I :=
      lt_of_le_of_ne (FractionalIdeal.absNorm_nonneg _) (Ne.symm ((map_ne_zero _).mpr hI0))
    exact_mod_cast h0
  have hle' : ((FractionalIdeal.absNorm NN.I : ℚ) : ℝ) ≤ ∏ σ : K →+* ℂ, ‖σ cf‖ := by
    rw [prod_norm_embedding_eq_abs_norm]
    exact_mod_cast hle
  have hσ : ∀ σ : K →+* ℂ, 0 < ‖σ cf‖ := fun σ => norm_pos_iff.mpr ((map_ne_zero σ).mpr hcf)
  have hlog1 : Real.log ((FractionalIdeal.absNorm NN.I : ℚ) : ℝ) ≤ ∑ σ : K →+* ℂ, Real.log ‖σ cf‖ := by
    rw [← Real.log_prod (fun σ _ => (hσ σ).ne')]
    exact Real.log_le_log hNpos hle'
  have hlog2 : ∀ σ : K →+* ℂ, Real.log ‖σ cf‖ + Real.log (NN.n σ) ≤ Real.log (S σ) + Real.log B := by
    intro σ
    rw [← Real.log_mul (hσ σ).ne' (hG.2 σ).ne', ← Real.log_mul (hS σ).ne' hB.ne']
    exact Real.log_le_log (mul_pos (hσ σ) (hG.2 σ)) (hlen σ)
  have hsum := Finset.sum_le_sum (fun σ (_ : σ ∈ Finset.univ) => hlog2 σ)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    NumberField.Embeddings.card K ℂ, nsmul_eq_mul] at hsum
  have e : NN.deg = - Real.log ((FractionalIdeal.absNorm NN.I : ℚ) : ℝ) - ∑ σ, Real.log (NN.n σ) := rfl
  rw [e]
  linarith

lemma log_two_pi_le_two : Real.log (2 * Real.pi) ≤ 2 := by
  have hpi := Real.pi_lt_d2
  have he := Real.exp_one_gt_d9
  rw [Real.log_le_iff_le_exp (by positivity)]
  have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
  rw [h2]
  nlinarith

lemma finrank_pos_real (K : Type) [Field K] [NumberField K] : (0 : ℝ) < (Module.finrank ℚ K : ℝ) := by
  exact Nat.cast_pos.mpr Module.finrank_pos

private lemma mLine_deg_dual {K : Type} [Field K] [NumberField K] (L : MLine K) : L.dual.deg = - L.deg := by
  simp only [MLine.deg, MLine.dual, map_inv₀, Rat.cast_inv, Real.log_inv, Finset.sum_neg_distrib]
  ring

theorem degree_delta_base : DegDe0 := by
  unfold DegDe0
  intro K _ _ g abelian₂ ℓ de La logOm h
  unfold CMNumbers0 at h
  obtain ⟨-, -, -, hLa, hsum, hnd, hdd⟩ := h
  have hd : (0:ℝ) < (Module.finrank ℚ K : ℝ) := finrank_pos_real K
  have hdeg : ∀ j, (ℓ j).deg = logOm / 2 * (Module.finrank ℚ K : ℝ) := fun j => by
    have e : (ℓ j).ndeg = (ℓ j).deg / (Module.finrank ℚ K : ℝ) := rfl
    rw [← hnd j, e, div_mul_cancel₀ _ hd.ne']
  have hs : ∑ j, (ℓ j).deg = (g : ℝ) * (logOm / 2 * (Module.finrank ℚ K : ℝ)) := by
    simp [hdeg]
  have hdual : abelian₂.dual.ndeg = - abelian₂.ndeg := by
    have e1 : abelian₂.dual.ndeg = abelian₂.dual.deg / (Module.finrank ℚ K : ℝ) := rfl
    have e2 : abelian₂.ndeg = abelian₂.deg / (Module.finrank ℚ K : ℝ) := rfl
    rw [e1, e2, mLine_deg_dual, neg_div]
  have hLamn : (g : ℝ) * (logOm / 2) - (g : ℝ) * Real.log La ≤ abelian₂.ndeg := by
    have e2 : abelian₂.ndeg = abelian₂.deg / (Module.finrank ℚ K : ℝ) := rfl
    rw [e2, le_div_iff₀ hd]
    rw [hs] at hsum
    linarith
  have hg : (0:ℝ) ≤ g := Nat.cast_nonneg g
  have h1 : (g:ℝ) * Real.log (2 * Real.pi) ≤ (g:ℝ) * 2 := mul_le_mul_of_nonneg_left log_two_pi_le_two hg
  have h2 : (g:ℝ) * (-logOm) ≤ (g:ℝ) * |logOm| := mul_le_mul_of_nonneg_left (neg_le_abs logOm) hg
  have h3 : (0:ℝ) ≤ (g:ℝ) * |logOm| := mul_nonneg hg (abs_nonneg logOm)
  unfold pDeg
  rw [hdual] at hdd
  linarith

private lemma mLine_good_pow {K : Type} [Field K] [NumberField K] (L : MLine K) (hL : L.Good) (k : ℕ) :
    (L.pow k).Good := by
  unfold MLine.Good at *
  exact ⟨pow_ne_zero _ hL.1, fun σ => pow_pos (hL.2 σ) _⟩

private lemma mLine_good_dual {K : Type} [Field K] [NumberField K] (L : MLine K) (hL : L.Good) : L.dual.Good := by
  unfold MLine.Good at *
  exact ⟨inv_ne_zero hL.1, fun σ => inv_pos.mpr (hL.2 σ)⟩

private lemma mLine_good_tensor {K : Type} [Field K] [NumberField K] (L M : MLine K) (hL : L.Good) (hM : M.Good) :
    (L.tensor M).Good := by
  unfold MLine.Good at *
  exact ⟨mul_ne_zero hL.1 hM.1, fun σ => mul_pos (hL.2 σ) (hM.2 σ)⟩

private lemma mLine_good_prodPow {K : Type} [Field K] [NumberField K] {V : Type} [Fintype V] (ℓ : V → MLine K)
    (k : V → ℕ) (h : ∀ v, (ℓ v).Good) : (MLine.prodPow ℓ k).Good := by
  unfold MLine.Good at *
  exact ⟨Finset.prod_ne_zero_iff.mpr fun v _ => pow_ne_zero _ (h v).1,
    fun σ => Finset.prod_pos fun v _ => pow_pos ((h v).2 σ) _⟩

private lemma mLine_deg_tensor {K : Type} [Field K] [NumberField K] (L M : MLine K) (hL : L.Good) (hM : M.Good) :
    (L.tensor M).deg = L.deg + M.deg := by
  have hL0 : ((FractionalIdeal.absNorm L.I : ℚ) : ℝ) ≠ 0 := Rat.cast_ne_zero.mpr ((map_ne_zero _).mpr hL.1)
  have hM0 : ((FractionalIdeal.absNorm M.I : ℚ) : ℝ) ≠ 0 := Rat.cast_ne_zero.mpr ((map_ne_zero _).mpr hM.1)
  simp only [MLine.deg, MLine.tensor, map_mul, Rat.cast_mul]
  rw [Real.log_mul hL0 hM0, Finset.sum_congr rfl (fun σ _ => Real.log_mul (hL.2 σ).ne' (hM.2 σ).ne'),
    Finset.sum_add_distrib]
  ring

private lemma mLine_deg_pow {K : Type} [Field K] [NumberField K] (L : MLine K) (k : ℕ) :
    (L.pow k).deg = k * L.deg := by
  simp only [MLine.deg, MLine.pow, map_pow, Rat.cast_pow, Real.log_pow]
  rw [mul_sub, Finset.mul_sum]
  ring

private lemma mLine_deg_prodPow {K : Type} [Field K] [NumberField K] {V : Type} [Fintype V] (ℓ : V → MLine K)
    (k : V → ℕ) (h : ∀ v, (ℓ v).Good) : (MLine.prodPow ℓ k).deg = ∑ v, (k v : ℝ) * (ℓ v).deg := by
  have hN : ∀ v, ((FractionalIdeal.absNorm (ℓ v).I : ℚ) : ℝ) ≠ 0 := fun v =>
    Rat.cast_ne_zero.mpr ((map_ne_zero _).mpr (h v).1)
  simp only [MLine.deg, MLine.prodPow, map_prod, map_pow, Rat.cast_prod, Rat.cast_pow]
  rw [Real.log_prod (fun v _ => pow_ne_zero _ (hN v))]
  rw [Finset.sum_congr rfl (fun σ _ => Real.log_prod (fun v _ => (pow_pos ((h v).2 σ) _).ne'))]
  simp only [Real.log_pow]
  rw [Finset.sum_comm]
  simp only [mul_sub, mul_neg, Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_neg_distrib]

theorem degree_norm_base : DegNN0 := by
  unfold DegNN0
  intro K _ _ g abelian₂ ℓ de La logOm V _ c μ n h
  have hde0 := degree_delta_base K g abelian₂ ℓ de La logOm h
  unfold CMNumbers0 at h
  obtain ⟨-, hℓ, hde, hLa, -, hnd, -⟩ := h
  have hP : (MLine.prodPow (fun v => ℓ (c v)) μ).Good := mLine_good_prodPow _ _ (fun v => hℓ (c v))
  have hPd : (MLine.prodPow (fun v => ℓ (c v)) μ).dual.Good := mLine_good_dual _ hP
  have hdn : (de.pow n).Good := mLine_good_pow _ hde n
  have hG : (lineNN de ℓ c μ n).Good := mLine_good_tensor _ _ hdn hPd
  refine ⟨hG, ?_⟩
  have hd : (0:ℝ) < (Module.finrank ℚ K : ℝ) := finrank_pos_real K
  have hd0 : (Module.finrank ℚ K : ℝ) ≠ 0 := hd.ne'
  have hdeg : ∀ j, (ℓ j).deg = logOm / 2 * (Module.finrank ℚ K : ℝ) := fun j => by
    have e : (ℓ j).ndeg = (ℓ j).deg / (Module.finrank ℚ K : ℝ) := rfl
    rw [← hnd j, e, div_mul_cancel₀ _ hd0]
  have hD : (lineNN de ℓ c μ n).deg =
      n * de.deg - (∑ v, (μ v : ℝ)) * (logOm / 2 * (Module.finrank ℚ K : ℝ)) := by
    have e : lineNN de ℓ c μ n = (de.pow n).tensor (MLine.prodPow (fun v => ℓ (c v)) μ).dual := rfl
    rw [e, mLine_deg_tensor _ _ hdn hPd, mLine_deg_dual, mLine_deg_pow, mLine_deg_prodPow _ _ (fun v => hℓ (c v))]
    simp only [hdeg, Finset.sum_mul]
    ring
  have hlog : 0 ≤ Real.log La := Real.log_nonneg hLa
  have hPl : -(logOm / 2) ≤ pDeg logOm + (1 / 2) * Real.log La := by
    unfold pDeg
    have := neg_le_abs logOm
    linarith
  have hsμ : (0:ℝ) ≤ ∑ v, (μ v : ℝ) := Finset.sum_nonneg (fun v _ => Nat.cast_nonneg _)
  have hn : (0:ℝ) ≤ n := Nat.cast_nonneg n
  have h1 : (n:ℝ) * de.ndeg ≤ n * (g * (pDeg logOm + (1 / 2) * Real.log La)) := mul_le_mul_of_nonneg_left hde0 hn
  have h2 : (∑ v, (μ v : ℝ)) * (-(logOm / 2)) ≤ (∑ v, (μ v : ℝ)) * (pDeg logOm + (1 / 2) * Real.log La) :=
    mul_le_mul_of_nonneg_left hPl hsμ
  have e2 : (lineNN de ℓ c μ n).ndeg = (lineNN de ℓ c μ n).deg / (Module.finrank ℚ K : ℝ) := rfl
  have e3 : de.ndeg = de.deg / (Module.finrank ℚ K : ℝ) := rfl
  have hnd' : (lineNN de ℓ c μ n).ndeg = n * de.ndeg - (∑ v, (μ v : ℝ)) * (logOm / 2) := by
    rw [e2, e3, hD, sub_div, mul_div_assoc]
    congr 1
    field_simp
  rw [hnd']
  linarith

theorem CMNumbersLink_of (hH : HadamardIdeals) (hD : DetGood) : CMNumbersLink := by
  unfold CMNumbersLink
  intro K _ _ g Lie ℓ u de La logOm h
  unfold CMNumbers at h
  unfold CMNumbers0
  obtain ⟨hL, hℓ, hde, hu, hmem, hLa, hsq, hnd, hdd⟩ := h
  exact ⟨(hD K g Lie hL).2, hℓ, hde, hLa, hH K g Lie ℓ u La hL hℓ hu hmem (by linarith) hsq, hnd, hdd⟩

theorem DegDe_of (hH : HadamardIdeals) (hD : DetGood) : DegDe := by
  unfold DegDe
  intro K _ _ g Lie ℓ u de La logOm h
  exact degree_delta_base K g _ ℓ de La logOm (CMNumbersLink_of hH hD K g Lie ℓ u de La logOm h)

theorem DegNN_of (hH : HadamardIdeals) (hD : DetGood) : DegNN := by
  unfold DegNN
  intro K _ _ g Lie ℓ u de La logOm V _ c μ n h
  exact degree_norm_base K g _ ℓ de La logOm V c μ n (CMNumbersLink_of hH hD K g Lie ℓ u de La logOm h)

section cauchy

lemma geom_root_sum {ζ : ℂ} {N : ℕ} (hζ : IsPrimitiveRoot ζ N) {a b : ℕ} (ha : a < N) (hb : b < N) :
    ∑ j ∈ Finset.range N, (ζ ^ a * ζ⁻¹ ^ b) ^ j = if a = b then (N : ℂ) else 0 := by
  have hN : 0 < N := lt_of_le_of_lt (Nat.zero_le a) ha
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hN.ne'
  split_ifs with hab
  · subst hab
    simp [mul_inv_cancel₀ (pow_ne_zero a hζ0)]
  · have hne : ζ ^ a * ζ⁻¹ ^ b ≠ 1 := by
      intro h
      apply hab
      apply hζ.pow_inj ha hb
      rw [inv_pow] at h
      exact (mul_inv_eq_one₀ (pow_ne_zero _ hζ0)).mp h
    rw [geom_sum_eq hne]
    have h1 : (ζ ^ a) ^ N = 1 := by rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
    have h2 : (ζ⁻¹ ^ b) ^ N = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, inv_pow, hζ.pow_eq_one, inv_one, one_pow]
    rw [mul_pow, h1, h2, one_mul, sub_self, zero_div]

theorem coeff_cauchy_bound : CoeffCauchy := by
  unfold CoeffCauchy
  intro V _ G ρ S μ hρ hS
  classical
  set N : ℕ := (∑ ν ∈ G.support, ∑ v, ν v) + (∑ v, μ v) + 1 with hNdef
  have hN : 0 < N := Nat.succ_pos _
  have hνN : ∀ ν ∈ G.support, ∀ v, ν v < N := by
    intro ν hν v
    have h1 : ν v ≤ ∑ w, ν w := Finset.single_le_sum (fun w _ => Nat.zero_le _) (Finset.mem_univ v)
    have h2 : ∑ w, ν w ≤ ∑ ν' ∈ G.support, ∑ w, ν' w :=
      Finset.single_le_sum (f := fun ν' => ∑ w, ν' w) (fun _ _ => Nat.zero_le _) hν
    omega
  have hμN : ∀ v, μ v < N := by
    intro v
    have h1 : μ v ≤ ∑ w, μ w := Finset.single_le_sum (fun w _ => Nat.zero_le _) (Finset.mem_univ v)
    omega
  set ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / N) with hζdef
  have hζ : IsPrimitiveRoot ζ N := Complex.isPrimitiveRoot_exp N hN.ne'
  have hζn : ‖ζ‖ = 1 := hζ.norm'_eq_one hN.ne'
  let z : (V → Fin N) → V → ℂ := fun k v => (ρ v : ℂ) * ζ ^ (k v : ℕ)
  have hz : ∀ k v, ‖z k v‖ ≤ ρ v := by
    intro k v
    simp only [z, norm_mul, norm_pow, hζn, one_pow, mul_one, Complex.norm_real, Real.norm_eq_abs]
    exact le_of_eq (abs_of_pos (hρ v))
  have inner : ∀ ν ∈ G.support, ∑ k : V → Fin N,
      MvPolynomial.coeff ν G * (∏ v, z k v ^ ν v) * ∏ v, ζ⁻¹ ^ ((k v : ℕ) * μ v) =
      if ν = μ then (N : ℂ) ^ Fintype.card V * (MvPolynomial.coeff μ G * ∏ v, (ρ v : ℂ) ^ μ v) else 0 := by
    intro ν hν
    have hprod : ∀ k : V → Fin N, (∏ v, z k v ^ ν v) * ∏ v, ζ⁻¹ ^ ((k v : ℕ) * μ v) =
        (∏ v, (ρ v : ℂ) ^ ν v) * ∏ v, (ζ ^ ν v * ζ⁻¹ ^ μ v) ^ (k v : ℕ) := by
      intro k
      rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl (fun v _ => by simp only [z]; ring)
    have hsum1 : ∑ k : V → Fin N, MvPolynomial.coeff ν G * (∏ v, z k v ^ ν v) * ∏ v, ζ⁻¹ ^ ((k v : ℕ) * μ v) =
        MvPolynomial.coeff ν G * ((∏ v, (ρ v : ℂ) ^ ν v) *
          ∑ k : V → Fin N, ∏ v, (ζ ^ ν v * ζ⁻¹ ^ μ v) ^ (k v : ℕ)) := by
      rw [Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun k _ => by rw [mul_assoc, hprod k])
    have hsumk : ∑ k : V → Fin N, ∏ v, (ζ ^ ν v * ζ⁻¹ ^ μ v) ^ (k v : ℕ) =
        ∏ v, ∑ j : Fin N, (ζ ^ ν v * ζ⁻¹ ^ μ v) ^ (j : ℕ) := by
      rw [Fintype.prod_sum]
    have hgeom : ∀ v, ∑ j : Fin N, (ζ ^ ν v * ζ⁻¹ ^ μ v) ^ (j : ℕ) = if ν v = μ v then (N : ℂ) else 0 := fun v =>
      (Fin.sum_univ_eq_sum_range (fun j => (ζ ^ ν v * ζ⁻¹ ^ μ v) ^ j) N).trans
        (geom_root_sum hζ (hνN ν hν v) (hμN v))
    have hprodif : ∏ v, (if ν v = μ v then (N : ℂ) else 0) = if ν = μ then (N : ℂ) ^ Fintype.card V else 0 := by
      split_ifs with h
      · simp [h]
      · obtain ⟨v, hv⟩ : ∃ v, ν v ≠ μ v := by
          by_contra hc
          push_neg at hc
          exact h (Finsupp.ext hc)
        exact Finset.prod_eq_zero (Finset.mem_univ v) (if_neg hv)
    rw [hsum1, hsumk, Finset.prod_congr rfl (fun v _ => hgeom v), hprodif]
    split_ifs with h
    · rw [h]
      ring
    · simp
  have hexp : ∀ k : V → Fin N, MvPolynomial.eval (z k) G * ∏ v, ζ⁻¹ ^ ((k v : ℕ) * μ v) =
      ∑ ν ∈ G.support, MvPolynomial.coeff ν G * (∏ v, z k v ^ ν v) * ∏ v, ζ⁻¹ ^ ((k v : ℕ) * μ v) := by
    intro k
    rw [MvPolynomial.eval_eq', Finset.sum_mul]
  have key : ∑ k : V → Fin N, MvPolynomial.eval (z k) G * ∏ v, ζ⁻¹ ^ ((k v : ℕ) * μ v) =
      (N : ℂ) ^ Fintype.card V * (MvPolynomial.coeff μ G * ∏ v, (ρ v : ℂ) ^ μ v) := by
    rw [Finset.sum_congr rfl (fun k _ => hexp k), Finset.sum_comm, Finset.sum_congr rfl inner]
    rw [Finset.sum_eq_single μ (fun ν _ hν => if_neg hν) (fun hμ => by
      have h0 : MvPolynomial.coeff μ G = 0 := by
        by_contra h
        exact hμ (MvPolynomial.mem_support_iff.mpr h)
      rw [if_pos rfl, h0]
      simp)]
    rw [if_pos rfl]
  have hbound : ‖(N : ℂ) ^ Fintype.card V * (MvPolynomial.coeff μ G * ∏ v, (ρ v : ℂ) ^ μ v)‖ ≤
      (N : ℝ) ^ Fintype.card V * S := by
    rw [← key]
    calc ‖∑ k : V → Fin N, MvPolynomial.eval (z k) G * ∏ v, ζ⁻¹ ^ ((k v : ℕ) * μ v)‖
        ≤ ∑ k : V → Fin N, ‖MvPolynomial.eval (z k) G * ∏ v, ζ⁻¹ ^ ((k v : ℕ) * μ v)‖ := norm_sum_le _ _
      _ ≤ ∑ _k : V → Fin N, S := by
          apply Finset.sum_le_sum
          intro k _
          rw [norm_mul, norm_prod]
          simp only [norm_pow, norm_inv, hζn, inv_one, one_pow, Finset.prod_const_one, mul_one]
          exact hS (z k) (hz k)
      _ = (N : ℝ) ^ Fintype.card V * S := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow]
  simp only [norm_mul, norm_pow, norm_prod, Complex.norm_real, Real.norm_eq_abs, Complex.norm_natCast] at hbound
  have hpos : (0:ℝ) < (N : ℝ) ^ Fintype.card V := pow_pos (Nat.cast_pos.mpr hN) _
  have habs : ∏ v, |ρ v| ^ μ v = ∏ v, ρ v ^ μ v :=
    Finset.prod_congr rfl (fun v _ => by rw [abs_of_pos (hρ v)])
  rw [habs] at hbound
  exact le_of_mul_le_mul_left hbound hpos

end cauchy

theorem lambda_number_base : LamNumber0 := by
  intro K _ _ g abelian₂ ℓ de La logOm V _ c G μ n S Rr h hcf hmem hS hRr hev
  obtain ⟨hNg, hNd⟩ := degree_norm_base K g abelian₂ ℓ de La logOm V c μ n h
  have hde := h.2.2.1
  have hℓ := h.2.1
  have hBpos : (0 : ℝ) < Rr ^ (∑ v, μ v) := pow_pos hRr _
  have hlen : ∀ σ, (lineNN de ℓ c μ n).len σ (MvPolynomial.coeff μ G) ≤ S σ * Rr ^ (∑ v, μ v) := by
    intro σ
    have hnv : ∀ v, 0 < (ℓ (c v)).n σ := fun v => (hℓ (c v)).2 σ
    have hdn : 0 < de.n σ ^ n := pow_pos (hde.2 σ) n
    have hC := coeff_cauchy_bound V (MvPolynomial.map σ G) (fun v => 1 / (ℓ (c v)).n σ)
      (S σ * Rr ^ (∑ v, μ v) / de.n σ ^ n) μ
      (fun v => one_div_pos.mpr (hnv v)) (fun z hz => by
        rw [le_div_iff₀ hdn]
        exact hev σ z (fun v => (le_div_iff₀ (hnv v)).mp (hz v)))
    rw [MvPolynomial.coeff_map, le_div_iff₀ hdn] at hC
    have hprod : ∏ v, (1 / (ℓ (c v)).n σ) ^ μ v = (∏ v, (ℓ (c v)).n σ ^ μ v)⁻¹ := by
      rw [← Finset.prod_inv_distrib]
      simp [one_div, inv_pow]
    rw [hprod] at hC
    simp only [MLine.len, lineNN, MLine.tensor, MLine.dual, MLine.pow, MLine.prodPow]
    calc ‖σ (MvPolynomial.coeff μ G)‖ * (de.n σ ^ n * (∏ v, (ℓ (c v)).n σ ^ μ v)⁻¹)
        = ‖σ (MvPolynomial.coeff μ G)‖ * (∏ v, (ℓ (c v)).n σ ^ μ v)⁻¹ * de.n σ ^ n := by ring
      _ ≤ S σ * Rr ^ (∑ v, μ v) := hC
  have hE := lambda_endomorphism K (lineNN de ℓ c μ n) (MvPolynomial.coeff μ G) S _ hNg hcf hmem hS hBpos hlen
  have hd := finrank_pos_real K
  have hlogB : Real.log (Rr ^ (∑ v, μ v)) = (∑ v, (μ v : ℝ)) * Real.log Rr := by
    rw [Real.log_pow]; push_cast; ring
  rw [le_div_iff₀ hd]
  have hN2 : (lineNN de ℓ c μ n).deg ≤
      ((pDeg logOm + (1 / 2) * Real.log La) * ((∑ v, (μ v : ℝ)) + (g : ℝ) * n)) * Module.finrank ℚ K := by
    have := hNd
    simp only [MLine.ndeg] at this
    rwa [div_le_iff₀ hd] at this
  rw [hlogB] at hE
  nlinarith

theorem LamNumber_of (hH : HadamardIdeals) (hD : DetGood) : LamNumber := by
  unfold LamNumber
  intro K _ _ g Lie ℓ u de La logOm V _ c G μ n S Rr h
  exact lambda_number_base K g _ ℓ de La logOm V c G μ n S Rr (CMNumbersLink_of hH hD K g Lie ℓ u de La logOm h)

section loc

variable {K : Type} [Field K] [NumberField K] {p : HeightOneSpectrum (𝓞 K)}

lemma IsLocGen.mul' {a b : K} {I J : FractionalIdeal (𝓞 K)⁰ K}
    (ha : IsLocGen p a I) (hb : IsLocGen p b J) (hI : I ≠ 0) (hJ : J ≠ 0) : IsLocGen p (a * b) (I * J) := by
  obtain ⟨ha0, hac⟩ := ha
  obtain ⟨hb0, hbc⟩ := hb
  refine ⟨mul_ne_zero ha0 hb0, ?_⟩
  have hsa : FractionalIdeal.spanSingleton (𝓞 K)⁰ a ≠ 0 := FractionalIdeal.spanSingleton_eq_zero_iff.not.mpr ha0
  have hsb : FractionalIdeal.spanSingleton (𝓞 K)⁰ b ≠ 0 := FractionalIdeal.spanSingleton_eq_zero_iff.not.mpr hb0
  rw [← FractionalIdeal.spanSingleton_mul_spanSingleton, FractionalIdeal.count_mul (K := K) (v := p) hsa hsb,
    FractionalIdeal.count_mul (K := K) (v := p) hI hJ, hac, hbc]

lemma IsLocGen.pow' {a : K} {I : FractionalIdeal (𝓞 K)⁰ K} (ha : IsLocGen p a I) (k : ℕ) :
    IsLocGen p (a ^ k) (I ^ k) := by
  obtain ⟨ha0, hac⟩ := ha
  refine ⟨pow_ne_zero _ ha0, ?_⟩
  rw [← FractionalIdeal.spanSingleton_pow, FractionalIdeal.count_pow, FractionalIdeal.count_pow, hac]

lemma IsLocGen.inv' {a : K} {I : FractionalIdeal (𝓞 K)⁰ K} (ha : IsLocGen p a I) : IsLocGen p a⁻¹ I⁻¹ := by
  obtain ⟨ha0, hac⟩ := ha
  refine ⟨inv_ne_zero ha0, ?_⟩
  rw [← FractionalIdeal.spanSingleton_inv, FractionalIdeal.count_inv, FractionalIdeal.count_inv, hac]

lemma IsLocGen.prod' {ι : Type} (s : Finset ι) (a : ι → K) (I : ι → FractionalIdeal (𝓞 K)⁰ K)
    (h : ∀ i, IsLocGen p (a i) (I i)) (hI : ∀ i, I i ≠ 0) : IsLocGen p (∏ i ∈ s, a i) (∏ i ∈ s, I i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty]
    exact ⟨one_ne_zero, by rw [FractionalIdeal.spanSingleton_one]⟩
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi]
    exact (h i).mul' ih (hI i) (Finset.prod_ne_zero_iff.mpr fun j _ => hI j)

end loc

theorem coeff_mem_of_local : CoeffMemOfLoc := by
  intro K _ _ g ℓ de V _ c μ n cf hde hℓ hloc
  have hP0 : (∏ v, (ℓ (c v)).I ^ μ v) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun v _ => pow_ne_zero _ (hℓ (c v)).1
  have hI0 : (lineNN de ℓ c μ n).I ≠ 0 := by
    simp only [lineNN, MLine.tensor, MLine.dual, MLine.pow, MLine.prodPow]
    exact mul_ne_zero (pow_ne_zero _ hde.1) (inv_ne_zero hP0)
  apply mem_of_loc' K _ cf hI0
  intro p
  obtain ⟨t, cl, ht, hcl, hv⟩ := hloc p
  have hG : IsLocGen p (∏ v, cl (c v) ^ μ v) (∏ v, (ℓ (c v)).I ^ μ v) :=
    IsLocGen.prod' _ _ _ (fun v => (hcl (c v)).pow' (μ v)) (fun v => pow_ne_zero _ (hℓ (c v)).1)
  refine ⟨t ^ n * (∏ v, cl (c v) ^ μ v)⁻¹, ?_, ?_⟩
  · simp only [lineNN, MLine.tensor, MLine.dual, MLine.pow, MLine.prodPow]
    exact (ht.pow' n).mul' hG.inv' (pow_ne_zero _ hde.1) (inv_ne_zero hP0)
  · have hne : p.valuation K (∏ v, cl (c v) ^ μ v) ≠ 0 := (Valuation.ne_zero_iff _).mpr hG.1
    rw [map_mul, map_inv₀]
    calc p.valuation K cf
        = p.valuation K (cf * ∏ v, cl (c v) ^ μ v) * (p.valuation K (∏ v, cl (c v) ^ μ v))⁻¹ := by
          rw [map_mul, mul_assoc, mul_inv_cancel₀ hne, mul_one]
      _ ≤ _ := by gcongr

section galois

variable {K : Type} [Field K] [NumberField K]

def compEquiv (γ : K ≃+* K) : (K →+* ℂ) ≃ (K →+* ℂ) where
  toFun σ := σ.comp (γ : K →+* K)
  invFun σ := σ.comp (γ.symm : K →+* K)
  left_inv σ := by ext x; simp
  right_inv σ := by ext x; simp

end galois

end Formalism.L2.LamCM
