import Formalism.FlagUnipotentLattices.CoveringRadius2
import Formalism.LogSumExpBounds.CharacterSumPhase.NuclearNormBoundHolds

open Finset MeasureTheory NumberField Matrix
open scoped ComplexOrder

namespace Formalism.HermitianLatticeCounting.P

open Formalism.HermitianLatticeCounting.S7
open Formalism.NuclearRankWeightBounds.D (lead hs q0)

lemma hs_sq_trace_b {N : ℕ} (Y : Matrix (Fin N) (Fin N) ℂ) :
    ((∑ a, ∑ b, ‖Y a b‖ ^ 2 : ℝ) : ℂ) = (Yᴴ * Y).trace := by
  simp only [trace, Matrix.diag, mul_apply, conjTranspose_apply]
  rw [Finset.sum_comm]
  push_cast
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [show star (Y b a) = (starRingEnd ℂ) (Y b a) from rfl, Complex.conj_mul']

lemma hs_unitary_conj_b {N : ℕ} (k X : Matrix (Fin N) (Fin N) ℂ) (hk : kᴴ * k = 1) :
    hs (k * X * kᴴ) = hs X := by
  unfold hs
  congr 1
  have : ((∑ a, ∑ b, ‖(k * X * kᴴ) a b‖ ^ 2 : ℝ) : ℂ) = ((∑ a, ∑ b, ‖X a b‖ ^ 2 : ℝ) : ℂ) := by
    rw [hs_sq_trace_b, hs_sq_trace_b]
    have e : (k * X * kᴴ)ᴴ * (k * X * kᴴ) = k * (Xᴴ * X) * kᴴ := by
      simp only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc kᴴ k, hk, Matrix.one_mul]
    rw [e, trace_mul_cycle, hk, Matrix.one_mul]
  exact_mod_cast this

lemma hs_neg_b {N : ℕ} (X : Matrix (Fin N) (Fin N) ℂ) : hs (-X) = hs X := by
  simp [hs]

lemma eigenvalue_le_hs_b {N : ℕ} (X : Matrix (Fin N) (Fin N) ℂ) (hX : X.IsHermitian) (i : Fin N) :
    hX.eigenvalues i ≤ hs X := by
  unfold hs
  rw [← Formalism.NuclearRankWeightBounds.P.sum_sq_eigenvalues X hX]
  apply Real.le_sqrt_of_sq_le
  exact Finset.single_le_sum (f := fun j => hX.eigenvalues j ^ 2) (fun j _ => sq_nonneg _) (mem_univ i)

lemma exp_sq_psd_b {N : ℕ} (X : Matrix (Fin N) (Fin N) ℂ) (hX : X.IsHermitian) :
    ((Real.exp (hs X) ^ 2 : ℝ) • (1 : Matrix (Fin N) (Fin N) ℂ)
        - NormedSpace.exp X * NormedSpace.exp X).PosSemidef := by
  set U : Matrix (Fin N) (Fin N) ℂ := (hX.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ) with hUdef
  set D : Fin N → ℂ := RCLike.ofReal ∘ hX.eigenvalues with hDdef
  have hUU : U * Uᴴ = 1 := by
    simpa [U, star_eq_conjTranspose] using Unitary.coe_mul_star_self hX.eigenvectorUnitary
  have hUU' : Uᴴ * U = 1 := by
    simpa [U, star_eq_conjTranspose] using Unitary.coe_star_mul_self hX.eigenvectorUnitary
  have hspec : X = U * diagonal D * Uᴴ := by
    conv_lhs => rw [hX.spectral_theorem]
    simp [U, D, Unitary.conjStarAlgAut_apply, star_eq_conjTranspose]
  have hinv : U⁻¹ = Uᴴ := Matrix.inv_eq_right_inv hUU
  have hunit : IsUnit U := ⟨⟨U, Uᴴ, hUU, hUU'⟩, rfl⟩
  have hexp : NormedSpace.exp X = U * diagonal (fun i => ((Real.exp (hX.eigenvalues i) : ℝ) : ℂ)) * Uᴴ := by
    conv_lhs => rw [hspec, ← hinv, Matrix.exp_conj U _ hunit, Matrix.exp_diagonal]
    have hD : NormedSpace.exp D = fun i => ((Real.exp (hX.eigenvalues i) : ℝ) : ℂ) := by
      funext i
      rw [Pi.coe_exp, ← Complex.exp_eq_exp_ℂ, Complex.ofReal_exp]
      rfl
    rw [hD, hinv]
  have e : ((Real.exp (hs X) ^ 2 : ℝ) • (1 : Matrix (Fin N) (Fin N) ℂ)
        - NormedSpace.exp X * NormedSpace.exp X)
      = U * diagonal (fun i => ((Real.exp (hs X) ^ 2 - Real.exp (hX.eigenvalues i) ^ 2 : ℝ) : ℂ)) * Uᴴ := by
    rw [hexp]
    have e1 : U * diagonal (fun i => ((Real.exp (hX.eigenvalues i) : ℝ) : ℂ)) * Uᴴ *
        (U * diagonal (fun i => ((Real.exp (hX.eigenvalues i) : ℝ) : ℂ)) * Uᴴ)
        = U * diagonal (fun i => ((Real.exp (hX.eigenvalues i) ^ 2 : ℝ) : ℂ)) * Uᴴ := by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc Uᴴ U, hUU', Matrix.one_mul, ← Matrix.mul_assoc (diagonal _) (diagonal _),
        diagonal_mul_diagonal]
      congr 3
      ext i
      push_cast; ring
    have e2 : ((Real.exp (hs X) ^ 2 : ℝ) • (1 : Matrix (Fin N) (Fin N) ℂ))
        = U * diagonal (fun _ => ((Real.exp (hs X) ^ 2 : ℝ) : ℂ)) * Uᴴ := by
      have : diagonal (fun _ : Fin N => ((Real.exp (hs X) ^ 2 : ℝ) : ℂ))
          = ((Real.exp (hs X) ^ 2 : ℝ) : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) := by
        ext a b; simp [diagonal_apply, one_apply]
      rw [this, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hUU]
      ext a b; simp
    rw [e1, e2, ← Matrix.sub_mul, ← Matrix.mul_sub, diagonal_sub]
    congr 3
    ext i
    push_cast; ring
  rw [e]
  apply Matrix.PosSemidef.mul_mul_conjTranspose_same
  apply Matrix.PosSemidef.diagonal
  intro i
  simp only [Pi.zero_apply]
  rw [Complex.zero_le_real, sub_nonneg]
  gcongr
  exact eigenvalue_le_hs_b X hX i

theorem polar_decomposition_inverse : PolarInv := by
  intro N k X hk hX
  have hk1 : k * kᴴ = 1 := by
    simpa [star_eq_conjTranspose] using (Matrix.mem_unitaryGroup_iff.1 hk)
  have hk2 : kᴴ * k = 1 := by
    simpa [star_eq_conjTranspose] using (Matrix.mem_unitaryGroup_iff'.1 hk)
  have hinv : k⁻¹ = kᴴ := Matrix.inv_eq_right_inv hk1
  have hunit : IsUnit k := ⟨⟨k, kᴴ, hk1, hk2⟩, rfl⟩
  have hexp : NormedSpace.exp (-(k * X * kᴴ)) = k * (NormedSpace.exp X)⁻¹ * kᴴ := by
    have : -(k * X * kᴴ) = k * (-X) * k⁻¹ := by rw [hinv]; simp
    rw [this, Matrix.exp_conj k _ hunit, Matrix.exp_neg, hinv]
  have hdet : IsUnit (NormedSpace.exp X).det := (Matrix.isUnit_iff_isUnit_det _).1 (Matrix.isUnit_exp X)
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply Matrix.inv_eq_right_inv
    rw [hexp]
    calc k * NormedSpace.exp X * (kᴴ * (k * (NormedSpace.exp X)⁻¹ * kᴴ))
        = k * (NormedSpace.exp X * ((kᴴ * k) * (NormedSpace.exp X)⁻¹)) * kᴴ := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hk2, Matrix.one_mul, Matrix.mul_nonsing_inv _ hdet, Matrix.mul_one, hk1]
  · exact (Matrix.isHermitian_mul_mul_conjTranspose k hX).neg
  · rw [hs_neg_b, hs_unitary_conj_b k X hk2]
  · have e : (k * NormedSpace.exp X)ᴴ * (k * NormedSpace.exp X) = NormedSpace.exp X * NormedSpace.exp X := by
      rw [conjTranspose_mul, (hX.exp).eq]
      calc NormedSpace.exp X * kᴴ * (k * NormedSpace.exp X)
          = NormedSpace.exp X * ((kᴴ * k) * NormedSpace.exp X) := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [hk2, Matrix.one_mul]
    rw [e]
    exact exp_sq_psd_b X hX

open Classical in

lemma layer_sum_b (ι Γ : Type) [Fintype ι] (S : Finset Γ) (d : Γ → ι → ℝ) (A B K : ℝ)
    (F : ℝ → ℝ) (u w : ℕ → ℝ) (hA : 0 ≤ A) (hu : ∀ i, 0 ≤ u i) (hw : ∀ i, 0 ≤ w i)
    (hF : ∀ t, 0 ≤ F t) (hlev : ∀ t, 0 ≤ t → ∃ i, t ≤ u i ∧ F t ≤ w i)
    (hd : ∀ γ ∈ S, ∀ v, 0 ≤ d γ v)
    (hcount : ∀ r : ι → ℝ, (∀ v, 0 ≤ r v) →
      ((S.filter fun γ => ∀ v, d γ v ≤ r v).card : ℝ) ≤ A * Real.exp (B * ∑ v, r v))
    (hK : ∀ M, ∑ i ∈ range M, w i * Real.exp (B * u i) ≤ K) :
    ∑ γ ∈ S, ∏ v, F (d γ v) ≤ A * K ^ Fintype.card ι := by
  have hlev' : ∀ t : ℝ, ∃ i, 0 ≤ t → (t ≤ u i ∧ F t ≤ w i) := by
    intro t
    by_cases ht : 0 ≤ t
    · obtain ⟨i, hi⟩ := hlev t ht
      exact ⟨i, fun _ => hi⟩
    · exact ⟨0, fun h => absurd h ht⟩
  choose lev hl using hlev'
  set L : Γ → ι → ℕ := fun γ v => lev (d γ v) with hL
  set M : ℕ := (S.sup fun γ => univ.sup (L γ)) + 1 with hM
  set T : Finset (ι → ℕ) := Fintype.piFinset fun _ => range M with hT
  have hmaps : ∀ γ ∈ S, L γ ∈ T := by
    intro γ hγ
    rw [hT, Fintype.mem_piFinset]
    intro v
    rw [mem_range, hM, Nat.lt_succ_iff]
    exact le_trans (Finset.le_sup (f := L γ) (mem_univ v))
      (Finset.le_sup (f := fun γ => univ.sup (L γ)) hγ)
  have h1 : ∑ γ ∈ S, ∏ v, F (d γ v) ≤ ∑ γ ∈ S, ∏ v, w (L γ v) := by
    apply Finset.sum_le_sum
    intro γ hγ
    apply Finset.prod_le_prod
    · intro v _; exact hF _
    · intro v _; exact (hl _ (hd γ hγ v)).2
  have h2 : ∑ γ ∈ S, ∏ v, w (L γ v) = ∑ I ∈ T, ∑ γ ∈ S with L γ = I, ∏ v, w (L γ v) :=
    (Finset.sum_fiberwise_of_maps_to hmaps _).symm
  have h3 : ∀ I ∈ T, ∑ γ ∈ S with L γ = I, ∏ v, w (L γ v) ≤
      A * ∏ v, (w (I v) * Real.exp (B * u (I v))) := by
    intro I _
    have e1 : ∑ γ ∈ S with L γ = I, ∏ v, w (L γ v) = ((S.filter fun γ => L γ = I).card : ℝ) * ∏ v, w (I v) := by
      rw [← nsmul_eq_mul, ← Finset.sum_const]
      apply Finset.sum_congr rfl
      intro γ hγ
      rw [(Finset.mem_filter.1 hγ).2]
    rw [e1]
    have hsub : (S.filter fun γ => L γ = I) ⊆ (S.filter fun γ => ∀ v, d γ v ≤ u (I v)) := by
      intro γ hγ
      rw [Finset.mem_filter] at hγ ⊢
      refine ⟨hγ.1, fun v => ?_⟩
      rw [← hγ.2]
      exact (hl _ (hd γ hγ.1 v)).1
    have hc : ((S.filter fun γ => L γ = I).card : ℝ) ≤ A * Real.exp (B * ∑ v, u (I v)) :=
      le_trans (by exact_mod_cast Finset.card_le_card hsub) (hcount _ fun v => hu _)
    have hp : 0 ≤ ∏ v, w (I v) := Finset.prod_nonneg fun v _ => hw _
    calc _ ≤ A * Real.exp (B * ∑ v, u (I v)) * ∏ v, w (I v) := mul_le_mul_of_nonneg_right hc hp
      _ = _ := by
        rw [Finset.prod_mul_distrib, Finset.mul_sum, Real.exp_sum]; ring
  have h4 : ∑ I ∈ T, A * ∏ v, (w (I v) * Real.exp (B * u (I v))) =
      A * (∑ i ∈ range M, w i * Real.exp (B * u i)) ^ Fintype.card ι := by
    have := Finset.prod_univ_sum (fun _ : ι => range M) (fun _ i => w i * Real.exp (B * u i))
    rw [← Finset.mul_sum, hT, ← this, Finset.prod_const, Finset.card_univ]
  have h5 : 0 ≤ ∑ i ∈ range M, w i * Real.exp (B * u i) :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hw i) (Real.exp_pos _).le
  calc _ ≤ _ := h1
    _ = _ := h2
    _ ≤ _ := Finset.sum_le_sum h3
    _ = _ := h4
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ hA
      exact pow_le_pow_left₀ h5 (hK M) _

lemma geom_partial_le_b (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 1) (M : ℕ) :
    ∑ i ∈ range M, x ^ i ≤ 1 / (1 - x) := by
  rw [one_div, ← tsum_geometric_of_lt_one hx0 hx1]
  exact (summable_geometric_of_lt_one hx0 hx1).sum_le_tsum _ (fun i _ => pow_nonneg hx0 i)

theorem all_sum_rate : AllSumRate := by
  intro ι Γ _ _ S d A B h q hq hA hB hh hd hcount
  have hq' : (1:ℝ) ≤ q := by exact_mod_cast hq
  have hs1 : 1 ≤ Real.sqrt (2 * (q:ℝ)) := by
    rw [Real.one_le_sqrt]; linarith
  have hs0 : 0 < Real.sqrt (2 * (q:ℝ)) := by linarith
  have hh0 : 0 ≤ h := le_trans (by positivity) hh
  have hx1 : Real.exp (-B) < 1 := by rw [Real.exp_lt_one_iff]; linarith
  refine layer_sum_b ι Γ S d A B _ (fun t => Real.exp (-(decExp h q t))) (fun i => (i:ℝ) + 1)
    (fun i => Real.exp (-(2 * B * i))) hA (fun i => by positivity) (fun i => (Real.exp_pos _).le)
    (fun t => (Real.exp_pos _).le) ?_ hd hcount ?_
  · intro t ht
    refine ⟨⌈t⌉₊ - 1, ?_, ?_⟩
    · have h1 := Nat.le_ceil t
      have h2 : (⌈t⌉₊ : ℝ) ≤ ((⌈t⌉₊ - 1 : ℕ) : ℝ) + 1 := by
        have : ⌈t⌉₊ ≤ (⌈t⌉₊ - 1) + 1 := by omega
        exact_mod_cast this
      linarith
    · rw [Real.exp_le_exp, neg_le_neg_iff]
      unfold decExp
      rcases Nat.eq_zero_or_pos (⌈t⌉₊ - 1) with h0 | h0
      · rw [h0]
        simp only [Nat.cast_zero, mul_zero]
        have : 0 ≤ min (t ^ 2) (t / Real.sqrt (2 * (q:ℝ))) := le_min (by positivity) (by positivity)
        positivity
      · have hlt : ((⌈t⌉₊ - 1 : ℕ) : ℝ) < t := by
          rw [← Nat.lt_ceil]; omega
        have hi1 : (1:ℝ) ≤ ((⌈t⌉₊ - 1 : ℕ) : ℝ) := by exact_mod_cast h0
        set i : ℝ := ((⌈t⌉₊ - 1 : ℕ) : ℝ) with hi
        have ht1 : 1 ≤ t := by linarith
        have hmin : i / Real.sqrt (2 * (q:ℝ)) ≤ min (t ^ 2) (t / Real.sqrt (2 * (q:ℝ))) := by
          apply le_min
          · calc i / Real.sqrt (2 * (q:ℝ)) ≤ i := div_le_self (by linarith) hs1
              _ ≤ t ^ 2 := by nlinarith
          · gcongr
        calc 2 * B * i = (16 * B * Real.sqrt (2 * (q:ℝ))) / 8 * (i / Real.sqrt (2 * (q:ℝ))) := by
              field_simp; ring
          _ ≤ h / 8 * (i / Real.sqrt (2 * (q:ℝ))) := by gcongr
          _ ≤ _ := by gcongr
  · intro M
    have e : ∀ i : ℕ, Real.exp (-(2 * B * i)) * Real.exp (B * ((i:ℝ) + 1)) = Real.exp B * Real.exp (-B) ^ i := by
      intro i
      rw [← Real.exp_add, ← Real.exp_nat_mul, ← Real.exp_add]; congr 1; ring
    simp_rw [e]
    rw [← Finset.mul_sum, div_eq_mul_one_div]
    exact mul_le_mul_of_nonneg_left (geom_partial_le_b _ (Real.exp_pos _).le hx1 M) (Real.exp_pos _).le

lemma sq_sum_fin_b {a : ℕ} (j : Fin a → ℕ) :
    (∑ x, j x) ^ 2 = ∑ x, j x ^ 2 + 2 * ∑ x, ∑ y ∈ univ.filter (fun y => x < y), j x * j y := by
  simp only [Finset.sum_filter]
  have h1 : ∀ x y : Fin a, j x * j y = (if x < y then j x * j y else 0)
      + (if y < x then j x * j y else 0) + (if x = y then j x ^ 2 else 0) := by
    intro x y
    rcases lt_trichotomy x y with h | h | h
    · simp [h, h.ne, h.not_gt]
    · subst h; simp [sq]
    · simp [h, h.ne', h.not_gt]
  have h2 : ∑ x, ∑ y, (if y < x then j x * j y else 0) = ∑ x, ∑ y, (if x < y then j x * j y else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    rw [mul_comm]
  calc (∑ x, j x) ^ 2 = ∑ x, ∑ y, j x * j y := by rw [sq, Finset.sum_mul_sum]
    _ = ∑ x, ∑ y, ((if x < y then j x * j y else 0)
      + (if y < x then j x * j y else 0) + (if x = y then j x ^ 2 else 0)) :=
        Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => h1 x y
    _ = _ := by
      simp only [Finset.sum_add_distrib, Finset.sum_ite_eq, mem_univ, if_true]
      rw [h2]; ring

lemma dimN_eq_b {a : ℕ} (j : Fin a → ℕ) (n0 : ℕ) :
    dimN j n0 = 4 * (∑ x, ∑ y ∈ univ.filter (fun y => x < y), j x * j y) + ∑ x, j x ^ 2
      + 2 * (∑ x, j x) * n0 := by
  unfold dimN
  have h1 : ∑ x, ∑ y ∈ univ.filter (fun y => x < y), 2 * j x * j y
      = 2 * ∑ x, ∑ y ∈ univ.filter (fun y => x < y), j x * j y := by
    simp only [Finset.mul_sum, mul_assoc]
  have h2 : ∑ x, 2 * j x * n0 = 2 * (∑ x, j x) * n0 := by
    simp only [Finset.mul_sum, Finset.sum_mul]
  rw [h1, h2]; ring

lemma vsph_pos_b (i : ℕ) : 0 < Vsph i := by
  unfold Vsph
  exact Finset.prod_pos fun l _ => by positivity

theorem kappaAssembly_of (hV : VRatio) : KappaAssembly := by
  obtain ⟨Cv, hCv, hV⟩ := hV
  intro C hC
  have hC7 : 1 ≤ C ^ 7 := one_le_pow₀ hC
  refine ⟨C ^ 7 * Cv, by nlinarith, ?_⟩
  intro a p q n0 f j v res cIw volN volR volGL hj ha hJq hqp hn hf hv hres hN0 hN hGL hR0 hR hI0 hI
  have hVr := hV p q a j hJq hqp
  have hsq := sq_sum_fin_b j
  have hdim := dimN_eq_b j n0
  have haJ : a ≤ ∑ x, j x := by
    calc a = ∑ _x : Fin a, 1 := by simp
      _ ≤ _ := Finset.sum_le_sum fun x _ => hj x
  set J := ∑ x, j x with hJ
  set dN := dimN j n0 with hdN
  set Q := ∑ x, j x ^ 2 with hQ
  set P := ∑ x, ∑ y ∈ univ.filter (fun y => x < y), j x * j y with hP
  set JJ : ℝ := (J : ℝ) ^ ((J : ℝ) ^ 2 / 2) with hJJ
  set R : ℝ := Vsph p * Vsph q / (Vsph (p - J) * Vsph (q - J) * ∏ x, Vsph (j x)) with hRdef
  have hC0 : 0 < C := by linarith
  have hCv0 : 0 < Cv := by linarith
  have hv0 : 0 < v := by linarith
  have hJJ0 : 0 ≤ JJ := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hR0' : 0 ≤ R := by
    have := vsph_pos_b p; have := vsph_pos_b q; have := vsph_pos_b (p - J); have := vsph_pos_b (q - J)
    have : 0 < ∏ x, Vsph (j x) := Finset.prod_pos fun x _ => vsph_pos_b _
    positivity
  have hJ1 : 1 ≤ J := le_trans ha haJ

  have hexp : dN * f + dN * f + Q * f + a * f + (p + q) * f ≤ 7 * (J * (p + q) * f) := by
    have hn1 : J ≤ p + q := by omega
    have h1 : dN ≤ 2 * (J * (p + q)) := by
      rw [hdim, hn]; nlinarith
    have h2 : Q ≤ J * (p + q) := by
      calc Q ≤ J ^ 2 := by omega
        _ = J * J := sq J
        _ ≤ _ := Nat.mul_le_mul_left _ hn1
    have h3 : p + q ≤ J * (p + q) := Nat.le_mul_of_pos_left _ hJ1
    have h4 : a ≤ J * (p + q) := by
      calc a ≤ J := haJ
        _ ≤ p + q := hn1
        _ ≤ _ := h3
    calc dN * f + dN * f + Q * f + a * f + (p + q) * f = (dN + dN + Q + a + (p + q)) * f := by ring
      _ ≤ (7 * (J * (p + q))) * f := Nat.mul_le_mul_right _ (by omega)
      _ = _ := by ring

  have hid : ((p + q : ℕ) : ℝ) ^ 2 - (n0 : ℝ) ^ 2 = 2 * (Q : ℝ) + 2 * (dN : ℝ) := by
    have : (p + q) ^ 2 = n0 ^ 2 + 2 * Q + 2 * dN := by
      rw [hdim, hn]; nlinarith
    have h' : ((p + q : ℕ) : ℝ) ^ 2 = (n0 : ℝ) ^ 2 + 2 * Q + 2 * dN := by exact_mod_cast this
    linarith
  set W : ℝ := (Cv / (p : ℝ)) ^ (J * (p - J)) * JJ with hW
  set W' : ℝ := (C ^ 7 * Cv / (p : ℝ)) ^ (J * (p - J)) * JJ with hW'
  have hW0 : 0 ≤ W := by positivity
  have hWW : W ≤ W' := by
    rw [hW, hW']
    gcongr
    nlinarith
  have sA : cIw ≤ C ^ (dN * f) * (Cv ^ (J * (p + q) * f) * W ^ f) := by
    refine hI.trans ?_
    calc (C ^ dN * R) ^ f ≤ (C ^ dN * (Cv ^ (J * (p + q)) * W)) ^ f := by
          gcongr
          rw [hW, ← mul_assoc]; exact hVr
      _ = _ := by rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul]
  have sB : volN ≤ C ^ (dN * f) * v ^ ((f : ℝ) * dN / 2) := by
    refine hN.trans ?_
    rw [Real.mul_rpow hC0.le hv0.le]
    gcongr
    rw [← Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_le hC
    push_cast
    have : (0:ℝ) ≤ (f:ℝ) * dN := by positivity
    linarith
  have sC : ∏ x, volGL x ≤ C ^ (Q * f) * v ^ ((Q : ℝ) * f) * res ^ a * C ^ (a * f) := by
    calc ∏ x, volGL x ≤ ∏ x, ((C * v) ^ (j x ^ 2 * f) * res * C ^ f) :=
          Finset.prod_le_prod (fun x _ => (hGL x).1) (fun x _ => (hGL x).2)
      _ = _ := by
          rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
            Finset.prod_const, Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← Finset.sum_mul,
            mul_pow, ← pow_mul, mul_comm f a]
          congr 3
          rw [← Real.rpow_natCast, Nat.cast_mul]
  have hG0 : 0 ≤ ∏ x, volGL x := Finset.prod_nonneg fun x _ => (hGL x).1
  have hvv : v ^ ((f : ℝ) * dN / 2) * v ^ ((Q : ℝ) * f)
      * v ^ (-(((p + q : ℕ) : ℝ) ^ 2 - (n0 : ℝ) ^ 2) * f / 2) = v ^ (-((f : ℝ) * dN / 2)) := by
    rw [← Real.rpow_add hv0, ← Real.rpow_add hv0, hid]
    congr 1; ring
  have hvp : 0 < v ^ (-((f : ℝ) * dN / 2)) := Real.rpow_pos_of_pos hv0 _
  have key : ∀ c1 k w v1 c3 v2 r c4 v3 c5 : ℝ, (c1 * (k * w)) * (c1 * v1) * (c3 * v2 * r * c4) * (v3 * c5)
      = (v1 * v2 * v3) * (c1 * c1 * c3 * c4 * c5 * k) * r * w := by intros; ring
  have key2 : ∀ x c c' k r w w' : ℝ, 0 ≤ x → 0 ≤ c → 0 ≤ k → 0 ≤ r → 0 ≤ w → c ≤ c' → w ≤ w' →
      x * (c * k) * r * w ≤ x * (c' * k) * r * w' := by
    intro x c c' k r w w' _ hc _ _ _ hcc _
    have : 0 ≤ c' := hc.trans hcc
    gcongr
  calc cIw * volN * (∏ x, volGL x) * volR
      ≤ (C ^ (dN * f) * (Cv ^ (J * (p + q) * f) * W ^ f)) * (C ^ (dN * f) * v ^ ((f : ℝ) * dN / 2))
        * (C ^ (Q * f) * v ^ ((Q : ℝ) * f) * res ^ a * C ^ (a * f))
        * (v ^ (-(((p + q : ℕ) : ℝ) ^ 2 - (n0 : ℝ) ^ 2) * f / 2) * C ^ ((p + q) * f)) := by
        gcongr
    _ = (v ^ ((f : ℝ) * dN / 2) * v ^ ((Q : ℝ) * f)
          * v ^ (-(((p + q : ℕ) : ℝ) ^ 2 - (n0 : ℝ) ^ 2) * f / 2))
        * (C ^ (dN * f + dN * f + Q * f + a * f + (p + q) * f) * Cv ^ (J * (p + q) * f))
        * res ^ a * W ^ f := by
        rw [pow_add, pow_add, pow_add, pow_add]
        exact key _ _ _ _ _ _ _ _ _ _
    _ ≤ v ^ (-((f : ℝ) * dN / 2)) * (C ^ (7 * (J * (p + q) * f)) * Cv ^ (J * (p + q) * f))
        * res ^ a * W' ^ f := by
        rw [hvv]
        exact key2 _ _ _ _ _ _ _ hvp.le (by positivity) (by positivity) (by positivity)
          (pow_nonneg hW0 f) (pow_le_pow_right₀ hC hexp) (pow_le_pow_left₀ hW0 hWW f)
    _ = _ := by
        rw [pow_mul C 7, ← mul_pow]

open scoped ENNReal

theorem room_for_iterations : StepsRoom := by
  intro n q f P b hq
  constructor
  · have : n^2*f ≤ P0 n q f := by
      unfold P0
      calc n^2*f = 1 * (n^2*f) := by ring
        _ ≤ (8*q) * (n^2*f) := Nat.mul_le_mul_right _ (by omega)
        _ = 8*q*n^2*f := by ring
    omega
  · intro hP
    unfold b1
    have h1 : (P:ℝ) ≤ 2 * (P0 n q f : ℝ) := by exact_mod_cast hP
    have hn : (0:ℝ) ≤ n := Nat.cast_nonneg _
    nlinarith [mul_le_mul_of_nonneg_right h1 hn]

theorem layer_count : LayerCount := by
  intro ι _ _ N de la laM hde hla hlaM
  have hc : (0:ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have h1 : (∏ _v : ι, 3 * de) ^ ((1 : ℝ) / Fintype.card ι) = 3*de := by
    rw [Finset.prod_const, Finset.card_univ, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    rw [mul_one_div_cancel hc.ne', Real.rpow_one]
  rw [h1]
  have hM : 0 < laM := by linarith
  apply pow_le_pow_left₀ (by positivity)
  have : 2*(3*de)/laM ≤ 12*de/la := by
    rw [div_le_div_iff₀ hM hla]; nlinarith
  linarith

theorem threshold_count : ThreshCount := by
  intro n q h hh
  have e : Real.sqrt (2*(q:ℝ)) = Real.sqrt 2 * Real.sqrt q := Real.sqrt_mul (by norm_num) _
  rw [e]
  have h2 : Real.sqrt 2 ≤ 23/16 := by rw [Real.sqrt_le_iff]; norm_num
  have hq := Real.sqrt_nonneg (q:ℝ)
  have hn : (0:ℝ) ≤ (n:ℝ)^2 := by positivity
  have := mul_le_mul_of_nonneg_right h2 (mul_nonneg hn hq)
  nlinarith

theorem log_volume_bound : LogVolumeBound := by
  intro a q f j C₁ Y hC hY hq hj
  have hY0 : 0 < Y := by linarith
  have hq' : (1:ℝ) ≤ q := by exact_mod_cast hq
  have hCq : 1 ≤ C₁*q := by nlinarith
  have hpos : 0 < Y^(-(C₁*q)) := Real.rpow_pos_of_pos hY0 _
  have hle : Y^(-(C₁*q)) ≤ 1/2 := by
    rw [Real.rpow_neg hY0.le, one_div]
    apply inv_anti₀ (by norm_num)
    calc (2:ℝ) ≤ Y := hY
      _ = Y^(1:ℝ) := (Real.rpow_one _).symm
      _ ≤ Y^(C₁*q) := Real.rpow_le_rpow_of_exponent_le (by linarith) hCq
  refine ⟨hpos, hle, ?_⟩
  have hlog : Real.log (1/(2*Y^(-(C₁*q)))) = C₁*q*Real.log Y - Real.log 2 := by
    rw [one_div, Real.log_inv, Real.log_mul (by norm_num) hpos.ne', Real.log_rpow hY0]; ring
  have hl0 : 0 ≤ Real.log (1/(2*Y^(-(C₁*q)))) := by
    apply Real.log_nonneg; rw [le_div_iff₀ (by positivity)]; linarith
  have hl1 : Real.log (1/(2*Y^(-(C₁*q)))) ≤ C₁*q*Real.log Y := by
    rw [hlog]; linarith [Real.log_pos (by norm_num : (1:ℝ)<2)]
  calc ∏ x, (2*(f:ℝ)*j x * Real.log (1/(2*Y^(-(C₁*q))))) ≤ ∏ _x : Fin a, (2*C₁*f*(q:ℝ)^2*Real.log Y) := by
        apply Finset.prod_le_prod
        · intro x _; positivity
        · intro x _
          have : (j x:ℝ) ≤ q := by exact_mod_cast hj x
          calc 2*(f:ℝ)*j x * Real.log (1/(2*Y^(-(C₁*q)))) ≤ 2*(f:ℝ)*q*(C₁*q*Real.log Y) := by gcongr
            _ = _ := by ring
    _ = _ := by simp

section Dedekind

open Ideal UniqueFactorizationMonoid

variable {K : Type} [Field K] [NumberField K]

noncomputable def normWeight_b (K : Type) [Field K] [NumberField K] (i : ℕ) : Ideal (𝓞 K) →* ℝ where
  toFun I := ((absNorm I : ℝ)⁻¹) ^ i
  map_one' := by simp
  map_mul' I J := by
    rw [map_mul, Nat.cast_mul, mul_inv, mul_pow]

end Dedekind

end Formalism.HermitianLatticeCounting.P
