import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsThetaMeanSquareNorm
import Development.AutomorphicSpectrum.Statements.GeometryStatements.ZhangDimensionPushDownGrassmannianHeightBounds
import GroundTheory.HeightsAndTheta.Heights.KernelsLattice
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.StatementsBundles
import GroundTheory.PAdicHodge.SlopeCauchyBinet

open NumberField

namespace GlobalTheory.CompanionTheory.Ar.FlagSlope

open Matrix InnerProductSpace

theorem val_det_le_one {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation K Γ) : ∀ (m : ℕ) (B : Matrix (Fin m) (Fin m) K),
    (∀ (i : Fin m) (c : Fin m → K), (∀ j, v (c j) ≤ 1) →
      (∀ k < i, ∑ j, c j * B k j = 0) → v (∑ j, c j * B i j) ≤ 1) →
    v B.det ≤ 1 := by
  intro m
  induction m with
  | zero => intro B _; simp
  | succ m ih =>
    intro B hB
    obtain ⟨j0, -, hj0⟩ := Finset.exists_max_image Finset.univ (fun j => v (B 0 j))
      Finset.univ_nonempty
    by_cases ht : B 0 j0 = 0
    · have hz : ∀ j, B 0 j = 0 := fun j => by
        have := hj0 j (Finset.mem_univ _)
        simpa [ht] using this
      rw [Matrix.det_eq_zero_of_row_eq_zero 0 hz]; simp
    let a : Fin (m + 1) → K := fun j => if j = j0 then 0 else B 0 j / B 0 j0
    have hvt : v (B 0 j0) ≠ 0 := (Valuation.ne_zero_iff v).mpr ht
    have ha_le : ∀ j, v (a j) ≤ 1 := by
      intro j
      by_cases hj : j = j0
      · simp [a, hj]
      · simp only [a, hj, if_false, map_div₀]
        exact div_le_one_of_le₀ (hj0 j (Finset.mem_univ _)) zero_le'
    let B' : Matrix (Fin (m + 1)) (Fin (m + 1)) K := fun i j => B i j - a j * B i j0
    have hB'0 : ∀ i, B' i j0 = B i j0 := fun i => by simp [B', a]
    have hdet : B.det = B'.det := by
      rw [← Matrix.det_transpose B, ← Matrix.det_transpose B']
      exact Matrix.det_eq_of_forall_row_eq_smul_add_const a j0 (by simp [a])
        (fun i j => by simp only [Matrix.transpose_apply]; rw [hB'0]; simp [B'])
    have hrow : ∀ l, B' 0 (j0.succAbove l) = 0 := by
      intro l
      have hne : j0.succAbove l ≠ j0 := Fin.succAbove_ne j0 l
      simp only [B', a, hne, if_false]
      field_simp
      ring
    have hrow' : ∀ j, j ≠ j0 → B' 0 j = 0 := by
      intro j hj
      obtain ⟨l, rfl⟩ := Fin.exists_succAbove_eq hj
      exact hrow l
    let D : Matrix (Fin m) (Fin m) K := B'.submatrix Fin.succ j0.succAbove
    have hexp : B.det = (-1) ^ (j0 : ℕ) * B 0 j0 * D.det := by
      rw [hdet, Matrix.det_succ_row_zero, Finset.sum_eq_single j0]
      · rw [hB'0]
      · intro j _ hj
        rw [hrow' j hj]; simp
      · simp
    have hvt1 : v (B 0 j0) ≤ 1 := by
      have := hB 0 (Pi.single j0 1) (by
        intro j
        by_cases hj : j = j0
        · subst hj; simp
        · simp [Pi.single_eq_of_ne hj]) (by intro k hk; exact absurd hk (Fin.not_lt_zero k))
      simpa [Pi.single_apply] using this
    have hD : v D.det ≤ 1 := by
      apply ih D
      intro i c hc hk
      let C : Fin (m + 1) → K :=
        Fin.insertNth (α := fun _ => K) j0 (-(∑ l, c l * a (j0.succAbove l))) c
      have hCsame : C j0 = -(∑ l, c l * a (j0.succAbove l)) := by simp [C]
      have hCabove : ∀ l, C (j0.succAbove l) = c l := fun l => by simp [C]
      have key : ∀ k', ∑ j, C j * B k' j = ∑ l, c l * B' k' (j0.succAbove l) := by
        intro k'
        rw [Fin.sum_univ_succAbove _ j0, hCsame]
        simp only [hCabove, B', mul_sub, Finset.sum_sub_distrib]
        rw [neg_mul, Finset.sum_mul]
        simp only [mul_assoc]
        ring
      have hC : ∀ j, v (C j) ≤ 1 := by
        intro j
        rcases Fin.eq_self_or_eq_succAbove j0 j with rfl | ⟨l, rfl⟩
        · rw [hCsame, Valuation.map_neg]
          refine Valuation.map_sum_le v (fun l _ => ?_)
          rw [map_mul]
          exact mul_le_one' (hc l) (ha_le _)
        · rw [hCabove]; exact hc l
      have := hB i.succ C hC (by
        intro k hk'
        rw [key]
        rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨k', rfl⟩
        · simp [hrow]
        · exact hk k' (Fin.succ_lt_succ_iff.mp hk'))
      rw [key] at this
      exact this
    rw [hexp, map_mul, map_mul, map_pow, Valuation.map_neg, map_one, one_pow, one_mul]
    exact mul_le_one' hvt1 hD

theorem one_le_prod_norm {K : Type*} [Field K] [NumberField K] (x : K) (hx : IsIntegral ℤ x)
    (h0 : x ≠ 0) : 1 ≤ ∏ σ : K →+* ℂ, ‖σ x‖ := by
  let y : 𝓞 K := ⟨x, hx⟩
  have hy : y ≠ 0 := fun h => h0 (congrArg (fun z : 𝓞 K => (z : K)) h)
  have hn : Algebra.norm ℤ y ≠ 0 := Algebra.norm_ne_zero_iff.mpr hy
  have h1 : algebraMap ℚ ℂ (Algebra.norm ℚ x) = ∏ σ : K →ₐ[ℚ] ℂ, σ x :=
    Algebra.norm_eq_prod_embeddings ℚ ℂ x
  have h2 : ∏ σ : K →+* ℂ, ‖σ x‖ = ∏ σ : K →ₐ[ℚ] ℂ, ‖σ x‖ :=
    Fintype.prod_equiv (RingHom.equivRatAlgHom K ℂ) _ _ (fun σ => by simp [RingHom.equivRatAlgHom])
  have h3 : ((Algebra.norm ℤ y : ℤ) : ℚ) = Algebra.norm ℚ x := Algebra.coe_norm_int y
  rw [h2, ← norm_prod, ← h1, ← h3]
  have : (1 : ℝ) ≤ |((Algebra.norm ℤ y : ℤ) : ℝ)| := by
    exact_mod_cast Int.one_le_abs hn
  simpa using this

theorem norm_det_le {m : ℕ} (C : Matrix (Fin m) (Fin m) ℂ) (a : Fin m → ℝ) (ha : ∀ i, 0 < a i)
    (h : ∀ (i : Fin m) (c : Fin m → ℂ), (∀ k < i, ∑ j, c j * C k j = 0) →
      ‖∑ j, c j * C i j‖ ≤ a i * √(∑ j, ‖c j‖ ^ 2)) :
    ‖C.det‖ ≤ ∏ i, a i := by
  classical
  let f : Fin m → EuclideanSpace ℂ (Fin m) := fun i => WithLp.toLp 2 (C i)
  let w : Fin m → EuclideanSpace ℂ (Fin m) := gramSchmidt ℂ f
  have hinner : ∀ x y : EuclideanSpace ℂ (Fin m),
      inner ℂ x y = ∑ j, (starRingEnd ℂ) (x j) * y j := fun x y => by
    simp [PiLp.inner_apply, mul_comm]
  have hfj : ∀ i j, f i j = C i j := fun i j => rfl
  have hii : ∀ i, inner ℂ (w i) (f i) = ((‖w i‖ : ℂ)) ^ 2 := by
    intro i
    have hdef := gramSchmidt_def'' ℂ f i
    have h1 : inner ℂ (w i) (f i) = inner ℂ (w i) (w i) := by
      rw [hdef, inner_add_right, inner_sum, Finset.sum_eq_zero, add_zero]
      intro k hk
      rw [inner_smul_right, gramSchmidt_orthogonal ℂ f (Finset.mem_Iio.mp hk).ne', mul_zero]
    rw [h1, inner_self_eq_norm_sq_to_K]
    rfl
  have hw_le : ∀ i, ‖w i‖ ≤ a i := by
    intro i
    have hb := h i (fun j => (starRingEnd ℂ) (w i j)) (by
      intro k hk
      have := gramSchmidt_inv_triangular ℂ f hk
      rw [hinner] at this
      simpa [hfj] using this)
    have h2 : ∑ j, (starRingEnd ℂ) (w i j) * C i j = ((‖w i‖ : ℂ)) ^ 2 := by
      rw [← hii, hinner]
    have h3 : √(∑ j, ‖(starRingEnd ℂ) (w i j)‖ ^ 2) = ‖w i‖ := by
      rw [EuclideanSpace.norm_eq]; simp
    rw [h2, h3] at hb
    have h4 : ‖w i‖ ^ 2 ≤ a i * ‖w i‖ := by simpa using hb
    rcases (norm_nonneg (w i)).eq_or_lt with h0 | h0
    · rw [← h0]; exact (ha i).le
    · nlinarith
  let T : Matrix (Fin m) (Fin m) ℂ := fun i k => (if k = i then 1 else 0) +
    (if k < i then inner ℂ (w k) (f i) / (‖w k‖ : ℂ) ^ 2 else 0)
  let Wm : Matrix (Fin m) (Fin m) ℂ := fun i j => w i j
  have hC : C = T * Wm := by
    ext i j
    have hdef := congrArg (fun x : EuclideanSpace ℂ (Fin m) => x j) (gramSchmidt_def'' ℂ f i)
    simp only [PiLp.add_apply, WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, smul_eq_mul] at hdef
    rw [hfj] at hdef
    rw [hdef, Matrix.mul_apply]
    simp only [T, Wm, add_mul, Finset.sum_add_distrib, ite_mul, zero_mul, one_mul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    congr 1
    rw [← Finset.sum_filter]
    apply Finset.sum_congr
    · ext k; simp
    · intro k _; rfl
  have hT : T.det = 1 := by
    rw [Matrix.det_of_lowerTriangular T (by
      intro i k hik
      have hik' : i < k := hik
      simp [T, hik'.ne', hik'.not_gt])]
    simp [T]
  have hG : Wm * Wmᴴ = Matrix.diagonal (fun i => ((‖w i‖ : ℂ)) ^ 2) := by
    ext i k
    have h1 : (Wm * Wmᴴ) i k = inner ℂ (w k) (w i) := by
      rw [hinner, Matrix.mul_apply]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      show w i j * (Wmᴴ j k) = _
      rw [Matrix.conjTranspose_apply, mul_comm]
      rfl
    rw [h1]
    by_cases hik : i = k
    · subst hik
      rw [inner_self_eq_norm_sq_to_K]
      simp
    · rw [Matrix.diagonal_apply_ne _ hik]
      exact gramSchmidt_orthogonal ℂ f (Ne.symm hik)
  have hdet : ‖Wm.det‖ ^ 2 = ∏ i, ‖w i‖ ^ 2 := by
    have h1 := congrArg Matrix.det hG
    rw [Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_diagonal] at h1
    have h2 := congrArg norm h1
    rw [norm_mul, norm_star, norm_prod] at h2
    simpa [sq] using h2
  have hCd : ‖C.det‖ = ‖Wm.det‖ := by
    rw [hC, Matrix.det_mul, hT, one_mul]
  rw [hCd]
  have hprod : ∏ i, ‖w i‖ ^ 2 ≤ (∏ i, a i) ^ 2 := by
    rw [← Finset.prod_pow]
    exact Finset.prod_le_prod (fun i _ => by positivity)
      (fun i _ => pow_le_pow_left₀ (norm_nonneg _) (hw_le i) 2)
  rw [← hdet] at hprod
  exact (sq_le_sq₀ (norm_nonneg _) (Finset.prod_nonneg fun i _ => (ha i).le)).mp hprod

theorem common_denominator {K : Type*} [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) {m : ℕ} (c : Fin m → K)
    (hc : ∀ j, v.valuation K (c j) ≤ 1) :
    ∃ s : 𝓞 K, v.valuation K (s : K) = 1 ∧ ∃ y : Fin m → 𝓞 K, ∀ j, (y j : K) = (s : K) * c j := by
  classical
  choose n d hnd using fun j =>
    IsDedekindDomain.HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer v (c j) (hc j)
  refine ⟨∏ j, (d j : 𝓞 K), ?_, fun j => n j * ∏ l ∈ Finset.univ.erase j, (d l : 𝓞 K), ?_⟩
  · have hmem : (∏ j, (d j : 𝓞 K)) ∈ v.asIdeal.primeCompl :=
      Submonoid.prod_mem _ (fun j _ => (d j).2)
    have := (v.intValuation_eq_one_iff_mem_primeCompl _).mpr hmem
    rw [← IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap (K := K)] at this
    exact this
  · intro j
    have hj := hnd j
    have hsplit : (∏ l, (d l : 𝓞 K)) = (d j : 𝓞 K) * ∏ l ∈ Finset.univ.erase j, (d l : 𝓞 K) :=
      (Finset.mul_prod_erase Finset.univ (fun l => (d l : 𝓞 K)) (Finset.mem_univ j)).symm
    rw [hsplit]
    simp only [map_mul]
    push_cast
    rw [← hj]
    ring

theorem rows_independent {K : Type*} [Field K] (r m : ℕ) (J : Fin m → Fin r → K)
    (hjump : ∀ i : Fin m, ∃ (σ : K →+* ℂ) (c : Fin r → ℂ),
      (∀ k < i, ∑ j, c j * σ (J k j) = 0) ∧ ∑ j, c j * σ (J i j) ≠ 0)
    (w : Fin m → K) (hw : ∀ j, ∑ i, J i j * w i = 0) : w = 0 := by
  classical
  by_contra hne
  have hne' : (Finset.univ.filter (fun i => w i ≠ 0)).Nonempty := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
    exact ⟨i, by simpa using hi⟩
  obtain ⟨i, hi, hmax⟩ := Finset.exists_max_image _ id hne'
  have hwi : w i ≠ 0 := by simpa using hi
  obtain ⟨σ, c, hck, hci⟩ := hjump i
  have hsum : ∑ l, σ (w l) * ∑ j, c j * σ (J l j) = 0 := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero (fun j _ => ?_)
    have h1 := congrArg σ (hw j)
    rw [map_sum, map_zero] at h1
    simp only [map_mul] at h1
    calc ∑ l, σ (w l) * (c j * σ (J l j)) = c j * ∑ l, σ (J l j) * σ (w l) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun l _ => by ring)
      _ = 0 := by rw [h1, mul_zero]
  rw [Finset.sum_eq_single i] at hsum
  · exact (mul_ne_zero (by simpa using hwi) hci) hsum
  · intro l _ hl
    rcases lt_or_gt_of_ne hl with hlt | hgt
    · rw [hck l hlt, mul_zero]
    · have : w l = 0 := by
        by_contra h
        exact absurd (hmax l (by simpa using h)) (not_le.mpr hgt)
      rw [this, map_zero, zero_mul]
  · simp

theorem flag_slope : ∀ (K : Type) [Field K] [NumberField K] (r n' : ℕ) (J : ℕ → Fin r → K) (A : ℕ → (K →+* ℂ) → ℝ), (∀ i σ, 0 < A i σ) → (∀ (i : ℕ) (c : Fin r → 𝓞 K), (∀ k < i, ∑ j, (c j : K) * J k j = 0) → IsIntegral ℤ (∑ j, (c j : K) * J i j)) → (∀ i ≤ n', ∃ (σ : K →+* ℂ) (c : Fin r → ℂ), (∀ k < i, ∑ j, c j * σ (J k j) = 0) ∧ ∑ j, c j * σ (J i j) ≠ 0) → (∀ i ≤ n', ∀ (σ : K →+* ℂ) (c : Fin r → ℂ), (∀ k < i, ∑ j, c j * σ (J k j) = 0) → ‖∑ j, c j * σ (J i j)‖ ≤ A i σ * √(∑ j, ‖c j‖ ^ 2)) → 0 ≤ ∑ i ∈ Finset.range (n' + 1), ∑ σ : K →+* ℂ, Real.log (A i σ) := by
  intro K _ _ r n' J A hA hint hjump hbound
  classical
  let B : Matrix (Fin r) (Fin (n' + 1)) K := fun j i => J i j
  have hli : LinearIndependent K B.col := by
    rw [GroundTheory.PAdicHodge.linearIndependent_col_iff_mulVec_eq_zero]
    intro w hw
    refine rows_independent r (n' + 1) (fun i => J i) (fun i => ?_) w (fun j => ?_)
    · obtain ⟨σ, c, h1, h2⟩ := hjump i (by omega)
      exact ⟨σ, c, fun k hk => h1 k hk, h2⟩
    · exact congrFun hw j
  obtain ⟨s, hs⟩ := GroundTheory.PAdicHodge.exists_maxMinor_ne_zero_of_linearIndependent B hli
  let e : Fin (n' + 1) → Fin r := s.emb
  have he : Function.Injective e := s.emb.injective
  let D : Matrix (Fin (n' + 1)) (Fin (n' + 1)) K := fun i l => J i (e l)
  have hD0 : D.det ≠ 0 := by
    have : GroundTheory.PAdicHodge.maxMinor B s = D.det := by
      rw [← Matrix.det_transpose D]; rfl
    rwa [← this]
  have hDint : IsIntegral ℤ D.det := by
    obtain ⟨y, hy⟩ := IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one
      (R := 𝓞 K) K D.det (fun v => by
        apply val_det_le_one (v.valuation K)
        intro i c hc hk
        obtain ⟨t, ht, y, hy⟩ := common_denominator v c hc
        let C : Fin r → 𝓞 K := Function.extend e y 0
        have hC : ∀ X : Fin r → K, ∑ j, (C j : K) * X j = (t : K) * ∑ l, c l * X (e l) := by
          intro X
          rw [Finset.mul_sum]
          symm
          apply Fintype.sum_of_injective e he
          · intro j hj
            simp [C, Function.extend_apply' _ _ _ (by simpa using hj)]
          · intro l
            simp only [C, he.extend_apply, hy]
            ring
        have hI := hint i C (fun k hk' => by
          rw [hC]
          have hk2 : k < n' + 1 := lt_trans hk' i.2
          have := hk ⟨k, hk2⟩ (Fin.lt_def.mpr hk')
          rw [show (∑ l, c l * J k (e l)) = ∑ j, c j * D ⟨k, hk2⟩ j from rfl, this, mul_zero])
        rw [hC] at hI
        let z : 𝓞 K := ⟨_, hI⟩
        have hz' : v.valuation K ((t : K) * ∑ l, c l * J i (e l)) ≤ 1 :=
          v.valuation_le_one (K := K) z
        rw [map_mul, ht, one_mul] at hz'
        exact hz')
    rw [← hy]
    exact y.isIntegral_coe
  have hDarch : ∀ σ : K →+* ℂ, ‖σ D.det‖ ≤ ∏ i : Fin (n' + 1), A i σ := by
    intro σ
    have hmap : σ D.det = (D.map σ).det := by rw [RingHom.map_det]; rfl
    rw [hmap]
    apply norm_det_le (D.map σ) (fun i => A i σ) (fun i => hA _ _)
    intro i c hk
    let C : Fin r → ℂ := Function.extend e c 0
    have hC : ∀ X : Fin r → ℂ, ∑ j, C j * X j = ∑ l, c l * X (e l) := by
      intro X
      symm
      apply Fintype.sum_of_injective e he
      · intro j hj
        simp [C, Function.extend_apply' _ _ _ (by simpa using hj)]
      · intro l
        simp only [C, he.extend_apply]
    have hCn : ∑ j, ‖C j‖ ^ 2 = ∑ l, ‖c l‖ ^ 2 := by
      symm
      apply Fintype.sum_of_injective e he
      · intro j hj
        simp [C, Function.extend_apply' _ _ _ (by simpa using hj)]
      · intro l
        simp only [C, he.extend_apply]
    have := hbound i (by omega) σ C (fun k hk' => by
      have hk2 : k < n' + 1 := lt_trans hk' i.2
      rw [hC (fun j => σ (J k j))]
      exact hk ⟨k, hk2⟩ (Fin.lt_def.mpr hk'))
    rw [hC (fun j => σ (J i j)), hCn] at this
    exact this
  have h1 := one_le_prod_norm _ hDint hD0
  have hne : ∀ σ : K →+* ℂ, ‖σ D.det‖ ≠ 0 := fun σ => by
    simpa using hD0
  have hlog : 0 ≤ ∑ σ : K →+* ℂ, Real.log ‖σ D.det‖ := by
    rw [← Real.log_prod (fun σ _ => hne σ)]
    exact Real.log_nonneg h1
  have hle : ∀ σ : K →+* ℂ, Real.log ‖σ D.det‖ ≤ ∑ i ∈ Finset.range (n' + 1), Real.log (A i σ) := by
    intro σ
    rw [Finset.sum_range, ← Real.log_prod (fun i _ => (hA _ _).ne')]
    exact Real.log_le_log (lt_of_le_of_ne (norm_nonneg _) (hne σ).symm) (hDarch σ)
  rw [Finset.sum_comm]
  exact hlog.trans (Finset.sum_le_sum (fun σ _ => hle σ))

end GlobalTheory.CompanionTheory.Ar.FlagSlope
