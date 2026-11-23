import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.CSandwichStD

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.GeometryOfNumbersTheory MvPolynomial MeasureTheory Module Filter Asymptotics
open scoped ComplexOrder Matrix

variable {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ] {D : ℕ}

theorem sum_secFun_eq' {x : Ix κ → Ω} {n r : ℕ} {b : Fin r → MvPolynomial (Ix κ) ℚ}
    (hb : IsSecBasis x n b) (g : MvPolynomial (Ix κ) ℤ) (hg : g.IsHomogeneous n) (c : Fin r → ℤ)
    (hc : ∑ j, (c j : Ω) * aeval x (b j) = aeval x g) :
    ∀ z ∈ pts (coordIdeal ℤ x),
      ∑ j, (c j : ℂ) * secFun (b j) z = eval z (map (Int.castRingHom ℂ) g) := by
  choose f hf hbf using hb.1
  intro z hz
  set h : MvPolynomial (Ix κ) ℤ := ∑ j, c j • f j - g with hh_def
  have hh : h.IsHomogeneous n := by
    have := Submodule.sub_mem _ (Submodule.sum_mem (homogeneousSubmodule (Ix κ) ℤ n) (t := Finset.univ)
      fun j _ => Submodule.smul_mem _ (c j) ((mem_homogeneousSubmodule _ _).mpr (hf j)))
      ((mem_homogeneousSubmodule _ _).mpr hg)
    exact (mem_homogeneousSubmodule _ _).mp this
  have hx : aeval x h = 0 := by
    rw [hh_def, map_sub, map_sum, ← hc, sub_eq_zero]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_zsmul, zsmul_eq_mul, hbf j, aeval_map_intQ]
  have h0 := hz.2 h (mem_coordIdeal_of_isHomogeneous (o := ℤ) (x := x) hh hx)
  rw [hh_def, map_sub, map_sum, map_sub, map_sum, sub_eq_zero] at h0
  rw [← h0]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_zsmul, map_zsmul, zsmul_eq_mul, hbf j, secFun_map_intQ]

theorem bNormSq_le_of_pts' {x : Ix κ → Ω} {m : ConeMetric ℂ (Ix κ)} {μ : Measure (Ix κ → ℂ)}
    (hg : IsGood D x m μ) {n r : ℕ} (s : Fin r → (Ix κ → ℂ) → ℂ) (c : Fin r → ℂ) {B : ℝ}
    (h : ∀ z ∈ pts (coordIdeal ℤ x), ‖∑ j, c j * s j z‖ ^ 2 * wgt m n z ≤ B) :
    bNormSq μ s (wgt m n) c ≤ B := by
  have := hg.vol.1
  have hae : ∀ᵐ z ∂μ, z ∈ pts (coordIdeal ℤ x) := ae_iff.mpr hg.vol.2.1
  unfold bNormSq
  calc ∫ z, ‖∑ j, c j * s j z‖ ^ 2 * wgt m n z ∂μ ≤ ∫ _z, B ∂μ := by
        refine integral_mono_of_nonneg (ae_of_all _ fun z => ?_) (integrable_const B) ?_
        · exact mul_nonneg (sq_nonneg _) (inv_nonneg.mpr (pow_nonneg (m.nonneg z) _))
        · filter_upwards [hae] with z hz using h z hz
    _ = B := by simp

theorem sum_mulVec_secFun {x : Ix κ → Ω} {n r R : ℕ} {b : Fin r → MvPolynomial (Ix κ) ℚ}
    (hb : IsSecBasis x n b) (M : Matrix (Fin r) (Fin R) ℤ) (Q : Fin R → MvPolynomial (Ix κ) ℤ)
    (hQ : ∀ p, (Q p).IsHomogeneous n)
    (hM : ∀ p, ∑ j, (M j p : Ω) * aeval x (b j) = aeval x (Q p)) (c : Fin R → ℂ) :
    ∀ z ∈ pts (coordIdeal ℤ x), ∑ j, (M.map (Int.cast : ℤ → ℂ) *ᵥ c) j * secFun (b j) z =
      ∑ p, c p * eval z (map (Int.castRingHom ℂ) (Q p)) := by
  intro z hz
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [← sum_secFun_eq' hb (Q p) (hQ p) (fun j => M j p) (hM p) z hz, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem diag_conj_eq {r s : ℕ} (N : Matrix (Fin s) (Fin r) ℂ) (G : Matrix (Fin s) (Fin s) ℂ)
    (i : Fin r) :
    (Nᴴ * G * N) i i = star (N *ᵥ Pi.single i 1) ⬝ᵥ G *ᵥ (N *ᵥ Pi.single i 1) := by
  simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, Pi.star_apply,
    Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

theorem pt_lower {x : Ix κ → Ω} {e : Fin (D + 1) → Ix κ} {m : ConeMetric ℂ (Ix κ)}
    (hFS : IsPullFS x e m) {N kε δ : ℕ} (H : Fin δ → MvPolynomial (Ix κ) ℤ) {Cε : ℝ}
    (hCε0 : 0 ≤ Cε)
    (hCε : ∀ l, ∀ z ∈ pts (coordIdeal ℤ x),
      ‖eval z (map (Int.castRingHom ℂ) (H l))‖ ≤ Cε * m.ρ z ^ kε)
    (c : Fin (δ * (Finset.Nat.antidiagonalTuple (D + 1) N).card) → ℂ) {z : Ix κ → ℂ}
    (hz : z ∈ pts (coordIdeal ℤ x)) :
    ‖∑ p, c p * eval z (map (Int.castRingHom ℂ) (prodForm e (adtEnum D N (finProdFinEquiv.symm p).2)
        (H (finProdFinEquiv.symm p).1)))‖ ^ 2 * wgt m (N + kε) z ≤
      Cε ^ 2 * δ * ((N + D).choose D : ℝ) *
        ∑ l : Fin δ, ∑ i, ‖c (finProdFinEquiv (l, i))‖ ^ 2 * monoNormSq (adtEnum D N i) := by
  have hρ0 : 0 ≤ m.ρ z := m.nonneg z
  have hBn0 : (0 : ℝ) ≤ ((N + D).choose D : ℝ) := Nat.cast_nonneg _
  set q : Fin δ → ℝ := fun l =>
    ∑ i, ‖c (finProdFinEquiv (l, i))‖ ^ 2 * monoNormSq (adtEnum D N i) with hq
  have hq0 : ∀ l, 0 ≤ q l := fun l =>
    Finset.sum_nonneg fun i _ => mul_nonneg (sq_nonneg _) (monoNormSq_pos _).le
  set P : Fin δ → ℂ := fun l =>
    ∑ i, c (finProdFinEquiv (l, i)) * monoC (adtEnum D N i) (z ∘ e) with hP
  have hsum : ∑ p, c p * eval z (map (Int.castRingHom ℂ) (prodForm e
      (adtEnum D N (finProdFinEquiv.symm p).2) (H (finProdFinEquiv.symm p).1))) =
      ∑ l, eval z (map (Int.castRingHom ℂ) (H l)) * P l := by
    rw [← Equiv.sum_comp finProdFinEquiv, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [hP, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Equiv.symm_apply_apply, eval_prodForm]; ring
  have hPl : ∀ l, ‖P l‖ ≤ Real.sqrt (((N + D).choose D : ℝ) * q l) * m.ρ z ^ N := fun l => by
    have h := form_enum_sq_le D N (fun i => c (finProdFinEquiv (l, i))) (z ∘ e)
    rw [sqN_comp_eq hFS hz] at h
    refine norm_le_sqrt_of_sq_le (norm_nonneg _) (mul_nonneg hBn0 (hq0 l)) (pow_nonneg hρ0 N) ?_
    calc ‖P l‖ ^ 2 ≤ ((N + D).choose D : ℝ) * (m.ρ z ^ 2) ^ N * q l := h
      _ = ((N + D).choose D : ℝ) * q l * (m.ρ z ^ N) ^ 2 := by ring
  have hmain : ‖∑ l, eval z (map (Int.castRingHom ℂ) (H l)) * P l‖ ≤
      (Cε * ∑ l, Real.sqrt (((N + D).choose D : ℝ) * q l)) * m.ρ z ^ (N + kε) := by
    refine (norm_sum_le _ _).trans ?_
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_le_sum fun l _ => ?_
    rw [norm_mul]
    calc ‖eval z (map (Int.castRingHom ℂ) (H l))‖ * ‖P l‖ ≤
          (Cε * m.ρ z ^ kε) * (Real.sqrt (((N + D).choose D : ℝ) * q l) * m.ρ z ^ N) :=
          mul_le_mul (hCε l z hz) (hPl l) (norm_nonneg _) (by positivity)
      _ = Cε * Real.sqrt (((N + D).choose D : ℝ) * q l) * m.ρ z ^ (N + kε) := by ring
  rw [hsum]
  refine (sq_wgt_le_of_le hz.1 (norm_nonneg _) hmain).trans ?_
  have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.univ)
    (f := fun l => Real.sqrt (((N + D).choose D : ℝ) * q l))
  simp only [Finset.card_univ, Fintype.card_fin] at hcs
  rw [mul_pow]
  calc Cε ^ 2 * (∑ l, Real.sqrt (((N + D).choose D : ℝ) * q l)) ^ 2 ≤
        Cε ^ 2 * (δ * ∑ l, Real.sqrt (((N + D).choose D : ℝ) * q l) ^ 2) :=
        mul_le_mul_of_nonneg_left hcs (sq_nonneg _)
    _ = Cε ^ 2 * δ * ((N + D).choose D : ℝ) * ∑ l, q l := by
        simp_rw [Real.sq_sqrt (mul_nonneg hBn0 (hq0 _))]
        rw [← Finset.mul_sum]; ring

theorem pt_small {x : Ix κ → Ω} {e : Fin (D + 1) → Ix κ} {m : ConeMetric ℂ (Ix κ)}
    (hFS : IsPullFS x e m) {N k₀ : ℕ} {a : Fin (D + 1) → ℕ} (ha : ∑ t, a t = N)
    (t : MvPolynomial (Ix κ) ℤ) {Ct : ℝ}
    (hCt : ∀ z ∈ pts (coordIdeal ℤ x), ‖eval z (map (Int.castRingHom ℂ) t)‖ ≤ Ct * m.ρ z ^ k₀)
    {z : Ix κ → ℂ} (hz : z ∈ pts (coordIdeal ℤ x)) :
    ‖eval z (map (Int.castRingHom ℂ) (prodForm e a t))‖ ^ 2 * wgt m (N + k₀) z ≤ Ct ^ 2 := by
  have hρ0 : 0 ≤ m.ρ z := m.nonneg z
  have hm : ‖monoC a (z ∘ e)‖ ≤ m.ρ z ^ N := by
    have h := norm_monoC_sq_le a (z ∘ e)
    have e2 : (m.ρ z ^ 2) ^ N = (m.ρ z ^ N) ^ 2 := by ring
    rw [sqN_comp_eq hFS hz, ha, e2] at h
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (pow_nonneg hρ0 N) two_ne_zero).mp h
  refine sq_wgt_le_of_le hz.1 (norm_nonneg _) ?_
  rw [eval_prodForm, norm_mul]
  have h2 := hCt z hz
  calc ‖monoC a (z ∘ e)‖ * ‖eval z (map (Int.castRingHom ℂ) t)‖ ≤ m.ρ z ^ N * (Ct * m.ρ z ^ k₀) :=
        mul_le_mul hm h2 (norm_nonneg _) (pow_nonneg hρ0 N)
    _ = Ct * m.ρ z ^ (N + k₀) := by ring

theorem aeval_monoZ {N : ℕ} {S : Type*} [CommRing S] (a : Fin N → ℕ) (y : Fin N → S) :
    aeval y (monoZ a) = ∏ i, y i ^ a i := by
  simp only [monoZ, MvPolynomial.aeval_monomial, map_one, one_mul]
  rw [Finsupp.prod_fintype _ _ (fun i => pow_zero _)]
  simp

theorem log_le_div_mul {L : ℝ} (hL : 0 ≤ L) {n : ℕ} (hn : 1 ≤ n) :
    L ≤ L / Real.log 2 * Real.log (n + 1) := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h3 : Real.log 2 ≤ Real.log (n + 1) := Real.log_le_log (by norm_num) (by linarith)
  calc L = L / Real.log 2 * Real.log 2 := by field_simp
    _ ≤ L / Real.log 2 * Real.log (n + 1) := mul_le_mul_of_nonneg_left h3 (div_nonneg hL h2.le)

theorem sec_le_span_prod {x : Ix κ → Ω} {e : Fin (D + 1) → Ix κ} {n k₀ r₀ : ℕ}
    (hmul : sec ℤ x n = sec ℤ (x ∘ e) (n - k₀) * sec ℤ x k₀) {tb : Fin r₀ → MvPolynomial (Ix κ) ℚ}
    (htb : IsSecBasis x k₀ tb) (Tf : Fin r₀ → MvPolynomial (Ix κ) ℤ)
    (hTfb : ∀ i, tb i = map (Int.castRingHom ℚ) (Tf i)) :
    sec ℤ x n ≤ Submodule.span ℤ (Set.range fun s : Fin (Finset.Nat.antidiagonalTuple (D + 1) (n - k₀)).card ×
      Fin r₀ => aeval x (prodForm e (adtEnum D (n - k₀) s.1) (Tf s.2))) := by
  rw [hmul, Submodule.mul_le]
  intro a ha t ht
  obtain ⟨pa, hpa, rfl⟩ := Submodule.mem_map.mp ha
  have hpa' : pa.IsHomogeneous (n - k₀) := (mem_homogeneousSubmodule _ _).mp hpa
  rw [← htb.2.2, Submodule.mem_span_range_iff_exists_fun] at ht
  obtain ⟨cc, rfl⟩ := ht
  have ea : (aeval (x ∘ e)).toLinearMap pa = ∑ i, (coeff (Finsupp.equivFunOnFinite.symm
      (adtEnum D (n - k₀) i)) pa : ℤ) • ∏ t, (x ∘ e) t ^ adtEnum D (n - k₀) i t := by
    rw [AlgHom.toLinearMap_apply, aeval_eq_sum_adt pa hpa', ← sum_adtEnum]
    simp only [zsmul_eq_mul]
  rw [ea, Finset.sum_mul_sum]
  refine Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun i₀ _ => ?_
  have : (coeff (Finsupp.equivFunOnFinite.symm (adtEnum D (n - k₀) i)) pa : ℤ) •
      (∏ t, (x ∘ e) t ^ adtEnum D (n - k₀) i t) * cc i₀ • aeval x (tb i₀) =
      (coeff (Finsupp.equivFunOnFinite.symm (adtEnum D (n - k₀) i)) pa * cc i₀) •
        aeval x (prodForm e (adtEnum D (n - k₀) i) (Tf i₀)) := by
    rw [aeval_prodForm, hTfb i₀, aeval_map_intQ]
    simp only [zsmul_eq_mul]; push_cast; ring
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨(i, i₀), rfl⟩)

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
