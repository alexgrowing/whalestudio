import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.BasisOfLinearIndependentOfCardEqFinrank

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.TraceNormBounds

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Polynomial Module

variable {Ω : Type*} [Field Ω] [CharZero Ω] {κ : Type*} {D : ℕ}

theorem hc_mul_homog {σ : Type*} {p : MvPolynomial σ ℤ} {a : ℕ} (hp : p.IsHomogeneous a)
    (q : MvPolynomial σ ℤ) (b : ℕ) :
    MvPolynomial.homogeneousComponent (a + b) (p * q) =
      p * MvPolynomial.homogeneousComponent b q := by
  classical
  conv_lhs => rw [← MvPolynomial.sum_homogeneousComponent q]
  rw [Finset.mul_sum, map_sum, Finset.sum_eq_single b]
  · rw [MvPolynomial.homogeneousComponent_of_mem ((MvPolynomial.mem_homogeneousSubmodule _ _).mpr
      (hp.mul (MvPolynomial.homogeneousComponent_isHomogeneous b q))), if_pos rfl]
  · intro k _ hk
    rw [MvPolynomial.homogeneousComponent_of_mem ((MvPolynomial.mem_homogeneousSubmodule _ _).mpr
      (hp.mul (MvPolynomial.homogeneousComponent_isHomogeneous k q))), if_neg (by omega)]
  · intro hb
    rw [MvPolynomial.homogeneousComponent_eq_zero b q (by simp at hb; omega), mul_zero, map_zero]

private theorem X_pow_dvd_of_le_degrees {σ : Type*} (i : σ) (m : ℕ) (p : MvPolynomial σ ℤ)
    (h : ∀ d ∈ p.support, m ≤ d i) : MvPolynomial.X i ^ m ∣ p := by
  classical
  rw [p.as_sum]
  refine Finset.dvd_sum fun d hd => ?_
  have hle : Finsupp.single i m ≤ d := Finsupp.single_le_iff.mpr (h d hd)
  exact ⟨MvPolynomial.monomial (d - Finsupp.single i m) (MvPolynomial.coeff d p), by
    rw [MvPolynomial.X_pow_eq_monomial, MvPolynomial.monomial_mul, one_mul, add_tsub_cancel_of_le hle]⟩

theorem X_pow_dvd_homogeneous_one_var {H : MvPolynomial (Fin (0 + 1)) ℤ} {M m : ℕ} (hH : H.IsHomogeneous M)
    (hm : m ≤ M) : MvPolynomial.X 0 ^ m ∣ H := by
  apply X_pow_dvd_of_le_degrees
  intro d hd
  have hdeg : d.degree = M := by
    by_contra hne
    exact (MvPolynomial.mem_support_iff.mp hd) (hH.coeff_eq_zero hne)
  rw [Finsupp.degree_eq_sum, Fin.sum_univ_one] at hdeg
  omega

private theorem coord_ne_zero_of_coordIdeal_eq_bot (y : Fin (D + 1) → Ω) (hfree : coordIdeal ℤ y = ⊥) (i : Fin (D + 1)) :
    y i ≠ 0 := by
  intro h0
  have hmem : (MvPolynomial.X i : MvPolynomial (Fin (D + 1)) ℤ) ∈ coordIdeal ℤ y := by
    rw [coordIdeal, RingHom.mem_ker]
    simp [coneMap, h0]
  rw [hfree, Ideal.mem_bot] at hmem
  exact MvPolynomial.X_ne_zero i hmem

private theorem coneMap_of_isHomogeneous_arakelov_geometry {n : ℕ} (y : Fin (D + 1) → Ω) (P : MvPolynomial (Fin (D + 1)) ℤ)
    (hP : P.IsHomogeneous n) :
    coneMap ℤ y P = Polynomial.C (MvPolynomial.aeval y P) * Polynomial.X ^ n := by
  classical
  conv_lhs => rw [P.as_sum]
  conv_rhs => rw [P.as_sum]
  simp only [map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdeg : d.degree = n := by
    by_contra hne
    exact (MvPolynomial.mem_support_iff.mp hd) (hP.coeff_eq_zero hne)
  rw [← hdeg, Finsupp.degree_eq_sum]
  simp only [coneMap, MvPolynomial.aeval_monomial]
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, ← map_pow, ← map_prod, map_mul,
    eq_intCast, map_intCast]
  ring

theorem X_zero_pow_dvd_of_isHomogeneous_aeval (y : Fin (D + 1) → Ω) (hfree : coordIdeal ℤ y = ⊥) (u : Ω) (n m : ℕ)
    (H : Fin (D + 1) → MvPolynomial (Fin (D + 1)) ℤ) (hH : ∀ l, (H l).IsHomogeneous (m + n))
    (hu : ∀ l, y l ^ m * u = MvPolynomial.aeval y (H l)) : MvPolynomial.X 0 ^ m ∣ H 0 := by
  rcases Nat.eq_zero_or_pos D with rfl | hD
  · exact X_pow_dvd_homogeneous_one_var (hH 0) (by omega)
  have hl1 : (⟨1, by omega⟩ : Fin (D + 1)) ≠ 0 := by simp [Fin.ext_iff]
  have hPh : (MvPolynomial.X ⟨1, by omega⟩ ^ m * H 0 - MvPolynomial.X 0 ^ m * H ⟨1, by omega⟩ :
      MvPolynomial (Fin (D + 1)) ℤ).IsHomogeneous (m + (m + n)) :=
    ((MvPolynomial.isHomogeneous_X_pow _ _).mul (hH 0)).sub ((MvPolynomial.isHomogeneous_X_pow _ _).mul (hH _))
  have hPy : MvPolynomial.aeval y (MvPolynomial.X ⟨1, by omega⟩ ^ m * H 0 - MvPolynomial.X 0 ^ m * H ⟨1, by omega⟩ :
      MvPolynomial (Fin (D + 1)) ℤ) = 0 := by
    simp only [map_sub, map_mul, map_pow, MvPolynomial.aeval_X, ← hu]
    ring
  have hP0 : (MvPolynomial.X ⟨1, by omega⟩ ^ m * H 0 - MvPolynomial.X 0 ^ m * H ⟨1, by omega⟩ :
      MvPolynomial (Fin (D + 1)) ℤ) = 0 := by
    have hmem : (MvPolynomial.X ⟨1, by omega⟩ ^ m * H 0 - MvPolynomial.X 0 ^ m * H ⟨1, by omega⟩ :
        MvPolynomial (Fin (D + 1)) ℤ) ∈ coordIdeal ℤ y := by
      rw [coordIdeal, RingHom.mem_ker, coneMap_of_isHomogeneous_arakelov_geometry y _ hPh, hPy]
      simp
    rw [hfree, Ideal.mem_bot] at hmem
    exact hmem
  have hPeq := sub_eq_zero.mp hP0
  apply X_pow_dvd_of_le_degrees
  intro d hd
  have h1 : MvPolynomial.coeff (d + Finsupp.single ⟨1, by omega⟩ m) (MvPolynomial.X 0 ^ m * H ⟨1, by omega⟩) ≠ 0 := by
    rw [← hPeq, MvPolynomial.X_pow_eq_monomial, MvPolynomial.coeff_monomial_mul', if_pos le_add_self,
      add_tsub_cancel_right, one_mul]
    exact MvPolynomial.mem_support_iff.mp hd
  rw [MvPolynomial.X_pow_eq_monomial, MvPolynomial.coeff_monomial_mul'] at h1
  split_ifs at h1 with hle
  · have := Finsupp.single_le_iff.mp hle
    simpa [Finsupp.single_apply, Ne.symm hl1] using this
  · exact absurd rfl h1

theorem mem_sec_of_charts (y : Fin (D + 1) → Ω) (hfree : coordIdeal ℤ y = ⊥) (u : Ω) (n m : ℕ)
    (H : Fin (D + 1) → MvPolynomial (Fin (D + 1)) ℤ) (hH : ∀ l, (H l).IsHomogeneous (m + n))
    (hu : ∀ l, y l ^ m * u = MvPolynomial.aeval y (H l)) : u ∈ sec ℤ y n := by
  have hy0 : y 0 ≠ 0 := coord_ne_zero_of_coordIdeal_eq_bot y hfree 0
  obtain ⟨G, hG⟩ := X_zero_pow_dvd_of_isHomogeneous_aeval y hfree u n m H hH hu
  have hG' : MvPolynomial.X 0 ^ m * MvPolynomial.homogeneousComponent n G = H 0 := by
    rw [← hc_mul_homog (MvPolynomial.isHomogeneous_X_pow (0 : Fin (D + 1)) m) G n, ← hG,
      MvPolynomial.homogeneousComponent_of_mem ((MvPolynomial.mem_homogeneousSubmodule _ _).mpr (hH 0)), if_pos rfl]
  refine Submodule.mem_map.mpr ⟨MvPolynomial.homogeneousComponent n G,
    (MvPolynomial.mem_homogeneousSubmodule _ _).mpr (MvPolynomial.homogeneousComponent_isHomogeneous n G), ?_⟩
  show MvPolynomial.aeval y (MvPolynomial.homogeneousComponent n G) = u
  have h2 := hu 0
  rw [← hG', map_mul, map_pow, MvPolynomial.aeval_X] at h2
  exact (mul_left_cancel₀ (pow_ne_zero m hy0) h2).symm

theorem trace_chart_eq [Fintype κ] (x : κ → Ω) (e : Fin (D + 1) → κ) (h0 : x (e 0) ≠ 0)
    (l : Fin (D + 1)) (hl : x (e l) ≠ 0) (n : ℕ) {s : Ω} (hs : s ∈ sec ℤ x n) :
    ((Algebra.trace (fnField (x ∘ e)) (IntermediateField.extendScalars (fnField_comp_le' x e))
      ⟨s / x (e l) ^ n, sec_div_mem x (e l) hs⟩ : fnField (x ∘ e)) : Ω) =
    (x (e 0) / x (e l)) ^ n *
      ((Algebra.trace (fnField (x ∘ e)) (IntermediateField.extendScalars (fnField_comp_le' x e))
        ⟨s / x (e 0) ^ n, sec_div_mem x (e 0) hs⟩ : fnField (x ∘ e)) : Ω) := by
  have hc : (x (e 0) / x (e l)) ^ n ∈ fnField (x ∘ e) := pow_mem (div_mem_fnField (x ∘ e) 0 l) n
  have heq : (⟨s / x (e l) ^ n, sec_div_mem x (e l) hs⟩ : IntermediateField.extendScalars (fnField_comp_le' x e)) =
      (⟨(x (e 0) / x (e l)) ^ n, hc⟩ : fnField (x ∘ e)) • ⟨s / x (e 0) ^ n, sec_div_mem x (e 0) hs⟩ := by
    apply Subtype.ext
    show s / x (e l) ^ n = (x (e 0) / x (e l)) ^ n * (s / x (e 0) ^ n)
    rw [div_pow]
    field_simp
  rw [heq, LinearMap.map_smul, smul_eq_mul]
  rfl

theorem chart_elem (x : κ → Ω) (e : Fin (D + 1) → κ) (l : Fin (D + 1)) (a : fnField (x ∘ e))
    (ha : a ∈ chartRing x e l) :
    ∃ g : MvPolynomial {k // k ≠ l} ℤ, (a : Ω) = MvPolynomial.aeval (fun k => x (e k.1) / x (e l)) g := by
  rw [chartRing, Algebra.adjoin_range_eq_range_aeval] at ha
  obtain ⟨g, rfl⟩ := ha
  refine ⟨g, ?_⟩
  induction g using MvPolynomial.induction_on <;> simp_all [chartGen]

theorem homog_of_chart (x : κ → Ω) (e : Fin (D + 1) → κ) (l : Fin (D + 1)) (a : fnField (x ∘ e))
    (ha : a ∈ chartRing x e l) (hl : x (e l) ≠ 0) :
    ∃ N0, ∀ N, N0 ≤ N → ∃ H : MvPolynomial (Fin (D + 1)) ℤ, H.IsHomogeneous N ∧
      x (e l) ^ N * (a : Ω) = MvPolynomial.aeval (x ∘ e) H := by
  obtain ⟨g, hg⟩ := chart_elem x e l a ha
  rw [hg]
  clear hg
  induction g using MvPolynomial.induction_on
  · rename_i c
    refine ⟨0, fun N _ => ⟨MvPolynomial.C c * MvPolynomial.X l ^ N, ?_, ?_⟩⟩
    · simpa using (MvPolynomial.isHomogeneous_C (Fin (D + 1)) c).mul (MvPolynomial.isHomogeneous_X_pow l N)
    · simp [mul_comm]
  · rename_i p q hp hq
    obtain ⟨N1, h1⟩ := hp
    obtain ⟨N2, h2⟩ := hq
    refine ⟨max N1 N2, fun N hN => ?_⟩
    obtain ⟨H1, hH1, e1⟩ := h1 N (le_of_max_le_left hN)
    obtain ⟨H2, hH2, e2⟩ := h2 N (le_of_max_le_right hN)
    exact ⟨H1 + H2, hH1.add hH2, by rw [map_add, mul_add, e1, e2, map_add]⟩
  · rename_i p k hp
    obtain ⟨N1, h1⟩ := hp
    refine ⟨N1 + 1, fun N hN => ?_⟩
    obtain ⟨N', rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩
    obtain ⟨H, hH, e1⟩ := h1 N' (by omega)
    refine ⟨H * MvPolynomial.X k.1, hH.mul (MvPolynomial.isHomogeneous_X ℤ k.1), ?_⟩
    rw [map_mul, MvPolynomial.aeval_X, map_mul, MvPolynomial.aeval_X, ← e1]
    simp only [Function.comp]
    field_simp
    ring

theorem trace_mem_sec [Fintype κ] (x : κ → Ω) (e : Fin (D + 1) → κ) (h : IsProjFrame x e) (n : ℕ)
    {s : Ω} (hs : s ∈ sec ℤ x n) :
    x (e 0) ^ n * ((Algebra.trace (fnField (x ∘ e))
      (IntermediateField.extendScalars (fnField_comp_le' x e))
        ⟨s / x (e 0) ^ n, sec_div_mem x (e 0) hs⟩ : fnField (x ∘ e)) : Ω) ∈ sec ℤ (x ∘ e) n := by
  have hne : ∀ j, x (e j) ≠ 0 := fun j => coord_ne_zero_of_coordIdeal_eq_bot (x ∘ e) h.free j
  choose N0 hN0 using fun j => homog_of_chart x e j _ (trace_mem_chart x e h j n hs) (hne j)
  choose H hHh hHe using fun j => hN0 j (Finset.univ.sup N0 + n)
    (le_trans (Finset.le_sup (Finset.mem_univ j)) (Nat.le_add_right _ _))
  refine mem_sec_of_charts (x ∘ e) h.free _ n (Finset.univ.sup N0) H hHh (fun j => ?_)
  rw [← hHe j, trace_chart_eq x e (hne 0) j (hne j) n hs]
  simp only [Function.comp_apply]
  have hj := hne j
  rw [div_pow, pow_add]
  field_simp

theorem eq_zero_of_trace' [Fintype κ] (x : κ → Ω) (e : Fin (D + 1) → κ) (h : IsRatProjFrame x e)
    {k : ℕ} (ε : Fin (projDeg x e) → Ω) (hε : ∀ l, ε l ∈ sec ℤ x k)
    (hli : LinearIndependent (fnField (x ∘ e)) ε) (n : ℕ) {s : Ω} (hs : s ∈ sec ℤ x n)
    (h0 : ∀ l, ((Algebra.trace (fnField (x ∘ e))
      (IntermediateField.extendScalars (fnField_comp_le' x e))
        ⟨s * ε l / x (e 0) ^ (n + k), sec_div_mem x (e 0) (mul_mem_sec x hs (hε l))⟩ :
          fnField (x ∘ e)) : Ω) = 0) : s = 0 := by
  have hx0 : x (e 0) ≠ 0 := coord_ne_zero_of_coordIdeal_eq_bot (x ∘ e) h.free 0
  have ht := eq_zero_of_trace x e h ε hε hli ⟨s / x (e 0) ^ n, sec_div_mem x (e 0) hs⟩ (fun l => by
    have e1 : (⟨s / x (e 0) ^ n, sec_div_mem x (e 0) hs⟩ : IntermediateField.extendScalars (fnField_comp_le' x e)) *
        ⟨ε l / x (e 0) ^ k, sec_div_mem x (e 0) (hε l)⟩ =
        ⟨s * ε l / x (e 0) ^ (n + k), sec_div_mem x (e 0) (mul_mem_sec x hs (hε l))⟩ := by
      apply Subtype.ext
      show s / x (e 0) ^ n * (ε l / x (e 0) ^ k) = s * ε l / x (e 0) ^ (n + k)
      rw [pow_add, div_mul_div_comm]
    rw [e1]
    exact Subtype.ext (h0 l))
  have h2 := congrArg Subtype.val ht
  simpa [hx0] using h2

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.TraceNormBounds
