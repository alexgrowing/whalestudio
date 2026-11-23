import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.AlgPoly

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem form_zero (a : K → ℕ) : IsMultiHomog (0 : MRing ι) a := by
  intro m hm
  simp at hm

theorem form_one : IsMultiHomog (1 : MRing ι) (0 : K → ℕ) := by
  classical
  intro m hm k
  rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_one] at hm
  split_ifs at hm with h0
  · subst h0
    simp
  · exact absurd rfl hm

theorem form_mul {f g : MRing ι} {a b : K → ℕ} (hf : IsMultiHomog f a) (hg : IsMultiHomog g b) :
    IsMultiHomog (f * g) (a + b) := by
  classical
  intro m hm k
  obtain ⟨m1, hm1, m2, hm2, rfl⟩ := Finset.mem_add.1 (MvPolynomial.support_mul f g hm)
  simp only [Finsupp.add_apply, Finset.sum_add_distrib, Pi.add_apply, hf m1 hm1 k, hg m2 hm2 k]

theorem form_add {f g : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) (hg : IsMultiHomog g a) :
    IsMultiHomog (f + g) a := by
  classical
  intro m hm k
  rcases Finset.mem_union.1 (MvPolynomial.support_add hm) with h | h
  · exact hf m h k
  · exact hg m h k

theorem form_neg {f : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) : IsMultiHomog (-f) a := by
  intro m hm
  rw [MvPolynomial.support_neg] at hm
  exact hf m hm

theorem form_sub {f g : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) (hg : IsMultiHomog g a) :
    IsMultiHomog (f - g) a := by
  rw [sub_eq_add_neg]
  exact form_add hf (form_neg hg)

theorem form_sum {σ : Type*} (s : Finset σ) (f : σ → MRing ι) {a : K → ℕ}
    (hf : ∀ x ∈ s, IsMultiHomog (f x) a) : IsMultiHomog (∑ x ∈ s, f x) a := by
  exact Finset.sum_induction f (fun p => IsMultiHomog p a) (fun _ _ h1 h2 => form_add h1 h2)
    (form_zero a) hf

theorem form_natCast_mul {f : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) (n : ℕ) :
    IsMultiHomog (f * (n : MRing ι)) a := by
  induction n with
  | zero => simpa using form_zero a
  | succ n ih =>
    rw [Nat.cast_succ, mul_add, mul_one]
    exact form_add ih hf

theorem cone_form (y : (Σ k, ι k) → Ω) {h : MRing ι} {d : K → ℕ} (hh : IsMultiHomog h d) :
    mConeMap y h = MvPolynomial.C (aeval y h) * ∏ k, (X k : MvPolynomial K Ω) ^ d k := by
  classical
  have key : ∀ v ∈ h.support, mConeMap y (monomial v (coeff v h)) =
      MvPolynomial.C (aeval y (monomial v (coeff v h))) * ∏ k, (X k : MvPolynomial K Ω) ^ d k := by
    intro v hv
    have hX : (v.prod fun p e => (X p.1 : MvPolynomial K Ω) ^ e) = ∏ k, (X k : MvPolynomial K Ω) ^ d k := by
      rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fintype.prod_sigma]
      exact Finset.prod_congr rfl fun k _ => by simp only [Finset.prod_pow_eq_pow_sum, hh v hv k]
    have h1 : (v.prod fun p e => (MvPolynomial.C (y p) * X p.1 : MvPolynomial K Ω) ^ e) =
        MvPolynomial.C (v.prod fun p e => y p ^ e) * v.prod fun p e => (X p.1 : MvPolynomial K Ω) ^ e := by
      rw [map_finsuppProd, ← Finsupp.prod_mul]
      exact Finsupp.prod_congr fun p _ => by simp only [mul_pow, map_pow]
    show (aeval fun p => MvPolynomial.C (y p) * (X p.1 : MvPolynomial K Ω)) (monomial v (coeff v h)) = _
    simp only [MvPolynomial.aeval_monomial]
    rw [h1, hX, map_mul]
    simp only [algebraMap_int_eq, eq_intCast, Int.coe_castRingHom, map_intCast]
    ring
  rw [h.as_sum]
  simp only [map_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl key

theorem mem_of_aeval_eq_zero {y : (Σ k, ι k) → Ω} {h : MRing ι} {d : K → ℕ} (hh : IsMultiHomog h d)
    (h0 : aeval y h = 0) : h ∈ mCoordIdeal y := by
  show h ∈ RingHom.ker (mConeMap y)
  rw [RingHom.mem_ker, cone_form y hh, h0, map_zero, zero_mul]

theorem notMem_of_aeval_ne_zero {y : (Σ k, ι k) → Ω} {h : MRing ι} {d : K → ℕ} (hh : IsMultiHomog h d)
    (h0 : aeval y h ≠ 0) : h ∉ mCoordIdeal y := by
  intro hmem
  change h ∈ RingHom.ker (mConeMap y) at hmem
  rw [RingHom.mem_ker, cone_form y hh] at hmem
  rcases mul_eq_zero.1 hmem with h1 | h1
  · exact h0 (MvPolynomial.C_eq_zero.1 h1)
  · exact (Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (MvPolynomial.X_ne_zero k)) h1

theorem common_denominator {y : (Σ k, ι k) → Ω} (hy : Birational y) (s : Finset Ω) :
    ∃ (b : K → ℕ) (H : MRing ι), IsMultiHomog H b ∧ aeval y H ≠ 0 ∧
      ∀ x ∈ s, ∃ g : MRing ι, IsMultiHomog g b ∧ aeval y g = x * aeval y H := by
  classical
  refine Finset.induction_on s ⟨0, 1, form_one, by simp, fun x hx => by simp at hx⟩ ?_
  intro x s _ ih
  obtain ⟨b, H, hH, hH0, hg⟩ := ih
  obtain ⟨d, g, h, hgd, hhd, hh0, hgh⟩ := hy x
  refine ⟨b + d, H * h, form_mul hH hhd, by rw [map_mul]; exact mul_ne_zero hH0 hh0, fun z hz => ?_⟩
  rcases Finset.mem_insert.1 hz with rfl | hz
  · exact ⟨H * g, form_mul hH hgd, by rw [map_mul, map_mul, hgh]; ring⟩
  · obtain ⟨g', hg', hg'e⟩ := hg z hz
    exact ⟨g' * h, form_mul hg' hhd, by rw [map_mul, map_mul, hg'e]; ring⟩

theorem lift_poly {y : (Σ k, ι k) → Ω} {b : K → ℕ} {H : MRing ι} (P : Polynomial Ω)
    (hP : ∀ j, j ∈ P.support → ∃ g : MRing ι, IsMultiHomog g b ∧ aeval y g = P.coeff j * aeval y H) :
    ∃ L : Polynomial (MRing ι), (∀ j, IsMultiHomog (L.coeff j) b) ∧
      L.map (aeval y : MRing ι →ₐ[ℤ] Ω).toRingHom = Polynomial.C (aeval y H) * P := by
  classical
  choose! g hg using hP
  refine ⟨∑ j ∈ P.support, Polynomial.monomial j (g j), fun j => ?_, ?_⟩
  · rw [Polynomial.finsetSum_coeff]
    simp only [Polynomial.coeff_monomial, Finset.sum_ite_eq']
    split_ifs with hj
    · exact (hg j hj).1
    · exact form_zero b
  · ext n
    simp only [Polynomial.coeff_map, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial,
      Finset.sum_ite_eq', Polynomial.coeff_C_mul]
    split_ifs with hn
    · exact ((hg n hn).2).trans (mul_comm _ _)
    · have hc : P.coeff n = 0 := by simpa using hn
      rw [map_zero, hc, mul_zero]

theorem sum_derivative (q : Polynomial ℂ) (n : ℕ) (hn : q.natDegree ≤ n) (τ : ℂ) :
    ∑ j ∈ Finset.range (n + 1), (j : ℂ) * q.coeff j * τ ^ (j - 1) = (Polynomial.derivative q).eval τ := by
  rw [Polynomial.derivative_eval, Polynomial.sum_over_range' _ (fun _ => by simp) (n + 1) (Nat.lt_succ_of_le hn)]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem sum_eval (q : Polynomial ℂ) (n : ℕ) (hn : q.natDegree ≤ n) (τ : ℂ) :
    ∑ j ∈ Finset.range (n + 1), q.coeff j * τ ^ j = q.eval τ := by
  exact (Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hn) τ).symm

def evalAt (w : (Σ k, ι k) → ℂ) : MRing ι →+* ℂ :=
  (MvPolynomial.eval w).comp (MvPolynomial.map (Int.castRingHom ℂ))

theorem evalAt_apply (w : (Σ k, ι k) → ℂ) (f : MRing ι) :
    evalAt w f = eval w (map (Int.castRingHom ℂ) f) := rfl

theorem core {Ω' : Type} [Field Ω'] {y : (Σ k, ι k) → Ω} (hy : Birational y) (i : Ω →+* Ω') (α : Ω')
    (m : Polynomial Ω) (hsep : IsCoprime m (Polynomial.derivative m)) (hroot : Polynomial.eval₂ i α m = 0) :
    ∃ (n : ℕ) (c : ℕ → MRing ι) (a : K → ℕ) (G : MRing ι) (b : K → ℕ),
      (∀ j, IsMultiHomog (c j) a) ∧ IsMultiHomog G b ∧ G ∉ mCoordIdeal y ∧
      (∑ j ∈ Finset.range (n + 1), i (aeval y (c j)) * α ^ j = 0) ∧
      ∀ w ∈ mcPts (mCoordIdeal y), eval w (map (Int.castRingHom ℂ) G) ≠ 0 → ∀ τ : ℂ,
        ∑ j ∈ Finset.range (n + 1), eval w (map (Int.castRingHom ℂ) (c j)) * τ ^ j = 0 →
        ∑ j ∈ Finset.range (n + 1), (j : ℂ) * eval w (map (Int.castRingHom ℂ) (c j)) * τ ^ (j - 1) ≠ 0 := by
  classical
  obtain ⟨u, v, huv⟩ := hsep
  obtain ⟨b, H, hH, hH0, hg⟩ := common_denominator hy
    (m.support.image m.coeff ∪ u.support.image u.coeff ∪ v.support.image v.coeff)
  obtain ⟨M, hMh, hMm⟩ := lift_poly (y := y) (H := H) m (fun j hj => hg _
    (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hj))))
  obtain ⟨U, hUh, hUm⟩ := lift_poly (y := y) (H := H) u (fun j hj => hg _
    (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hj))))
  obtain ⟨V, hVh, hVm⟩ := lift_poly (y := y) (H := H) v (fun j hj => hg _
    (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hj)))
  have hDh : ∀ j, IsMultiHomog ((Polynomial.derivative M).coeff j) b := fun j => by
    rw [Polynomial.coeff_derivative]
    exact_mod_cast form_natCast_mul (hMh (j + 1)) (j + 1)
  have hEh : ∀ j, IsMultiHomog ((U * M + V * Polynomial.derivative M - Polynomial.C (H * H)).coeff j)
      (b + b) := by
    intro j
    rw [Polynomial.coeff_sub, Polynomial.coeff_add, Polynomial.coeff_mul, Polynomial.coeff_mul,
      Polynomial.coeff_C]
    refine form_sub (form_add (form_sum _ _ fun x _ => form_mul (hUh _) (hMh _))
      (form_sum _ _ fun x _ => form_mul (hVh _) (hDh _))) ?_
    split_ifs
    · exact form_mul hH hH
    · exact form_zero _
  have hEm : (U * M + V * Polynomial.derivative M - Polynomial.C (H * H)).map
      (aeval y : MRing ι →ₐ[ℤ] Ω).toRingHom = 0 := by
    rw [Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul,
      ← Polynomial.derivative_map, Polynomial.map_C, hUm, hVm, hMm, Polynomial.derivative_C_mul]
    simp only [map_mul, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    linear_combination (Polynomial.C (aeval y H) * Polynomial.C (aeval y H)) * huv
  have hEmem : ∀ j, (U * M + V * Polynomial.derivative M - Polynomial.C (H * H)).coeff j ∈
      mCoordIdeal y := by
    intro j
    refine mem_of_aeval_eq_zero (hEh j) ?_
    have h2 := congrArg (fun p => Polynomial.coeff p j) hEm
    simp only [Polynomial.coeff_map, Polynomial.coeff_zero] at h2
    exact h2
  refine ⟨M.natDegree, fun j => M.coeff j, b, H, b, hMh, hH, notMem_of_aeval_ne_zero hH hH0, ?_, ?_⟩
  · have hdeg : (M.map (aeval y : MRing ι →ₐ[ℤ] Ω).toRingHom).natDegree < M.natDegree + 1 :=
      Nat.lt_succ_of_le Polynomial.natDegree_map_le
    have h1 := Polynomial.eval₂_eq_sum_range' i hdeg α
    simp only [Polynomial.coeff_map] at h1
    rw [hMm, Polynomial.eval₂_mul, Polynomial.eval₂_C, hroot, mul_zero] at h1
    exact h1.symm
  · intro w hw hG τ hτ hder
    have key : ∀ j, eval w (map (Int.castRingHom ℂ)
        ((U * M + V * Polynomial.derivative M - Polynomial.C (H * H)).coeff j)) = 0 :=
      fun j => hw.2 _ (hEmem j)
    have hE0 : (U * M + V * Polynomial.derivative M - Polynomial.C (H * H)).map (evalAt w) = 0 := by
      ext j
      rw [Polynomial.coeff_map, Polynomial.coeff_zero, evalAt_apply]
      exact key j
    rw [Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul,
      ← Polynomial.derivative_map, Polynomial.map_C] at hE0
    have hMe : (M.map (evalAt w)).eval τ = 0 := by
      rw [← sum_eval (M.map (evalAt w)) M.natDegree Polynomial.natDegree_map_le τ]
      simpa only [Polynomial.coeff_map, evalAt_apply] using hτ
    have hDe : (Polynomial.derivative (M.map (evalAt w))).eval τ = 0 := by
      rw [← sum_derivative (M.map (evalAt w)) M.natDegree Polynomial.natDegree_map_le τ]
      simpa only [Polynomial.coeff_map, evalAt_apply] using hder
    have h3 := congrArg (Polynomial.eval τ) hE0
    simp only [Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, hMe,
      hDe, mul_zero, add_zero, zero_sub, Polynomial.eval_zero, neg_eq_zero, map_mul] at h3
    have hGH : evalAt w H ≠ 0 := by
      rw [evalAt_apply]
      exact hG
    exact hGH (mul_self_eq_zero.1 h3)

theorem algebraic_form_poly : ∀ (K₀ : Type) [Fintype K₀] (J₀ : K₀ → Type) [∀ k, Fintype (J₀ k)] (Ω₀ Ω : Type)
    [Field Ω₀] [Field Ω] [CharZero Ω] (y₀ : (Σ k, J₀ k) → Ω₀) (i : Ω₀ →+* Ω) (α : Ω), Birational y₀ →
    (letI := i.toAlgebra; IsAlgebraic Ω₀ α) →
    ∃ (n : ℕ) (c : ℕ → MRing J₀) (a : K₀ → ℕ) (G : MRing J₀) (b : K₀ → ℕ),
      (∀ j, IsMultiHomog (c j) a) ∧ IsMultiHomog G b ∧ G ∉ mCoordIdeal y₀ ∧
      (∑ j ∈ Finset.range (n + 1), i (aeval y₀ (c j)) * α ^ j = 0) ∧
      ∀ w ∈ mcPts (mCoordIdeal y₀), eval w (map (Int.castRingHom ℂ) G) ≠ 0 → ∀ τ : ℂ,
        ∑ j ∈ Finset.range (n + 1), eval w (map (Int.castRingHom ℂ) (c j)) * τ ^ j = 0 →
        ∑ j ∈ Finset.range (n + 1), (j : ℂ) * eval w (map (Int.castRingHom ℂ) (c j)) * τ ^ (j - 1) ≠ 0 := by
  intro K₀ _ J₀ _ Ω₀ Ω _ _ _ y₀ i α hy hα
  letI := i.toAlgebra
  haveI : CharZero Ω₀ := RingHom.charZero i
  have hα' : IsAlgebraic Ω₀ α := hα
  have hint : IsIntegral Ω₀ α := hα'.isIntegral
  have hsep : (minpoly Ω₀ α).Separable := (minpoly.irreducible hint).separable
  have hroot : Polynomial.eval₂ i α (minpoly Ω₀ α) = 0 := by
    have h := minpoly.aeval Ω₀ α
    rwa [Polynomial.aeval_def, RingHom.algebraMap_toAlgebra] at h
  exact core hy i α (minpoly Ω₀ α) hsep hroot

end GlobalTheory.CompanionTheory.Ar.AlgPoly
