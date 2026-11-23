import Development.AbelianVarietyTheory.Definitions.ThetaValues.LetAct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.WeightOrderLemmas

open MvPolynomial
open scoped MonomialOrder

section Order

variable {σ : Type}

def WSyn (_ : σ → ℕ) : Type := σ →₀ ℕ

theorem exists_order [Finite σ] (w : σ → ℕ) :
    ∃ m : MonomialOrder.{0,0} σ, ∀ c d : σ →₀ ℕ, Finsupp.weight w c < Finsupp.weight w d → c ≺[m] d := by
  classical
  letI : LinearOrder σ := LinearOrder.lift' (Finite.equivFin σ) (Finite.equivFin σ).injective
  let key : (σ →₀ ℕ) → ℕ ×ₗ Lex (σ →₀ ℕ) := fun c => toLex (Finsupp.weight w c, toLex c)
  have hinj : Function.Injective key := by
    intro a b h
    have := congrArg (fun x => ofLex (ofLex x).2) h
    simpa [key] using this
  have hadd : ∀ a b, key (a + b) = key a + key b := by
    intro a b
    simp only [key, map_add]
    rfl
  letI : AddCommMonoid (WSyn w) := inferInstanceAs (AddCommMonoid (σ →₀ ℕ))
  letI lo : LinearOrder (WSyn w) := LinearOrder.lift' key hinj
  have hle : ∀ a b : WSyn w, a ≤ b ↔ key a ≤ key b := fun _ _ => Iff.rfl
  have hlt : ∀ a b : WSyn w, a < b ↔ key a < key b := fun _ _ => Iff.rfl
  refine ⟨{ syn := WSyn w
            isOrderedAddMonoid_syn := ⟨fun a b h c => ?_, fun a b h c => ?_⟩
            toSyn := AddEquiv.refl _
            toSyn_monotone := fun a b h => ?_
            wellFoundedLT_syn := ⟨?_⟩ }, ?_⟩
  · rw [hle] at h ⊢
    erw [hadd, hadd]
    gcongr
  · rw [hle] at h ⊢
    erw [hadd, hadd]
    gcongr
  · change key a ≤ key b
    simp only [key, Prod.Lex.toLex_le_toLex]
    obtain ⟨c, rfl⟩ := exists_add_of_le h
    rcases Nat.eq_zero_or_pos (Finsupp.weight w c) with h0 | h0
    · right
      exact ⟨by erw [map_add, h0, add_zero], Finsupp.toLex_monotone h⟩
    · left
      erw [map_add]; omega
  · exact InvImage.wf key wellFounded_lt
  · intro c d h
    change key c < key d
    simp only [key, Prod.Lex.toLex_lt_toLex]
    exact Or.inl h

variable {K : Type} [Field K] (m : MonomialOrder.{0,0} σ)

theorem le_of_le_add_disj {a s d : σ →₀ ℕ} (h : a ≤ s + d) (hd : ∀ v, a v = 0 ∨ d v = 0) : a ≤ s := by
  intro v
  have := h v
  rcases hd v with h1 | h1
  · simp [h1]
  · simpa [h1] using this

theorem div_ideal {ι : Type} (f : ι → MvPolynomial σ K) (hf : ∀ i, f i ≠ 0) (S : Set ι) (g : MvPolynomial σ K) :
    ∃ s, g - s ∈ Ideal.span (f '' S) ∧ (s ≠ 0 → ∀ i ∈ S, ¬ m.degree (f i) ≤ m.degree s) := by
  obtain ⟨q, r, h1, -, h3⟩ := m.div (b := fun i : S => f i)
    (fun i => isUnit_iff_ne_zero.2 (by simpa using hf i)) g
  refine ⟨r, ?_, fun hr i hi => h3 _ (m.degree_mem_support hr) ⟨i, hi⟩⟩
  rw [h1, add_sub_cancel_right, Finsupp.linearCombination_apply, Finsupp.sum]
  refine Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, i.2, rfl⟩)

theorem groebner {ι : Type} (f : ι → MvPolynomial σ K) (hf : ∀ i, f i ≠ 0)
    (hd : ∀ i j, i ≠ j → ∀ v, m.degree (f i) v = 0 ∨ m.degree (f j) v = 0) (S : Finset ι) :
    ∀ h ∈ Ideal.span (f '' S), h ≠ 0 → ∃ i ∈ S, m.degree (f i) ≤ m.degree h := by
  classical
  induction S using Finset.induction_on with
  | empty => intro h hh h0; simp at hh; exact absurd hh h0
  | insert k S hk ih =>
    intro h hh h0
    rw [Finset.coe_insert, Set.image_insert_eq, Ideal.mem_span_insert] at hh
    obtain ⟨g, z, hz, rfl⟩ := hh
    obtain ⟨s, hs1, hs2⟩ := div_ideal m f hf S g
    have e : g * f k + z = s * f k + ((g - s) * f k + z) := by ring
    have hz' : (g - s) * f k + z ∈ Ideal.span (f '' S) := add_mem (Ideal.mul_mem_right _ _ hs1) hz
    rw [e] at h0 ⊢
    generalize (g - s) * f k + z = y at *
    by_cases hs : s = 0
    · subst hs
      simp only [zero_mul, zero_add] at h0 ⊢
      obtain ⟨i, hi, hi'⟩ := ih y hz' h0
      exact ⟨i, Finset.mem_insert_of_mem hi, hi'⟩
    have hdeg : m.degree (s * f k) = m.degree s + m.degree (f k) := m.degree_mul hs (hf k)
    by_cases hy : y = 0
    · subst hy
      exact ⟨k, Finset.mem_insert_self _ _, by rw [add_zero, hdeg]; exact le_add_self⟩
    obtain ⟨i, hi, hi'⟩ := ih y hz' hy
    rcases lt_trichotomy (m.toSyn (m.degree y)) (m.toSyn (m.degree (s * f k))) with h1 | h1 | h1
    · exact ⟨k, Finset.mem_insert_self _ _, by rw [m.degree_add_of_lt h1, hdeg]; exact le_add_self⟩
    · exfalso
      rw [m.toSyn.injective h1, hdeg] at hi'
      exact hs2 hs i hi (le_of_le_add_disj hi' (hd i k (by rintro rfl; exact hk hi)))
    · exact ⟨i, Finset.mem_insert_of_mem hi, by rw [add_comm, m.degree_add_of_lt h1]; exact hi'⟩

theorem nzd_of_groebner {ι : Type} [Finite ι] (f : ι → MvPolynomial σ K) (hf : ∀ i, f i ≠ 0)
    (hd : ∀ i j, i ≠ j → ∀ v, m.degree (f i) v = 0 ∨ m.degree (f j) v = 0)
    (D : MvPolynomial σ K) (hD : D ≠ 0) (hD' : ∀ i v, m.degree (f i) v = 0 ∨ m.degree D v = 0)
    (g : MvPolynomial σ K) (hg : D * g ∈ Ideal.span (Set.range f)) : g ∈ Ideal.span (Set.range f) := by
  haveI := Fintype.ofFinite ι
  have e : Set.range f = f '' ((Finset.univ : Finset ι) : Set ι) := by simp
  rw [e] at hg ⊢
  obtain ⟨s, hs1, hs2⟩ := div_ideal m f hf ((Finset.univ : Finset ι) : Set ι) g
  by_cases hs : s = 0
  · simpa [hs] using hs1
  exfalso
  have h1 : s * D ∈ Ideal.span (f '' ((Finset.univ : Finset ι) : Set ι)) := by
    have : s * D = D * g - D * (g - s) := by ring
    rw [this]
    exact sub_mem hg (Ideal.mul_mem_left _ _ hs1)
  obtain ⟨i, hi, hi'⟩ := groebner m f hf hd _ _ h1 (mul_ne_zero hs hD)
  rw [m.degree_mul hs hD] at hi'
  exact hs2 hs i (by simp) (le_of_le_add_disj hi' (hD' i))

theorem degree_sum_monomial {κ : Type} [Fintype κ] (w : σ → ℕ)
    (hm : ∀ c d : σ →₀ ℕ, Finsupp.weight w c < Finsupp.weight w d → c ≺[m] d)
    (e : κ → σ →₀ ℕ) (c : κ → K) (k0 : κ) (h0 : c k0 ≠ 0)
    (h : ∀ k, k ≠ k0 → c k ≠ 0 → Finsupp.weight w (e k) < Finsupp.weight w (e k0)) :
    (∑ k, monomial (e k) (c k)) ≠ 0 ∧ m.degree (∑ k, monomial (e k) (c k)) = e k0 := by
  classical
  have hc : coeff (e k0) (∑ k, monomial (e k) (c k)) = c k0 := by
    rw [coeff_sum, Finset.sum_eq_single k0]
    · simp
    · intro k _ hk
      rw [coeff_monomial]
      split_ifs with h1
      · by_contra h2
        have := h k hk h2
        rw [h1] at this
        exact lt_irrefl _ this
      · rfl
    · simp
  refine ⟨fun hz => h0 (by rw [← hc, hz]; simp), ?_⟩
  apply m.toSyn.injective
  apply le_antisymm
  · rw [m.degree_le_iff]
    intro d hd
    rw [mem_support_iff, coeff_sum] at hd
    obtain ⟨k, -, hk⟩ := Finset.exists_ne_zero_of_sum_ne_zero hd
    rw [coeff_monomial] at hk
    split_ifs at hk with h1
    · subst h1
      by_cases hkk : k = k0
      · rw [hkk]
      · exact (hm _ _ (h k hkk hk)).le
    · exact absurd rfl hk
  · apply m.le_degree
    rw [mem_support_iff, hc]; exact h0

end Order

section Fock

variable {σ : Type} [Fintype σ] {K : Type} [Field K]

def fac (m : σ →₀ ℕ) : ℕ := ∏ v, (m v).factorial

theorem fac_pos (m : σ →₀ ℕ) : 0 < fac m := Finset.prod_pos fun _ _ => Nat.factorial_pos _

theorem fac_add (m : σ →₀ ℕ) (v : σ) : fac (m + Finsupp.single v 1) = fac m * (m v + 1) := by
  classical
  unfold fac
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ v), ← Finset.mul_prod_erase _ (fun u => (m u).factorial) (Finset.mem_univ v)]
  rw [Finset.prod_congr rfl (g := fun u => (m u).factorial)]
  · simp [Nat.factorial_succ]; ring
  · intro u hu
    simp [Finsupp.single_eq_of_ne (Finset.ne_of_mem_erase hu)]

def fock (σ K : Type) [Fintype σ] [Field K] : LinearMap.BilinForm K (MvPolynomial σ K) :=
  (basisMonomials σ K).constr K fun m => (fac m : K) • lcoeff K m

theorem fock_monomial (m : σ →₀ ℕ) (c : K) (g : MvPolynomial σ K) :
    fock σ K (monomial m c) g = c * (fac m * coeff m g) := by
  have : (monomial m c : MvPolynomial σ K) = c • basisMonomials σ K m := by
    simp [smul_monomial]
  rw [this, map_smul, fock, Module.Basis.constr_basis]
  simp

theorem fock_eq (f g : MvPolynomial σ K) :
    fock σ K f g = ∑ m ∈ f.support, coeff m f * (fac m * coeff m g) := by
  conv_lhs => rw [f.as_sum]
  rw [map_sum, LinearMap.sum_apply]
  simp only [fock_monomial]

theorem fock_symm (f g : MvPolynomial σ K) : fock σ K f g = fock σ K g f := by
  classical
  induction f using MvPolynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | monomial m c =>
    induction g using MvPolynomial.induction_on' with
    | add p q hp hq => simp [hp, hq]
    | monomial m' c' =>
      simp only [fock_monomial, coeff_monomial]
      by_cases h : m = m'
      · subst h; simp; ring
      · simp [h, Ne.symm h]

theorem fock_X_mul (v : σ) (f g : MvPolynomial σ K) :
    fock σ K (X v * f) g = fock σ K f (pderiv v g) := by
  induction f using MvPolynomial.induction_on' with
  | add p q hp hq => simp [mul_add, hp, hq]
  | monomial m c =>
    rw [mul_comm, X, monomial_mul, fock_monomial, fock_monomial, coeff_pderiv, fac_add]
    push_cast; ring

theorem eq_zero_of_fock [CharZero K] (g : MvPolynomial σ K) (h : ∀ m, fock σ K (monomial m 1) g = 0) : g = 0 := by
  ext m
  have := h m
  rw [fock_monomial, one_mul, mul_eq_zero] at this
  rcases this with h1 | h1
  · exact absurd h1 (Nat.cast_ne_zero.2 (fac_pos m).ne')
  · simpa using h1

theorem eq_zero_of_fock_conj (g : MvPolynomial σ ℂ) (h : fock σ ℂ g (map (starRingEnd ℂ) g) = 0) : g = 0 := by
  rw [fock_eq] at h
  have e : ∀ m, coeff m g * (fac m * coeff m (map (starRingEnd ℂ) g)) =
      ((Complex.normSq (coeff m g) * fac m : ℝ) : ℂ) := by
    intro m
    rw [coeff_map]
    push_cast
    rw [← Complex.mul_conj]; ring
  simp only [e] at h
  rw [← Complex.ofReal_sum, Complex.ofReal_eq_zero, Finset.sum_eq_zero_iff_of_nonneg
    (fun m _ => mul_nonneg (Complex.normSq_nonneg _) (Nat.cast_nonneg _))] at h
  ext m
  by_cases hm : m ∈ g.support
  · have := h m hm
    rw [mul_eq_zero] at this
    rcases this with h1 | h1
    · simpa using h1
    · exact absurd h1 (Nat.cast_ne_zero.2 (fac_pos m).ne')
  · simpa using hm

end Fock

section Scale

variable {σ ρ : Type} [Fintype ρ] [DecidableEq ρ] {K : Type} [Field K]

abbrev Deg (w : σ → ρ) (a : ρ → ℕ) (P : MvPolynomial σ K) : Prop :=
  IsWeightedHomogeneous (fun v => (Pi.single (w v) 1 : ρ → ℕ)) P a

theorem prod_pow_weight {A : Type} [CommRing A] (w : σ → ρ) (t : ρ → A) (m : σ →₀ ℕ) :
    m.prod (fun v e => t (w v) ^ e) = ∏ r, t r ^ (Finsupp.weight (fun v => (Pi.single (w v) 1 : ρ → ℕ)) m r) := by
  induction m using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
    rw [Finsupp.prod_add_index' (by simp) (by simp [pow_add]), hf, hg, map_add, ← Finset.prod_mul_distrib]
    simp [pow_add]
  | single v e =>
    rw [Finsupp.prod_single_index (by simp), Finsupp.weight_single, Finset.prod_eq_single (w v)]
    · simp
    · intro r _ hr
      simp [Pi.single_eq_of_ne hr]
    · simp

theorem aeval_scale_monomial {A : Type} [CommRing A] [Algebra K A] (w : σ → ρ) (t : ρ → A) (x : σ → A)
    (m : σ →₀ ℕ) (c : K) :
    aeval (fun v => t (w v) * x v) (monomial m c) =
      (∏ r, t r ^ (Finsupp.weight (fun v => (Pi.single (w v) 1 : ρ → ℕ)) m r)) * aeval x (monomial m c) := by
  rw [aeval_monomial, aeval_monomial, ← prod_pow_weight]
  simp only [mul_pow, Finsupp.prod_mul]
  ring

theorem aeval_scale {A : Type} [CommRing A] [Algebra K A] {w : σ → ρ} {a : ρ → ℕ} {P : MvPolynomial σ K}
    (hP : Deg w a P) (t : ρ → A) (x : σ → A) :
    aeval (fun v => t (w v) * x v) P = (∏ r, t r ^ a r) * aeval x P := by
  conv_lhs => rw [P.as_sum]
  conv_rhs => rw [P.as_sum]
  rw [map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [aeval_scale_monomial, hP (mem_support_iff.1 hm)]

theorem coeff_scale (w : σ → ρ) (t : ρ → K) (m : σ →₀ ℕ) (P : MvPolynomial σ K) :
    coeff m (aeval (fun v => (C (t (w v)) * X v : MvPolynomial σ K)) P) =
      (∏ r, t r ^ (Finsupp.weight (fun v => (Pi.single (w v) 1 : ρ → ℕ)) m r)) * coeff m P := by
  classical
  induction P using MvPolynomial.induction_on' with
  | add p q hp hq => simp only [map_add, coeff_add, hp, hq, mul_add]
  | monomial m' c =>
    rw [aeval_scale_monomial w (fun r => (C (t r) : MvPolynomial σ K)), aeval_X_left_apply]
    simp only [← C_pow, ← map_prod, coeff_C_mul, coeff_monomial]
    split_ifs with h
    · rw [h]
    · simp

theorem deg_of_scale [CharZero K] {w : σ → ρ} {a : ρ → ℕ} {P : MvPolynomial σ K}
    (h : ∀ t : ρ → K, (∀ r, t r ≠ 0) → aeval (fun v => C (t (w v)) * X v) P = C (∏ r, t r ^ a r) * P) : Deg w a P := by
  classical
  intro m hm
  funext r
  have h1 := congrArg (coeff m) (h (fun s => if s = r then 2 else 1) (fun s => by split_ifs <;> simp))
  rw [coeff_scale w (fun s => if s = r then (2 : K) else 1), coeff_C_mul] at h1
  have h2 := mul_right_cancel₀ hm h1
  have h3 : ∀ u : ρ → ℕ, ∏ s, (if s = r then (2 : K) else 1) ^ u s = 2 ^ u r := by
    intro u
    rw [Finset.prod_eq_single r]
    · simp
    · intro s _ hs; simp [hs]
    · simp
  rw [h3, h3] at h2
  have h4 : (2 : ℕ) ^ (Finsupp.weight (fun v => (Pi.single (w v) 1 : ρ → ℕ)) m r) = 2 ^ a r := by exact_mod_cast h2
  exact Nat.pow_right_injective le_rfl h4

theorem weight_apply [Fintype σ] (w : σ → ρ) (m : σ →₀ ℕ) (r : ρ) :
    Finsupp.weight (fun v => (Pi.single (w v) 1 : ρ → ℕ)) m r = ∑ v, if w v = r then m v else 0 := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finset.sum_apply]
  refine Finset.sum_congr rfl fun v _ => ?_
  simp [Pi.single_apply, eq_comm]

theorem finite_deg [Fintype σ] (w : σ → ρ) (a : ρ → ℕ) :
    Module.Finite K (weightedHomogeneousSubmodule K (fun v => (Pi.single (w v) 1 : ρ → ℕ)) a) := by
  refine Submodule.finiteDimensional_of_le (S₂ := restrictTotalDegree σ K (∑ r, a r)) ?_
  intro P hP
  rw [mem_restrictTotalDegree, totalDegree, Finset.sup_le_iff]
  intro m hm
  have h := hP (mem_support_iff.1 hm)
  rw [← h, Finsupp.sum_fintype _ _ (by simp)]
  simp only [weight_apply]
  rw [Finset.sum_comm]
  simp

end Scale

section Harm

variable {σ ι κ : Type} [Fintype σ] [Fintype ι] [Fintype κ] (x y : ι → κ → σ)

def qf (K : Type) [Field K] (i : ι) : MvPolynomial σ K := ∑ b, X (x i b) * X (y i b)

def lp {K : Type} [Field K] (i : ι) (P : MvPolynomial σ K) : MvPolynomial σ K :=
  ∑ b, pderiv (x i b) (pderiv (y i b) P)

variable {K : Type} [Field K]

theorem fock_qf (i : ι) (f g : MvPolynomial σ K) : fock σ K (f * qf x y K i) g = fock σ K f (lp x y i g) := by
  unfold qf lp
  rw [Finset.mul_sum, map_sum, LinearMap.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← fock_X_mul, ← fock_X_mul]
  congr 2; ring

theorem fock_ideal {f h : MvPolynomial σ K} (hf : f ∈ Ideal.span (Set.range (qf x y K)))
    (hh : ∀ i, lp x y i h = 0) : fock σ K f h = 0 := by
  obtain ⟨c, rfl⟩ := Ideal.mem_span_range_iff_exists_fun.1 hf
  rw [map_sum, LinearMap.sum_apply]
  exact Finset.sum_eq_zero fun i _ => by rw [fock_qf, hh, map_zero]

theorem harm_ideal_zero (φ : K →+* ℂ) {h : MvPolynomial σ K} (hf : h ∈ Ideal.span (Set.range (qf x y K)))
    (hh : ∀ i, lp x y i h = 0) : h = 0 := by
  apply map_injective φ φ.injective
  rw [map_zero]
  apply eq_zero_of_fock_conj
  apply fock_ideal x y
  · obtain ⟨c, rfl⟩ := Ideal.mem_span_range_iff_exists_fun.1 hf
    rw [map_sum]
    refine Ideal.sum_mem _ fun i _ => ?_
    rw [map_mul]
    refine Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, ?_⟩)
    simp [qf]
  · intro i
    have := congrArg (fun P => map (starRingEnd ℂ) (map φ P)) (hh i)
    simpa [lp, pderiv_map] using this

theorem exists_harm (φ : K →+* ℂ) {ρ : Type} [Fintype ρ] [DecidableEq ρ] (w : σ → ρ) (wx wy : ι → ρ)
    (hx : ∀ i b, w (x i b) = wx i) (hy : ∀ i b, w (y i b) = wy i) {a : ρ → ℕ} {P : MvPolynomial σ K}
    (hP : Deg w a P) : ∃ h, Deg w a h ∧ (∀ i, lp x y i h = 0) ∧ P - h ∈ Ideal.span (Set.range (qf x y K)) := by
  haveI : CharZero K := φ.charZero
  let V := weightedHomogeneousSubmodule K (fun v => (Pi.single (w v) 1 : ρ → ℕ)) a
  haveI : Module.Finite K V := finite_deg w a
  let B : LinearMap.BilinForm K V := (fock σ K).restrict V
  have hB : B.IsRefl := fun u v h => by
    have h' : fock σ K u v = 0 := h
    show fock σ K v u = 0
    rw [fock_symm, h']
  let W : Submodule K V := ((Ideal.span (Set.range (qf x y K))).restrictScalars K).comap V.subtype
  have hH : ∀ h ∈ B.orthogonal W, ∀ i, lp x y i (h : MvPolynomial σ K) = 0 := by
    intro h hh i
    apply eq_zero_of_fock
    intro m
    rw [← fock_qf]
    have hd : Deg w (Finsupp.weight (fun v => (Pi.single (w v) 1 : ρ → ℕ)) m + (Pi.single (wx i) 1 + Pi.single (wy i) 1))
        (monomial m (1 : K) * qf x y K i) := by
      refine IsWeightedHomogeneous.mul (isWeightedHomogeneous_monomial _ _ _ rfl) ?_
      refine IsWeightedHomogeneous.sum _ _ _ fun b _ => ?_
      rw [← hx i b, ← hy i b]
      exact (isWeightedHomogeneous_X _ _ _).mul (isWeightedHomogeneous_X _ _ _)
    by_cases ha : Finsupp.weight (fun v => (Pi.single (w v) 1 : ρ → ℕ)) m + (Pi.single (wx i) 1 + Pi.single (wy i) 1) = a
    · rw [ha] at hd
      have hI : monomial m (1 : K) * qf x y K i ∈ Ideal.span (Set.range (qf x y K)) :=
        Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)
      exact hh ⟨_, hd⟩ hI
    · rw [fock_eq]
      refine Finset.sum_eq_zero fun d hd' => ?_
      have h1 := hd (mem_support_iff.1 hd')
      have h2 : coeff d (h : MvPolynomial σ K) = 0 := by
        by_contra h3
        exact ha (h1.symm.trans (h.2 h3))
      simp [h2]
  have hc : IsCompl W (B.orthogonal W) := by
    rw [LinearMap.BilinForm.isCompl_orthogonal_iff_disjoint hB, Submodule.disjoint_def]
    intro h h1 h2
    exact Subtype.ext (harm_ideal_zero x y φ h1 (hH h h2))
  have : (⟨P, hP⟩ : V) ∈ W ⊔ B.orthogonal W := by rw [hc.sup_eq_top]; trivial
  obtain ⟨u, hu, h, hh, e⟩ := Submodule.mem_sup.1 this
  refine ⟨h, h.2, hH h hh, ?_⟩
  have e' : (u : MvPolynomial σ K) + h = P := congrArg Subtype.val e
  rw [← e', add_sub_cancel_right]
  exact hu

end Harm

section Tensor

open Formalism.GradedWeylDivisibility

variable {K : Type} [Field K] {S : Type} [Fintype S] [DecidableEq S] {n : ℕ}

def part (m : S × (Fin n × Fin n) →₀ ℕ) (s : S) : Fin n × Fin n →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun v => m (s, v)

theorem prod_emb_monomial (e : S → Fin n × Fin n →₀ ℕ) :
    ∏ s, blockEmb K s (monomial (e s) (1 : K)) =
      monomial (Finsupp.equivFunOnFinite.symm fun v : S × (Fin n × Fin n) => e v.1 v.2) 1 := by
  simp only [blockEmb, rename_monomial]
  rw [← monomial_sum_one]
  congr 2
  ext ⟨s, v⟩
  simp only [Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.equivFunOnFinite_symm_apply_apply]
  rw [Finset.sum_eq_single s]
  · exact Finsupp.mapDomain_apply (fun a b h => (Prod.ext_iff.1 h).2) _ _
  · intro t _ ht
    apply Finsupp.mapDomain_notin_range
    rintro ⟨u, hu⟩
    exact ht (Prod.ext_iff.1 hu).1
  · simp

theorem monomial_eq_prod (m : S × (Fin n × Fin n) →₀ ℕ) :
    monomial m (1 : K) = ∏ s, blockEmb K s (monomial (part m s) (1 : K)) := by
  rw [prod_emb_monomial]
  congr 2
  ext v
  simp [part]

def tens (φ : S → Module.End K (MvPolynomial (Fin n × Fin n) K)) :
    Module.End K (MvPolynomial (S × (Fin n × Fin n)) K) :=
  (basisMonomials _ K).constr K fun m => ∏ s, blockEmb K s (φ s (monomial (part m s) 1))

theorem tens_monomial (φ : S → Module.End K (MvPolynomial (Fin n × Fin n) K)) (m : S × (Fin n × Fin n) →₀ ℕ) :
    tens φ (monomial m 1) = ∏ s, blockEmb K s (φ s (monomial (part m s) 1)) := by
  have := (basisMonomials (S × (Fin n × Fin n)) K).constr_basis K
    (fun m => ∏ s, blockEmb K s (φ s (monomial (part m s) 1))) m
  simpa [tens] using this

theorem tens_prod (φ : S → Module.End K (MvPolynomial (Fin n × Fin n) K)) (f : S → MvPolynomial (Fin n × Fin n) K) :
    tens φ (∏ s, blockEmb K s (f s)) = ∏ s, blockEmb K s (φ s (f s)) := by
  have : (tens φ).compMultilinearMap ((MultilinearMap.mkPiAlgebra K S _).compLinearMap
        fun s => (blockEmb K s).toLinearMap) =
      (MultilinearMap.mkPiAlgebra K S _).compLinearMap fun s => (blockEmb K s).toLinearMap ∘ₗ φ s := by
    refine Module.Basis.ext_multilinear (fun _ => basisMonomials _ K) fun e => ?_
    simp only [LinearMap.compMultilinearMap_apply, MultilinearMap.compLinearMap_apply,
      MultilinearMap.mkPiAlgebra_apply, coe_basisMonomials, AlgHom.toLinearMap_apply, LinearMap.comp_apply]
    rw [prod_emb_monomial, tens_monomial]
    refine Finset.prod_congr rfl fun s _ => ?_
    congr 3
    ext v
    simp [part]
  simpa using congrArg (fun F => F f) this

theorem lin_ext {M : Type} [AddCommGroup M] [Module K M] (F G : MvPolynomial (S × (Fin n × Fin n)) K →ₗ[K] M)
    (h : ∀ f : S → MvPolynomial (Fin n × Fin n) K, F (∏ s, blockEmb K s (f s)) = G (∏ s, blockEmb K s (f s))) :
    F = G := by
  refine (basisMonomials _ K).ext fun m => ?_
  simp only [coe_basisMonomials]
  rw [monomial_eq_prod, h]

def pev (t : S) (z : S × (Fin n × Fin n) → K) :
    MvPolynomial (S × (Fin n × Fin n)) K →ₐ[K] MvPolynomial (Fin n × Fin n) K :=
  aeval fun v => if v.1 = t then X v.2 else C (z v)

theorem pev_self (t : S) (z : S × (Fin n × Fin n) → K) (f : MvPolynomial (Fin n × Fin n) K) :
    pev t z (blockEmb K t f) = f := by
  simp only [pev, blockEmb, aeval_rename, Function.comp_def, if_true]
  exact aeval_X_left_apply f

theorem pev_ne {s t : S} (h : s ≠ t) (z : S × (Fin n × Fin n) → K) (f : MvPolynomial (Fin n × Fin n) K) :
    pev t z (blockEmb K s f) = C (eval (fun v => z (s, v)) f) := by
  simp only [pev, blockEmb, aeval_rename, Function.comp_def, h, if_false]
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p v hp => simp only [map_mul, hp, aeval_X, eval_X]

theorem pev_prod (t : S) (z : S × (Fin n × Fin n) → K) (f : S → MvPolynomial (Fin n × Fin n) K) :
    pev t z (∏ s, blockEmb K s (f s)) = (∏ s ∈ Finset.univ.erase t, eval (fun v => z (s, v)) (f s)) • f t := by
  rw [map_prod, ← Finset.mul_prod_erase _ _ (Finset.mem_univ t), pev_self, smul_eq_C_mul, map_prod, mul_comm]
  congr 1
  exact Finset.prod_congr rfl fun s hs => pev_ne (Finset.ne_of_mem_erase hs) _ _

theorem eq_zero_of_pev [Infinite K] (t : S) (G : MvPolynomial (S × (Fin n × Fin n)) K) (h : ∀ z, pev t z G = 0) :
    G = 0 := by
  apply MvPolynomial.funext
  intro z
  have e : (aeval fun v => z (t, v)).comp (pev t z) = aeval z := by
    apply algHom_ext
    rintro ⟨s, v⟩
    by_cases hs : s = t
    · simp [pev, hs]
    · simp [pev, hs]
  have := congrArg (fun F => F G) e
  simp only [AlgHom.comp_apply, h, map_zero] at this
  simpa [aeval_eq_eval] using this.symm

theorem mem_tensor [Infinite K] (V : S → Submodule K (MvPolynomial (Fin n × Fin n) K))
    (G : MvPolynomial (S × (Fin n × Fin n)) K) (h : ∀ t z, pev t z G ∈ V t) : G ∈ tensorLat K K V := by
  have hπ : ∀ t, ∃ π : Module.End K (MvPolynomial (Fin n × Fin n) K), (∀ f, π f ∈ V t) ∧ ∀ f ∈ V t, π f = f := by
    intro t
    obtain ⟨W, hW⟩ := (V t).exists_isCompl
    exact ⟨(V t).subtype ∘ₗ (V t).linearProjOfIsCompl W hW, fun f => ((V t).linearProjOfIsCompl W hW f).2,
      fun f hf => congrArg Subtype.val (Submodule.linearProjOfIsCompl_apply_left hW ⟨f, hf⟩)⟩
  choose π hπ1 hπ2 using hπ
  have h1 : ∀ t, tens (fun s => if s = t then π s else 1) G = G := by
    intro t
    rw [← sub_eq_zero]
    apply eq_zero_of_pev t
    intro z
    have : (pev t z).toLinearMap ∘ₗ tens (fun s => if s = t then π s else 1) = π t ∘ₗ (pev t z).toLinearMap := by
      apply lin_ext
      intro f
      simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, tens_prod, pev_prod, map_smul, if_true]
      congr 1
      exact Finset.prod_congr rfl fun s hs => by simp [Finset.ne_of_mem_erase hs]
    have e := congrArg (fun F => F G) this
    simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply] at e
    rw [map_sub, e, hπ2 t _ (h t z), sub_self]
  have h2 : ∀ T : Finset S, tens (fun s => if s ∈ T then π s else 1) G = G := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      have : tens (fun s => if s ∈ (∅ : Finset S) then π s else 1) = LinearMap.id :=
        lin_ext _ _ fun f => by simp [tens_prod]
      rw [this]; rfl
    | insert t T ht ih =>
      have : tens (fun s => if s ∈ insert t T then π s else 1) =
          tens (fun s => if s ∈ T then π s else 1) ∘ₗ tens (fun s => if s = t then π s else 1) := by
        apply lin_ext
        intro f
        simp only [LinearMap.comp_apply, tens_prod]
        refine Finset.prod_congr rfl fun s _ => ?_
        by_cases hs : s = t
        · subst hs; simp [ht]
        · simp [hs]
      rw [this, LinearMap.comp_apply, h1, ih]
  rw [← h2 Finset.univ]
  simp only [Finset.mem_univ, if_true]
  generalize G = F
  induction F using MvPolynomial.induction_on' with
  | add p q hp hq => rw [map_add]; exact add_mem hp hq
  | monomial m c =>
    have : (monomial m c : MvPolynomial _ K) = c • monomial m 1 := by simp [smul_monomial]
    rw [this, map_smul, tens_monomial]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, fun s => hπ1 s _, rfl⟩)

end Tensor

section Irr

open Formalism.GradedWeylDivisibility

variable {n : ℕ}

theorem rowGen_eval (a b : Fin n) (c : ℚ) (f : MvPolynomial (Fin n × Fin n) ℚ) :
    (rowGen ℚ a b f).eval (C c) = rowAct ℚ (1 + Matrix.single b a c) f := by
  have : ((Polynomial.aeval (R := MvPolynomial (Fin n × Fin n) ℚ) (C c : MvPolynomial (Fin n × Fin n) ℚ)).restrictScalars ℚ).comp
      (rowGen ℚ (n := n) a b) = rowAct ℚ (1 + Matrix.single b a c) := by
    apply algHom_ext
    rintro ⟨u, s⟩
    simp only [rowGen, rowAct, AlgHom.comp_apply, aeval_X, AlgHom.coe_restrictScalars', map_add, Matrix.add_apply,
      add_mul, Finset.sum_add_distrib]
    congr 1
    · rw [Finset.sum_eq_single u]
      · simp
      · intro j _ hj; simp [Matrix.one_apply_ne (Ne.symm hj)]
      · simp
    · rw [Finset.sum_eq_single a]
      · by_cases h : u = b
        · simp [h]
          ring
        · simp [h, Matrix.single_apply, Ne.symm h]
      · intro j _ hj; simp [Matrix.single_apply, Ne.symm hj]
      · simp
  have := congrArg (fun F => F f) this
  simpa [Polynomial.coe_aeval_eq_eval] using this

theorem closed_of_stable (M : Submodule ℚ (MvPolynomial (Fin n × Fin n) ℚ))
    (h : ∀ g : GL (Fin n) ℚ, ∀ f ∈ M, rowAct ℚ (g : Matrix (Fin n) (Fin n) ℚ) f ∈ M) : RowDivClosed M := by
  intro a b k f hf
  rw [← Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff]
  intro φ hφ
  let Q := rowGen ℚ a b f
  let R : Polynomial ℚ := ∑ i ∈ Finset.range (Q.natDegree + 1), Polynomial.monomial i (φ (Q.coeff i))
  have hR : R = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    refine Set.Infinite.mono (s := {-1}ᶜ) ?_ (Set.toFinite _).infinite_compl
    intro c hc
    have hdet : (1 + Matrix.single b a c : Matrix (Fin n) (Fin n) ℚ).det ≠ 0 := by
      by_cases hab : b = a
      · subst hab
        have : (1 + Matrix.single b b c : Matrix (Fin n) (Fin n) ℚ) =
            Matrix.diagonal (fun i => if i = b then 1 + c else 1) := by
          ext i j
          by_cases hij : i = j
          · subst hij
            by_cases hi : i = b
            · simp [hi]
            · simp [hi, Matrix.single_apply, Ne.symm hi]
          · simp only [Matrix.add_apply, Matrix.one_apply_ne hij, Matrix.diagonal_apply_ne _ hij, Matrix.single_apply]
            rw [if_neg (by rintro ⟨rfl, rfl⟩; exact hij rfl)]; simp
        rw [this, Matrix.det_diagonal, Finset.prod_ne_zero_iff]
        intro i _
        split_ifs
        · intro h0; apply hc; simp only [Set.mem_singleton_iff]; linarith
        · simp
      · have := Matrix.det_transvection_of_ne b a hab c
        rw [Matrix.transvection] at this
        rw [this]; simp
    have h1 := h (Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet) f hf
    have h2 : φ (Q.eval (C c)) = 0 := by
      rw [rowGen_eval]
      exact (Submodule.mem_dualAnnihilator φ).1 hφ _ h1
    simp only [Set.mem_setOf_eq, Polynomial.IsRoot.def, R, Polynomial.eval_finset_sum, Polynomial.eval_monomial]
    rw [Polynomial.eval_eq_sum_range, map_sum] at h2
    rw [← h2]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← C_pow, mul_comm (Q.coeff i), ← smul_eq_C_mul, map_smul, smul_eq_mul, mul_comm]
  have := congrArg (fun P => P.coeff k) hR
  simp only [R, Polynomial.finset_sum_coeff, Polynomial.coeff_monomial, Finset.sum_ite_eq', Polynomial.coeff_zero] at this
  split_ifs at this with hk
  · exact this
  · have : Q.coeff k = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by simpa using hk)
    show φ (Q.coeff k) = 0
    rw [this, map_zero]

theorem irr {K : Type} [Field K] [Algebra ℚ K] (ν : Fin n → ℕ) (hν : Antitone ν)
    (M : Submodule ℚ (MvPolynomial (Fin n × Fin n) ℚ)) (hle : M ≤ dualWeyl ℚ n n ν) (hne : M ≠ ⊥)
    (h : ∀ g : GL (Fin n) ℚ, ∀ f ∈ M, rowAct ℚ (g : Matrix (Fin n) (Fin n) ℚ) f ∈ M)
    (N : Submodule K (MvPolynomial (Fin n × Fin n) K)) (hN : ∀ f ∈ M, map (algebraMap ℚ K) f ∈ N) :
    dualWeyl K n n ν ≤ N := by
  have hc := closed_of_stable M h
  have e := closedEqNabla n n le_rfl ν hν M hle hc (hwInClosed n n le_rfl ν hν M hle hc hne)
  rw [standardMonomialSpanDomain, Submodule.span_le]
  rintro _ ⟨k, sz, hsz, I, rfl, rfl⟩
  have := hN _ (e ▸ bidetMem ℚ n n k sz hsz I)
  suffices e2 : map (algebraMap ℚ K) (bideterminant ℚ sz hsz I) = bideterminant K sz hsz I by rw [← e2]; exact this
  simp only [bideterminant, initMinor, map_prod, RingHom.map_det]
  refine Finset.prod_congr rfl fun i _ => ?_
  congr 1
  ext1 p q
  simp

end Irr

section Core

open Formalism.GradedWeylDivisibility GlobalTheory.FrameRead

abbrev Row (Ix : Type) (p q : ℕ) : Type := Ix × (Fin p ⊕ Fin q)

abbrev Lt (Ix : Type) (p q n : ℕ) : Type := Row Ix p q × Fin n

variable {Ix : Type} {p q n : ℕ} (h : p + q ≤ n)

def cx (i : Fin p) : Fin n := ⟨i, by omega⟩

def cy (j : Fin q) : Fin n := ⟨n - 1 - j, by omega⟩

def val {A : Type} [CommRing A] (g : Ix → Matrix (Fin n) (Fin n) A) : Lt Ix p q n → A := fun ℓ =>
  Sum.elim (fun i => g ℓ.1.1 ℓ.2 (cx h i)) (fun j => (g ℓ.1.1).adjugate (cy h j) ℓ.2) ℓ.1.2

@[simp] theorem val_inl {A : Type} [CommRing A] (g : Ix → Matrix (Fin n) (Fin n) A) (t : Ix) (i : Fin p) (b : Fin n) :
    val h g ((t, Sum.inl i), b) = g t b (cx h i) := rfl

@[simp] theorem val_inr {A : Type} [CommRing A] (g : Ix → Matrix (Fin n) (Fin n) A) (t : Ix) (j : Fin q) (b : Fin n) :
    val h g ((t, Sum.inr j), b) = (g t).adjugate (cy h j) b := rfl

def xl (i : Ix × Fin p × Fin q) (b : Fin n) : Lt Ix p q n := ((i.1, Sum.inl i.2.1), b)

def yl (i : Ix × Fin p × Fin q) (b : Fin n) : Lt Ix p q n := ((i.1, Sum.inr i.2.2), b)

variable {K : Type} [Field K]

theorem map_val {A B : Type} [CommRing A] [CommRing B] [Algebra K A] [Algebra K B] (φ : A →ₐ[K] B)
    (g : Ix → Matrix (Fin n) (Fin n) A) (P : MvPolynomial (Lt Ix p q n) K) :
    φ (aeval (val h g) P) = aeval (val h fun t => (g t).map φ) P := by
  rw [← AlgHom.comp_apply]
  congr 1
  apply algHom_ext
  rintro ⟨⟨t, i | j⟩, b⟩
  · simp
  · simp only [AlgHom.comp_apply, aeval_X, val_inr]
    have := congrFun (congrFun (φ.map_adjugate (g t)) (cy h j)) b
    simpa using this

theorem cx_ne_cy (i : Fin p) (j : Fin q) : cy h j ≠ cx h i := by
  intro e
  have := congrArg Fin.val e
  simp only [cx, cy] at this
  omega

abbrev II (Ix : Type) (p q n : ℕ) (K : Type) [Field K] : Ideal (MvPolynomial (Lt Ix p q n) K) :=
  Ideal.span (Set.range (qf (xl (Ix := Ix) (p := p) (q := q) (n := n)) yl K))

theorem val_ideal {A : Type} [CommRing A] [Algebra K A] (g : Ix → Matrix (Fin n) (Fin n) A)
    {P : MvPolynomial (Lt Ix p q n) K} (hP : P ∈ II Ix p q n K) : aeval (val h g) P = 0 := by
  have : II Ix p q n K ≤ RingHom.ker (aeval (R := K) (val h g)) := by
    rw [Ideal.span_le]
    rintro _ ⟨⟨t, i, j⟩, rfl⟩
    have := congrFun (congrFun (Matrix.adjugate_mul (g t)) (cy h j)) (cx h i)
    rw [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply_ne (cx_ne_cy h i j), smul_zero] at this
    simp [qf, xl, yl, ← this, mul_comm]
  exact this hP

variable [DecidableEq Ix]

def shift (ρ ρ' : Row Ix p q) (c : K) : MvPolynomial (Lt Ix p q n) K →ₐ[K] MvPolynomial (Lt Ix p q n) K :=
  aeval fun ℓ => if ℓ.1 = ρ then X ℓ + C c * X (ρ', ℓ.2) else X ℓ

def Inv (P : MvPolynomial (Lt Ix p q n) K) : Prop :=
  (∀ t (i i' : Fin p), i' < i → ∀ c : K, shift (t, Sum.inl i) (t, Sum.inl i') c P = P) ∧
  (∀ t (i i' : Fin q), i' < i → ∀ c : K, shift (t, Sum.inr i) (t, Sum.inr i') c P = P)

theorem aeval_shift {A : Type} [CommRing A] [Algebra K A] (v : Lt Ix p q n → A) (ρ ρ' : Row Ix p q) (c : K)
    (P : MvPolynomial (Lt Ix p q n) K) :
    aeval v (shift ρ ρ' c P) =
      aeval (fun ℓ => if ℓ.1 = ρ then v ℓ + algebraMap K A c * v (ρ', ℓ.2) else v ℓ) P := by
  rw [← AlgHom.comp_apply]
  congr 1
  apply algHom_ext
  intro ℓ
  simp only [shift, AlgHom.comp_apply, aeval_X]
  split_ifs <;> simp

theorem adj_transv {A : Type} [CommRing A] {l j : Fin n} (hlj : l ≠ j) (c : A) :
    (Matrix.transvection l j c).adjugate = Matrix.transvection l j (-c) := by
  have h1 := Matrix.adjugate_mul (Matrix.transvection l j c)
  rw [Matrix.det_transvection_of_ne _ _ hlj, one_smul] at h1
  have h2 : Matrix.transvection l j c * Matrix.transvection l j (-c) = 1 := by
    rw [Matrix.transvection_mul_transvection_same _ _ hlj]; simp
  rw [← mul_one (Matrix.transvection l j c).adjugate, ← h2, ← mul_assoc, h1, one_mul]

theorem val_transv {A : Type} [CommRing A] [Algebra K A] (g : Ix → Matrix (Fin n) (Fin n) A) (t : Ix)
    {l j : Fin n} (hlj : l < j) (c : K) {P : MvPolynomial (Lt Ix p q n) K} (hP : Inv P) :
    aeval (val h fun s => g s * if s = t then Matrix.transvection l j (algebraMap K A c) else 1) P =
      aeval (val h g) P := by
  have hx : ∀ s (i : Fin p) b, val h (fun s => g s * if s = t then Matrix.transvection l j (algebraMap K A c) else 1)
      ((s, Sum.inl i), b) = g s b (cx h i) + if s = t ∧ cx h i = j then algebraMap K A c * g s b l else 0 := by
    intro s i b
    rw [val_inl]
    by_cases hs : s = t
    · by_cases hi : cx h i = j
      · simp [hs, hi]
      · simp [hs, hi]
    · simp [hs]
  have hy : ∀ s (i : Fin q) b, val h (fun s => g s * if s = t then Matrix.transvection l j (algebraMap K A c) else 1)
      ((s, Sum.inr i), b) = (g s).adjugate (cy h i) b +
        if s = t ∧ cy h i = l then algebraMap K A (-c) * (g s).adjugate j b else 0 := by
    intro s i b
    rw [val_inr]
    by_cases hs : s = t
    · simp only [hs, if_true, Matrix.adjugate_mul_distrib, adj_transv hlj.ne, true_and]
      by_cases hi : cy h i = l
      · simp [hi]
      · simp [hi]
    · simp [hs]
  have hlj' : (l : ℕ) < j := hlj
  by_cases h1 : (j : ℕ) < p
  · conv_rhs => rw [← hP.1 t ⟨j, h1⟩ ⟨l, by omega⟩ hlj' c]
    rw [aeval_shift]
    congr 2
    funext ⟨⟨s, i⟩, b⟩
    rcases i with i | i
    · rw [hx]
      have : cx h i = j ↔ i = ⟨j, h1⟩ := by simp [cx, Fin.ext_iff]
      by_cases h2 : s = t ∧ i = ⟨j, h1⟩
      · obtain ⟨rfl, rfl⟩ := h2
        simp [cx]
      · rw [if_neg (by rw [this]; exact h2), if_neg (by simpa using h2)]; simp
    · rw [hy]
      have : cy h i ≠ l := by simp only [cy, ne_eq, Fin.ext_iff]; omega
      simp [this]
  by_cases h3 : n - 1 - l < q
  · conv_rhs => rw [← hP.2 t ⟨n - 1 - l, h3⟩ ⟨n - 1 - j, by omega⟩ (by simp only [Fin.mk_lt_mk]; omega) (-c)]
    rw [aeval_shift]
    congr 2
    funext ⟨⟨s, i⟩, b⟩
    rcases i with i | i
    · rw [hx]
      have : cx h i ≠ j := by simp only [cx, ne_eq, Fin.ext_iff]; omega
      simp [this]
    · rw [hy]
      have : cy h i = l ↔ i = ⟨n - 1 - l, h3⟩ := by simp only [cy, Fin.ext_iff]; omega
      by_cases h2 : s = t ∧ i = ⟨n - 1 - l, h3⟩
      · rw [if_pos (by rw [this]; exact h2), if_pos (by simpa using h2)]
        have e : cy h (⟨n - 1 - j, by omega⟩ : Fin q) = j := by simp only [cy, Fin.ext_iff]; omega
        rw [val_inr, val_inr, e, h2.1]
      · rw [if_neg (by rw [this]; exact h2), if_neg (by simpa using h2)]; simp
  · congr 2
    funext ⟨⟨s, i⟩, b⟩
    rcases i with i | i
    · rw [hx]
      have : cx h i ≠ j := by simp only [cx, ne_eq, Fin.ext_iff]; omega
      simp [this]
    · rw [hy]
      have : cy h i ≠ l := by simp only [cy, ne_eq, Fin.ext_iff]; omega
      simp [this]

def mu (a : Row Ix p q → ℕ) (t : Ix) (k : Fin n) : ℕ :=
  (∑ i, if cx h i = k then a (t, Sum.inl i) else 0) + ∑ j, if k ≠ cy h j then a (t, Sum.inr j) else 0

variable [Fintype Ix]

theorem prod_block {A : Type} [CommMonoid A] (t : Ix) (c : Fin p ⊕ Fin q → A) (a : Row Ix p q → ℕ) :
    ∏ r : Row Ix p q, (if r.1 = t then c r.2 else 1) ^ a r =
      (∏ i, c (Sum.inl i) ^ a (t, Sum.inl i)) * ∏ j, c (Sum.inr j) ^ a (t, Sum.inr j) := by
  rw [Fintype.prod_prod_type, Finset.prod_eq_single t]
  · simp
  · intro s _ hs; simp [hs]
  · simp

theorem val_diag {A : Type} [CommRing A] [Algebra K A] (g : Ix → Matrix (Fin n) (Fin n) A) (t : Ix)
    (d : Fin n → A) {a : Row Ix p q → ℕ} {P : MvPolynomial (Lt Ix p q n) K} (hP : Deg Prod.fst a P) :
    aeval (val h fun s => g s * if s = t then Matrix.diagonal d else 1) P =
      (∏ k, d k ^ mu h a t k) * aeval (val h g) P := by
  let c : Fin p ⊕ Fin q → A := Sum.elim (fun i => d (cx h i)) fun j => ∏ k ∈ Finset.univ.erase (cy h j), d k
  have e := aeval_scale hP (fun r => if r.1 = t then c r.2 else 1) (val h g)
  rw [prod_block] at e
  convert e using 2
  · congr 1
    funext ⟨⟨s, i⟩, b⟩
    by_cases hs : s = t
    · rcases i with i | i
      · simp [hs, c, mul_comm]
      · simp [hs, c, Matrix.adjugate_mul_distrib, Matrix.adjugate_diagonal]
    · rcases i with i | i <;> simp [hs]
  · simp only [mu, pow_add, Finset.prod_mul_distrib, ← Finset.prod_pow_eq_pow_sum, c, Sum.elim_inl, Sum.elim_inr]
    congr 1
    · rw [Finset.prod_comm]
      refine Finset.prod_congr rfl fun i _ => ?_
      simp [pow_ite]
    · rw [Finset.prod_comm]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [← Finset.prod_pow, ← Finset.filter_ne', Finset.prod_filter]
      refine Finset.prod_congr rfl fun k _ => ?_
      split_ifs <;> simp

theorem pev_cof_mem [CharZero K] {a : Row Ix p q → ℕ} {P : MvPolynomial (Lt Ix p q n) K} (hP : Deg Prod.fst a P)
    (hI : Inv P) (t : Ix) (z : Ix × (Fin n × Fin n) → K) :
    pev t z (aeval (val h (gen K n)) P) ∈ dualWeyl K n n (mu h a t) := by
  rw [dualWeylPoint, map_val]
  refine ⟨deg_of_scale (w := Prod.snd) fun d _ => ?_, fun l j hlj c => ?_⟩
  · have e := val_diag h (fun s => (gen K n s).map (pev t z)) t (fun k => C (d k)) hP
    simp only [← C_pow, ← map_prod] at e
    rw [← e, map_val]
    congr 3
    funext s
    ext1 b k
    by_cases hs : s = t
    · simp [hs, gen, pev, mul_comm]
    · simp [hs, gen, pev]
  · rw [map_val]
    refine Eq.trans ?_ (val_transv h _ t hlj c hI)
    congr 3
    funext s
    ext1 b k
    by_cases hs : s = t
    · by_cases hk : k = j
      · simp [hs, hk, gen, pev, colAdd, hlj.ne]
      · simp [hs, hk, gen, pev, colAdd]
    · simp [hs, gen, pev]

theorem cof_mem [CharZero K] {a : Row Ix p q → ℕ} {P : MvPolynomial (Lt Ix p q n) K} (hP : Deg Prod.fst a P)
    (hI : Inv P) : aeval (val h (gen K n)) P ∈ tensorLat K K fun t => dualWeyl K n n (mu h a t) :=
  mem_tensor _ _ fun t z => pev_cof_mem h hP hI t z

end Core

section Act

open Formalism.GradedWeylDivisibility GlobalTheory.FrameRead Formalism.L2.DIV
open scoped Matrix

variable {Ix : Type} [Fintype Ix] [DecidableEq Ix] {p q n : ℕ} (h : p + q ≤ n) {K : Type} [Field K]

def mat (g : Ix → GL (Fin n) K) (ρ : Row Ix p q) : Matrix (Fin n) (Fin n) K :=
  Sum.elim (fun _ => (g ρ.1 : Matrix (Fin n) (Fin n) K)ᵀ) (fun _ => (((g ρ.1)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) ρ.2

def act (g : Ix → GL (Fin n) K) : MvPolynomial (Lt Ix p q n) K →ₐ[K] MvPolynomial (Lt Ix p q n) K :=
  aeval fun ℓ => ∑ j, C (mat g ℓ.1 ℓ.2 j) * X (ℓ.1, j)

theorem aeval_act {A : Type} [CommRing A] [Algebra K A] (v : Lt Ix p q n → A) (g : Ix → GL (Fin n) K)
    (P : MvPolynomial (Lt Ix p q n) K) :
    aeval v (act g P) = aeval (fun ℓ => ∑ j, algebraMap K A (mat g ℓ.1 ℓ.2 j) * v (ℓ.1, j)) P := by
  rw [← AlgHom.comp_apply]
  congr 1
  apply algHom_ext
  intro ℓ
  simp [act]

theorem cof_act (g : Ix → GL (Fin n) K) {a : Row Ix p q → ℕ} {P : MvPolynomial (Lt Ix p q n) K}
    (hP : Deg Prod.fst a P) :
    aeval (val h (gen K n)) (act g P) =
      (∏ t, ((g t : Matrix (Fin n) (Fin n) K).det)⁻¹ ^ (∑ j, a (t, Sum.inr j))) • trAct g (aeval (val h (gen K n)) P) := by
  let c : Row Ix p q → MvPolynomial (Ix × Fin n × Fin n) K := fun r =>
    Sum.elim (fun _ => 1) (fun _ => C ((g r.1 : Matrix (Fin n) (Fin n) K).det)⁻¹) r.2
  have e := aeval_scale hP c (val h fun t => (gen K n t).map (trAct g))
  have e2 : ∀ t, (gen K n t).map (trAct g) = ((g t : Matrix (Fin n) (Fin n) K)ᵀ).map C * gen K n t := by
    intro t
    ext1 b k
    simp [gen, trAct, blockAct, Matrix.mul_apply]
  rw [map_val, aeval_act, smul_eq_C_mul]
  convert e using 2
  · congr 1
    funext ⟨⟨t, i⟩, b⟩
    rcases i with i | i
    · simp [c, e2, mat, Matrix.mul_apply]
    · simp only [c, mat, Sum.elim_inr, val_inr, e2, Matrix.adjugate_mul_distrib, Matrix.mul_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      have h1 := congrFun (congrFun ((C : K →+* MvPolynomial (Ix × Fin n × Fin n) K).map_adjugate
        ((g t : Matrix (Fin n) (Fin n) K)ᵀ)) j) b
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply] at h1
      rw [← h1, ← Matrix.adjugate_transpose, Matrix.transpose_apply, Matrix.coe_units_inv, Matrix.inv_def,
        Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul, map_mul, algebraMap_eq]
      ring
  · rw [Fintype.prod_prod_type, map_prod]
    refine Finset.prod_congr rfl fun t _ => ?_
    simp [c, Finset.prod_pow_eq_pow_sum, -inv_pow]

theorem act_deg [CharZero K] (g : Ix → GL (Fin n) K) {a : Row Ix p q → ℕ} {P : MvPolynomial (Lt Ix p q n) K}
    (hP : Deg Prod.fst a P) : Deg Prod.fst a (act g P) := by
  refine deg_of_scale fun t _ => ?_
  have e := aeval_scale hP (fun r => (C (t r) : MvPolynomial (Lt Ix p q n) K))
    (fun ℓ => ∑ j, C (mat g ℓ.1 ℓ.2 j) * X (ℓ.1, j))
  rw [aeval_act, map_prod]
  simp only [map_pow]
  rw [act, ← e]
  congr 2
  funext ℓ
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by rw [algebraMap_eq]; ring

theorem shift_act (g : Ix → GL (Fin n) K) {ρ ρ' : Row Ix p q} (hm : mat g ρ = mat g ρ') (c : K)
    (P : MvPolynomial (Lt Ix p q n) K) : shift ρ ρ' c (act g P) = act g (shift ρ ρ' c P) := by
  rw [← AlgHom.comp_apply, ← AlgHom.comp_apply]
  congr 1
  apply algHom_ext
  intro ℓ
  by_cases hl : ℓ.1 = ρ
  · simp only [AlgHom.comp_apply, act, shift, aeval_X, hl, if_true, map_sum, map_mul, map_add, algHom_C, algebraMap_eq,
      ← hm, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  · simp [act, shift, hl]

theorem act_inv (g : Ix → GL (Fin n) K) {P : MvPolynomial (Lt Ix p q n) K} (hP : Inv P) : Inv (act g P) :=
  ⟨fun t i i' hi c => (shift_act g (by rfl) c P).trans (by rw [hP.1 t i i' hi]),
    fun t i i' hi c => (shift_act g (by rfl) c P).trans (by rw [hP.2 t i i' hi])⟩

theorem pderiv_shift (ρ ρ' : Row Ix p q) (c : K) (v : Lt Ix p q n) (P : MvPolynomial (Lt Ix p q n) K) :
    pderiv v (shift ρ ρ' c P) =
      shift ρ ρ' c (pderiv v P) + if v.1 = ρ' then c • shift ρ ρ' c (pderiv (ρ, v.2) P) else 0 := by
  have hX : ∀ ℓ : Lt Ix p q n, pderiv v (shift ρ ρ' c (X ℓ)) =
      shift ρ ρ' c (pderiv v (X ℓ)) + if v.1 = ρ' then c • shift ρ ρ' c (pderiv (ρ, v.2) (X ℓ)) else 0 := by
    rintro ⟨r, b⟩
    obtain ⟨r', b'⟩ := v
    simp only [pderiv_X, Pi.single_apply, apply_ite (shift ρ ρ' c), map_one, map_zero]
    simp only [shift, aeval_X]
    by_cases h1 : r = ρ
    · subst h1
      simp only [if_true, map_add, pderiv_C_mul, pderiv_X, Pi.single_apply, Prod.mk.injEq, true_and]
      congr 1
      by_cases h2 : r' = ρ'
      · subst h2; simp [smul_eq_C_mul]
      · simp [h2, Ne.symm h2]
    · simp [h1, pderiv_X, Pi.single_apply]
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add P Q hP hQ =>
    simp only [map_add, hP, hQ]
    split_ifs
    · rw [smul_add]; ring
    · ring
  | mul_X P ℓ hP =>
    simp only [map_mul, pderiv_mul, map_add, hP, hX]
    split_ifs
    · simp only [smul_eq_C_mul]; ring
    · ring

theorem harm_shift (t : Ix) (c : K) {P : MvPolynomial (Lt Ix p q n) K} (hP : ∀ i, lp xl yl i P = 0) :
    (∀ u u' : Fin p, ∀ i, lp xl yl i (shift (t, Sum.inl u) (t, Sum.inl u') c P) = 0) ∧
    (∀ u u' : Fin q, ∀ i, lp xl yl i (shift (t, Sum.inr u) (t, Sum.inr u') c P) = 0) := by
  constructor
  · rintro u u' ⟨s, i, j⟩
    have h1 := congrArg (shift (t, Sum.inl u) (t, Sum.inl u') c) (hP (s, i, j))
    have h2 := congrArg (shift (t, Sum.inl u) (t, Sum.inl u') c) (hP (t, u, j))
    simp only [lp, xl, yl, map_sum, map_zero] at h1 h2 ⊢
    simp only [pderiv_shift, Prod.mk.injEq, reduceCtorEq, and_false, if_false, add_zero, Finset.sum_add_distrib, h1,
      zero_add]
    by_cases h3 : s = t ∧ (Sum.inl i : Fin p ⊕ Fin q) = Sum.inl u'
    · simp only [h3, and_self, if_true, ← Finset.smul_sum, h2, smul_zero]
    · simp only [h3, if_false, Finset.sum_const_zero]
  · rintro u u' ⟨s, i, j⟩
    have h1 := congrArg (shift (t, Sum.inr u) (t, Sum.inr u') c) (hP (s, i, j))
    have h2 := congrArg (shift (t, Sum.inr u) (t, Sum.inr u') c) (hP (t, i, u))
    simp only [lp, xl, yl, map_sum, map_zero] at h1 h2 ⊢
    by_cases h3 : s = t ∧ (Sum.inr j : Fin p ⊕ Fin q) = Sum.inr u'
    · simp only [pderiv_shift, Prod.mk.injEq, h3, and_self, if_true, map_add, Derivation.map_smul, reduceCtorEq, and_false,
        if_false, add_zero, Finset.sum_add_distrib, ← Finset.smul_sum, h2, smul_zero]
      simpa only [h3] using h1
    · simp only [pderiv_shift, Prod.mk.injEq, h3, reduceCtorEq, and_false, if_false, add_zero, h1]

theorem ideal_shift_of {ρ ρ' : Row Ix p q} {c : K}
    (hq : ∀ i, shift ρ ρ' c (qf xl yl K i) ∈ II Ix p q n K) {P : MvPolynomial (Lt Ix p q n) K}
    (hP : P ∈ II Ix p q n K) : shift ρ ρ' c P ∈ II Ix p q n K := by
  obtain ⟨d, rfl⟩ := Ideal.mem_span_range_iff_exists_fun.1 hP
  rw [map_sum]
  exact Ideal.sum_mem _ fun i _ => by rw [map_mul]; exact Ideal.mul_mem_left _ _ (hq i)

theorem ideal_shift (t : Ix) (c : K) {P : MvPolynomial (Lt Ix p q n) K} (hP : P ∈ II Ix p q n K) :
    (∀ u u' : Fin p, shift (t, Sum.inl u) (t, Sum.inl u') c P ∈ II Ix p q n K) ∧
    (∀ u u' : Fin q, shift (t, Sum.inr u) (t, Sum.inr u') c P ∈ II Ix p q n K) := by
  have hm : ∀ i, qf xl yl K i ∈ II Ix p q n K := fun i => Ideal.subset_span ⟨i, rfl⟩
  constructor
  · refine fun u u' => ideal_shift_of ?_ hP
    rintro ⟨s, i, j⟩
    by_cases h3 : s = t ∧ i = u
    · obtain ⟨rfl, rfl⟩ := h3
      convert add_mem (hm (s, i, j)) (Ideal.mul_mem_left _ (C c) (hm (s, u', j)))
      simp [qf, xl, yl, shift, add_mul, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]
    · convert hm (s, i, j)
      simp [qf, xl, yl, shift, h3]
  · refine fun u u' => ideal_shift_of ?_ hP
    rintro ⟨s, i, j⟩
    by_cases h3 : s = t ∧ j = u
    · obtain ⟨rfl, rfl⟩ := h3
      convert add_mem (hm (s, i, j)) (Ideal.mul_mem_left _ (C c) (hm (s, i, u')))
      simp [qf, xl, yl, shift, mul_add, Finset.sum_add_distrib, Finset.mul_sum, mul_left_comm]
    · convert hm (s, i, j)
      simp [qf, xl, yl, shift, h3]

theorem exists_harm_inv (φ : K →+* ℂ) {a : Row Ix p q → ℕ} {P : MvPolynomial (Lt Ix p q n) K}
    (hP : Deg Prod.fst a P) (hI : Inv P) :
    ∃ Q : MvPolynomial (Lt Ix p q n) K, Deg Prod.fst a Q ∧ Inv Q ∧ (∀ i, lp xl yl i Q = 0) ∧ aeval (val h (gen K n)) Q = aeval (val h (gen K n)) P := by
  obtain ⟨Q, h1, h2, h3⟩ := exists_harm (K := K) (σ := Lt Ix p q n) (ι := Ix × Fin p × Fin q) (κ := Fin n) xl yl φ Prod.fst (fun i => (i.1, Sum.inl i.2.1)) (fun i => (i.1, Sum.inr i.2.2))
    (fun _ _ => rfl) (fun _ _ => rfl) hP
  have key : ∀ S : MvPolynomial (Lt Ix p q n) K →ₐ[K] MvPolynomial (Lt Ix p q n) K, S P = P →
      S (P - Q) ∈ II Ix p q n K → (∀ i, lp xl yl i (S Q) = 0) → S Q = Q := by
    intro S e1 e2 e3
    rw [← sub_eq_zero]
    refine harm_ideal_zero xl yl φ ?_ fun i => ?_
    · have : S Q - Q = (P - Q) - S (P - Q) := by rw [map_sub, e1]; ring
      rw [this]
      exact sub_mem h3 e2
    · have := h2 i
      have e4 := e3 i
      simp only [lp, map_sub, Finset.sum_sub_distrib] at this e4 ⊢
      rw [this, e4, sub_zero]
  refine ⟨Q, h1, ⟨fun t i i' hi c => ?_, fun t i i' hi c => ?_⟩, h2, ?_⟩
  · exact key _ (hI.1 t i i' hi c) ((ideal_shift t c h3).1 i i') ((harm_shift t c h2).1 i i')
  · exact key _ (hI.2 t i i' hi c) ((ideal_shift t c h3).2 i i') ((harm_shift t c h2).2 i i')
  · have := val_ideal h (gen K n) h3
    rw [map_sub, sub_eq_zero] at this
    exact this.symm

end Act

section Inj

open GlobalTheory.FrameRead

variable {Ix : Type} [Fintype Ix] [DecidableEq Ix] {p q n : ℕ} (h : p + q ≤ n) {K : Type} [Field K]

def xm (p q n : ℕ) (K : Type) [Field K] (t : Ix) : Matrix (Fin n) (Fin n) (MvPolynomial (Lt Ix p q n) K) :=
  Matrix.of fun b k => if hk : (k : ℕ) < p then X ((t, Sum.inl ⟨k, hk⟩), b) else if b = k then 1 else 0

def ym (p q n : ℕ) (K : Type) [Field K] (t : Ix) : Matrix (Fin n) (Fin n) (MvPolynomial (Lt Ix p q n) K) :=
  Matrix.of fun k b => if hk : n - 1 - k < q then X ((t, Sum.inr ⟨n - 1 - k, hk⟩), b) else if k = b then 1 else 0

def wm (p q n : ℕ) (K : Type) [Field K] (t : Ix) : Matrix (Fin n) (Fin n) (MvPolynomial (Lt Ix p q n) K) :=
  Matrix.of fun i k => if (k : ℕ) < p then (if i = k then 1 else 0) else (ym p q n K t * xm p q n K t) i k

theorem xm_cx (t : Ix) (i : Fin p) (b : Fin n) : xm p q n K t b (cx h i) = X ((t, Sum.inl i), b) := by
  simp [xm, cx]

theorem ym_cy (t : Ix) (j : Fin q) (b : Fin n) : ym p q n K t (cy h j) b = X ((t, Sum.inr j), b) := by
  have h1 : n - 1 - (n - 1 - j) = j := by have := j.2; omega
  simp [ym, cy, h1]

include h in
theorem det_wm_ne (t : Ix) : (wm p q n K t).det ≠ 0 := by
  let z : Lt Ix p q n → K := fun ℓ => if ℓ.2 = Sum.elim (cx h) (cy h) ℓ.1.2 then 1 else 0
  have h1 : (xm p q n K t).map (eval z) = 1 := by
    ext b k
    simp only [xm, Matrix.map_apply, Matrix.of_apply, Matrix.one_apply]
    split_ifs with h1 h2 <;> simp_all [z, cx]
  have h2 : (ym p q n K t).map (eval z) = 1 := by
    ext k b
    have h3 : n - 1 - (n - 1 - k) = k := by have := k.2; omega
    simp only [ym, Matrix.map_apply, Matrix.of_apply, Matrix.one_apply]
    by_cases hk : n - 1 - k < q
    · have e : cy h ⟨n - 1 - k, hk⟩ = k := Fin.ext h3
      simp only [hk, dif_pos, eval_X, z, Sum.elim_inr, e, eq_comm]
    · simp only [hk, dif_neg, not_false_eq_true]
      split_ifs <;> simp
  have h3 : (wm p q n K t).map (eval z) = 1 := by
    have h4 : (ym p q n K t * xm p q n K t).map (eval z) = 1 := by rw [Matrix.map_mul, h1, h2, one_mul]
    ext i k
    have := congrFun (congrFun h4 i) k
    simp only [wm, Matrix.map_apply, Matrix.of_apply, Matrix.one_apply] at this ⊢
    split_ifs with h1 h2 <;> simp_all
  intro h0
  have := (eval z).map_det (wm p q n K t)
  rw [h0, map_zero, RingHom.mapMatrix_apply, h3, Matrix.det_one] at this
  exact zero_ne_one this

def th (K : Type) [Field K] : Lt Ix p q n → MvPolynomial (Lt Ix p q n) K := fun ℓ =>
  Sum.elim (fun _ => X ℓ) (fun j => (wm p q n K ℓ.1.1 * (xm p q n K ℓ.1.1).adjugate) (cy h j) ℓ.2) ℓ.1.2

theorem th_eq_zero {a : Row Ix p q → ℕ} {P : MvPolynomial (Lt Ix p q n) K} (hP : Deg Prod.fst a P)
    (h0 : aeval (val h (gen K n)) P = 0) : aeval (th h K) P = 0 := by
  let A := FractionRing (MvPolynomial (Lt Ix p q n) K)
  let ι : MvPolynomial (Lt Ix p q n) K →ₐ[K] A := IsScalarTower.toAlgHom K _ A
  have hι : Function.Injective ι := IsFractionRing.injective (MvPolynomial (Lt Ix p q n) K) A
  have hW : ∀ t, IsUnit ((wm p q n K t).map ι).det := by
    intro t
    have := ι.map_det (wm p q n K t)
    rw [AlgHom.mapMatrix_apply] at this
    rw [← this, isUnit_iff_ne_zero]
    exact fun e => det_wm_ne h t (hι (by rw [e, map_zero]))
  let g : Ix → Matrix (Fin n) (Fin n) A := fun t => (xm p q n K t).map ι * ((wm p q n K t).map ι)⁻¹
  have hg : ∀ t, g t * (wm p q n K t).map ι = (xm p q n K t).map ι := fun t =>
    Matrix.nonsing_inv_mul_cancel_right _ _ (hW t)
  have h1 : aeval (val h g) P = 0 := by
    have := map_val h (aeval fun v : Ix × Fin n × Fin n => g v.1 v.2.1 v.2.2) (gen K n) P
    rw [h0, map_zero] at this
    rw [this]
    congr 3
    funext t
    ext b k
    simp [gen]
  let c : Row Ix p q → A := fun r => Sum.elim (fun _ => 1) (fun _ => ((wm p q n K r.1).map ι).det) r.2
  have h2 := aeval_scale hP c (val h g)
  rw [h1, mul_zero] at h2
  apply hι
  rw [map_zero, ← h2, ← AlgHom.comp_apply]
  congr 1
  apply algHom_ext
  rintro ⟨⟨t, i | j⟩, b⟩
  · have := congrFun (congrFun (hg t) b) (cx h i)
    rw [Matrix.mul_apply, Matrix.map_apply, xm_cx, Finset.sum_eq_single (cx h i)] at this
    · simp [th, c, ← this, wm, cx]
    · intro k _ hk
      have hi : ((cx h i : Fin n) : ℕ) < p := i.2
      simp [wm, hk, hi]
    · simp
  · have e : (wm p q n K t * (xm p q n K t).adjugate).map ι = ((wm p q n K t).map ι).det • (g t).adjugate := by
      have e1 := ι.map_adjugate (xm p q n K t)
      simp only [AlgHom.mapMatrix_apply] at e1
      rw [Matrix.map_mul, e1, ← hg, Matrix.adjugate_mul_distrib, ← mul_assoc, Matrix.mul_adjugate, smul_mul_assoc,
        one_mul]
    have := congrFun (congrFun e (cy h j)) b
    simpa [th, c] using this

theorem th_mod (t : Ix) (j : Fin q) (b : Fin n) :
    (xm p q n K t).det * X ((t, Sum.inr j), b) - th h K ((t, Sum.inr j), b) ∈ II Ix p q n K := by
  have e : (xm p q n K t).det * X ((t, Sum.inr j), b) =
      (ym p q n K t * xm p q n K t * (xm p q n K t).adjugate) (cy h j) b := by
    rw [mul_assoc, Matrix.mul_adjugate, mul_smul_comm, mul_one, Matrix.smul_apply, ym_cy, smul_eq_mul]
  rw [e]
  simp only [th, Sum.elim_inr]
  rw [Matrix.mul_apply, Matrix.mul_apply, ← Finset.sum_sub_distrib]
  refine Ideal.sum_mem _ fun k _ => ?_
  rw [← sub_mul]
  refine Ideal.mul_mem_right _ _ ?_
  by_cases hk : (k : ℕ) < p
  · have h1 : k = cx h ⟨k, hk⟩ := rfl
    have h2 : cy h j ≠ k := by rw [h1]; exact cx_ne_cy h _ _
    simp only [wm, Matrix.of_apply, hk, if_true, h2, if_false, sub_zero]
    refine Ideal.subset_span ⟨(t, ⟨k, hk⟩, j), ?_⟩
    rw [Matrix.mul_apply, qf]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [ym_cy, mul_comm]
    congr 1
    exact (xm_cx h t ⟨k, hk⟩ b).symm
  · simp [wm, hk]

def wt (ℓ : Lt Ix p q n) : ℕ :=
  Sum.elim (fun i : Fin p => n ^ 2 + 2 * ℓ.2 * i - ℓ.2 ^ 2) (fun j : Fin q => 2 * ℓ.2 * (j + 1)) ℓ.1.2

theorem weight_variable_formula (t : Ix) (i : Fin p) (b : Fin n) :
    (wt (((t, Sum.inl i), b) : Lt Ix p q n) : ℤ) = n ^ 2 + 2 * b * i - b ^ 2 := by
  have : (b : ℕ) ^ 2 ≤ n ^ 2 := Nat.pow_le_pow_left b.2.le 2
  simp only [wt, Sum.elim_inl]
  rw [Nat.cast_sub (by omega)]
  push_cast; ring

theorem wt_y (t : Ix) (j : Fin q) (b : Fin n) :
    (wt (((t, Sum.inr j), b) : Lt Ix p q n) : ℤ) = 2 * b * (j + 1) := by
  simp [wt]

def lead (i : Ix × Fin p × Fin q) : Fin n := ⟨i.2.1 + i.2.2 + 1, by omega⟩

theorem degree_qf (m : MonomialOrder.{0,0} (Lt Ix p q n))
    (hm : ∀ c d : Lt Ix p q n →₀ ℕ, Finsupp.weight wt c < Finsupp.weight wt d → c ≺[m] d) (i : Ix × Fin p × Fin q) :
    (qf xl yl K i : MvPolynomial (Lt Ix p q n) K) ≠ 0 ∧ m.degree (qf xl yl K i) =
      Finsupp.single (xl i (lead h i)) 1 + Finsupp.single (yl i (lead h i)) 1 := by
  have e : qf xl yl K i = ∑ b : Fin n, monomial (Finsupp.single (xl i b) 1 + Finsupp.single (yl i b) 1) (1 : K) := by
    simp [qf, X, monomial_mul]
  rw [e]
  refine degree_sum_monomial m wt hm _ _ (lead h i) one_ne_zero fun b hb _ => ?_
  obtain ⟨t, i, j⟩ := i
  simp only [map_add, Finsupp.weight_single, one_smul, xl, yl]
  zify
  simp only [weight_variable_formula, wt_y, lead]
  have : ((b : ℕ) : ℤ) - (i + j + 1) ≠ 0 := by
    intro e; apply hb; simp only [lead, Fin.ext_iff]; omega
  have := sq_pos_of_ne_zero this
  push_cast
  nlinarith

theorem degree_det (m : MonomialOrder.{0,0} (Lt Ix p q n))
    (hm : ∀ c d : Lt Ix p q n →₀ ℕ, Finsupp.weight wt c < Finsupp.weight wt d → c ≺[m] d) (t : Ix) :
    (xm p q n K t).det ≠ 0 ∧ m.degree (xm p q n K t).det =
      ∑ k : Fin n, if hk : (k : ℕ) < p then Finsupp.single ((t, Sum.inl ⟨k, hk⟩), k) 1 else 0 := by
  let e : Equiv.Perm (Fin n) → Lt Ix p q n →₀ ℕ := fun σ =>
    ∑ k : Fin n, if hk : (k : ℕ) < p then Finsupp.single ((t, Sum.inl ⟨k, hk⟩), σ k) 1 else 0
  let c : Equiv.Perm (Fin n) → K := fun σ =>
    (Equiv.Perm.sign σ : ℤ) * ∏ k : Fin n, if (k : ℕ) < p then 1 else if σ k = k then 1 else 0
  have h1 : (xm p q n K t).det = ∑ σ, monomial (e σ) (c σ) := by
    rw [Matrix.det_apply']
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [monomial_sum_index, map_mul, map_prod, mul_assoc, ← Finset.prod_mul_distrib, map_intCast]
    congr 1
    refine Finset.prod_congr rfl fun k _ => ?_
    simp only [xm, Matrix.of_apply]
    split_ifs <;> simp [X]
  rw [h1]
  refine degree_sum_monomial m wt hm e c 1 (by simp [c]) fun σ hσ hc => ?_
  have h2 : ∀ k : Fin n, ¬ (k : ℕ) < p → σ k = k := by
    intro k hk
    have := Finset.prod_ne_zero_iff.1 (right_ne_zero_of_mul hc) k (Finset.mem_univ _)
    by_contra h3
    simp [hk, h3] at this
  simp only [e, map_sum]
  apply Finset.sum_lt_sum
  · intro k _
    split_ifs
    · simp only [Finsupp.weight_single, one_smul]
      zify
      simp only [weight_variable_formula, Equiv.Perm.coe_one, id]
      nlinarith [sq_nonneg (((σ k : ℕ) : ℤ) - (k : ℕ))]
    · rfl
  · obtain ⟨k, hk⟩ : ∃ k, σ k ≠ k := by
      by_contra h3
      push Not at h3
      exact hσ (Equiv.ext h3)
    have hk' : (k : ℕ) < p := by by_contra h3; exact hk (h2 k h3)
    refine ⟨k, Finset.mem_univ _, ?_⟩
    simp only [hk', dif_pos, Finsupp.weight_single, one_smul]
    zify
    simp only [weight_variable_formula, Equiv.Perm.coe_one, id]
    have : ((σ k : ℕ) : ℤ) - (k : ℕ) ≠ 0 := by
      intro e; apply hk; simp only [Fin.ext_iff]; omega
    nlinarith [sq_pos_of_ne_zero this]

include h in
theorem det_xm_nzd (t : Ix) (g : MvPolynomial (Lt Ix p q n) K) (hg : (xm p q n K t).det * g ∈ II Ix p q n K) :
    g ∈ II Ix p q n K := by
  obtain ⟨m, hm⟩ := exists_order (wt (Ix := Ix) (p := p) (q := q) (n := n))
  refine nzd_of_groebner m _ (fun i => (degree_qf h m hm i).1) ?_ _ (degree_det m hm t).1 ?_ g hg
  · rintro ⟨s, i, j⟩ ⟨s', i', j'⟩ hne v
    rw [(degree_qf h m hm _).2, (degree_qf h m hm _).2]
    by_contra hc
    apply hne
    have key : ∀ i : Ix × Fin p × Fin q, ¬ (Finsupp.single (xl i (lead h i)) 1 + Finsupp.single (yl i (lead h i)) 1 :
        Lt Ix p q n →₀ ℕ) v = 0 → v = xl i (lead h i) ∨ v = yl i (lead h i) := by
      intro i hi
      by_contra h3
      rw [not_or] at h3
      exact hi (by simp [Finsupp.single_eq_of_ne h3.1, Finsupp.single_eq_of_ne h3.2])
    rw [not_or] at hc
    rcases key _ hc.1 with h1 | h1 <;> rcases key _ hc.2 with h2 | h2 <;> rw [h1] at h2 <;>
      simp only [xl, yl, lead, Prod.mk.injEq, Sum.inl.injEq, Sum.inr.injEq, Fin.ext_iff, reduceCtorEq, and_false,
        false_and] at h2 ⊢
    · exact ⟨h2.1.1, h2.1.2, by omega⟩
    · exact ⟨h2.1.1, by omega, h2.1.2⟩
  · rintro ⟨s, i, j⟩ v
    rw [(degree_qf h m hm _).2, (degree_det m hm _).2]
    by_contra hc
    simp only [not_or] at hc
    obtain ⟨h1, h2⟩ := hc
    rw [Finsupp.finset_sum_apply] at h2
    obtain ⟨k, -, hk⟩ := Finset.exists_ne_zero_of_sum_ne_zero h2
    split_ifs at hk with hk'
    · rw [Finsupp.single_apply_ne_zero] at hk
      obtain ⟨rfl, -⟩ := hk
      apply h1
      simp only [Finsupp.add_apply, Finsupp.single_apply, xl, yl, lead, Prod.mk.injEq, Sum.inl.injEq, Fin.ext_iff]
      rw [if_neg (by omega), if_neg (by simp), add_zero]
    · simp at hk

theorem cof_inj (φ : K →+* ℂ) {a : Row Ix p q → ℕ} {P : MvPolynomial (Lt Ix p q n) K} (hP : Deg Prod.fst a P)
    (hH : ∀ i, lp xl yl i P = 0) (h0 : aeval (val h (gen K n)) P = 0) : P = 0 := by
  refine harm_ideal_zero xl yl φ ?_ hH
  let π := Ideal.Quotient.mkₐ K (II Ix p q n K)
  let c : Row Ix p q → (MvPolynomial (Lt Ix p q n) K ⧸ II Ix p q n K) := fun r =>
    Sum.elim (fun _ => 1) (fun _ => π (xm p q n K r.1).det) r.2
  have h1 := aeval_scale hP c (fun ℓ => π (X ℓ))
  have h2 : (aeval fun ℓ => π (X ℓ)) = π := by
    apply algHom_ext; intro ℓ; simp
  have h3 : (aeval fun ℓ => c ℓ.1 * π (X ℓ)) = π.comp (aeval (th h K)) := by
    apply algHom_ext
    rintro ⟨⟨t, i | j⟩, b⟩
    · simp [c, th]
    · simp only [aeval_X, AlgHom.comp_apply, c, Sum.elim_inr, ← map_mul]
      exact (Ideal.Quotient.eq).2 (th_mod h t j b)
  rw [h2, h3, AlgHom.comp_apply, th_eq_zero h hP h0, map_zero] at h1
  have h4 : ∏ r, c r ^ a r ∈ nonZeroDivisors _ := by
    refine prod_mem fun r _ => pow_mem ?_ _
    obtain ⟨t, i | j⟩ := r
    · exact one_mem _
    · rw [mem_nonZeroDivisors_iff_left]
      intro x hx
      obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective x
      exact Ideal.Quotient.eq_zero_iff_mem.2 (det_xm_nzd h t g (Ideal.Quotient.eq_zero_iff_mem.1 hx))
  exact Ideal.Quotient.eq_zero_iff_mem.1 (mem_nonZeroDivisors_iff_left.1 h4 _ h1.symm)

end Inj

section Surj

open Formalism.GradedWeylDivisibility GlobalTheory.FrameRead

variable {Ix : Type} [Fintype Ix] [DecidableEq Ix] {p q n : ℕ} (h : p + q ≤ n) {K : Type} [Field K]

def gshift (ρ ρ' : Row Ix p q) : MvPolynomial (Lt Ix p q n) ℚ →ₐ[ℚ] Polynomial (MvPolynomial (Lt Ix p q n) ℚ) :=
  aeval fun ℓ => if ℓ.1 = ρ then Polynomial.C (X ℓ) + Polynomial.X * Polynomial.C (X (ρ', ℓ.2)) else Polynomial.C (X ℓ)

theorem eval_gshift [Algebra ℚ K] (ρ ρ' : Row Ix p q) (c : K) (P : MvPolynomial (Lt Ix p q n) ℚ) :
    Polynomial.eval₂ (map (algebraMap ℚ K)) (C c) (gshift ρ ρ' P) = shift ρ ρ' c (map (algebraMap ℚ K) P) := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [Polynomial.algebraMap_apply]
  | add P Q hP hQ => simp only [map_add, Polynomial.eval₂_add, hP, hQ]
  | mul_X P ℓ hP =>
    simp only [map_mul, Polynomial.eval₂_mul, hP, map_X]
    congr 1
    simp only [gshift, shift, aeval_X]
    split_ifs
    · simp
      ring
    · simp

theorem shift_map [Algebra ℚ K] {ρ ρ' : Row Ix p q} {P : MvPolynomial (Lt Ix p q n) ℚ}
    (hP : ∀ c : ℚ, shift ρ ρ' c P = P) (c : K) : shift ρ ρ' c (map (algebraMap ℚ K) P) = map (algebraMap ℚ K) P := by
  have e : gshift ρ ρ' P - Polynomial.C P = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    refine Set.infinite_of_injective_forall_mem (f := fun c : ℚ => (C c : MvPolynomial (Lt Ix p q n) ℚ))
      (C_injective _ _) fun c => ?_
    have := eval_gshift ρ ρ' c P
    simp only [Algebra.algebraMap_self, map_id, hP] at this
    have e2 : (map (RingHom.id ℚ) : MvPolynomial (Lt Ix p q n) ℚ →+* _) = RingHom.id _ := RingHom.ext fun x => map_id x
    rw [e2, Polynomial.eval₂_id] at this
    simp [this]
  rw [← eval_gshift, sub_eq_zero.1 e, Polynomial.eval₂_C]

def res (t : Ix) (a : Row Ix p q → ℕ) : Row Ix p q → ℕ := fun r => if r.1 = t then a r else 0

def NN (K : Type) [Field K] (t : Ix) (a : Row Ix p q → ℕ) : Submodule K (MvPolynomial (Fin n × Fin n) K) where
  carrier := {f | ∃ P : MvPolynomial (Lt Ix p q n) K, Deg Prod.fst (res t a) P ∧ Inv P ∧
    aeval (val h (gen K n)) P = blockEmb K t f}
  add_mem' := by
    rintro _ _ ⟨P, h1, h2, h3⟩ ⟨Q, k1, k2, k3⟩
    exact ⟨P + Q, h1.add k1, ⟨fun t i j hij c => by rw [map_add, h2.1 t i j hij, k2.1 t i j hij],
      fun t i j hij c => by rw [map_add, h2.2 t i j hij, k2.2 t i j hij]⟩, by rw [map_add, map_add, h3, k3]⟩
  zero_mem' := ⟨0, isWeightedHomogeneous_zero _ _ _, ⟨fun _ _ _ _ _ => map_zero _, fun _ _ _ _ _ => map_zero _⟩, by simp⟩
  smul_mem' := by
    rintro c _ ⟨P, h1, h2, h3⟩
    exact ⟨c • P, (weightedHomogeneousSubmodule K _ _).smul_mem c h1,
      ⟨fun t i j hij c => by rw [map_smul, h2.1 t i j hij], fun t i j hij c => by rw [map_smul, h2.2 t i j hij]⟩,
      by rw [map_smul, map_smul, h3]⟩

theorem NN_map [Algebra ℚ K] (t : Ix) (a : Row Ix p q → ℕ) {f : MvPolynomial (Fin n × Fin n) ℚ} (hf : f ∈ NN h ℚ t a) :
    map (algebraMap ℚ K) f ∈ NN h K t a := by
  obtain ⟨P, h1, h2, h3⟩ := hf
  refine ⟨map (algebraMap ℚ K) P, fun m hm => h1 fun e => hm (by rw [coeff_map, e, map_zero]),
    ⟨fun s i j hij c => shift_map (h2.1 s i j hij) c, fun s i j hij c => shift_map (h2.2 s i j hij) c⟩, ?_⟩
  have e := map_val h (mapAlgHom (σ := Ix × Fin n × Fin n) (Algebra.ofId ℚ K)) (gen ℚ n) P
  rw [h3] at e
  rw [aeval_map_algebraMap]
  have e1 : (fun t => (gen ℚ n t).map (mapAlgHom (σ := Ix × Fin n × Fin n) (Algebra.ofId ℚ K))) = gen K n := by
    funext s
    ext1 b k
    simp [gen]
  rw [e1] at e
  rw [← e]
  simp only [blockEmb, mapAlgHom_apply, map_rename]
  rfl

theorem NN_le [CharZero K] (t : Ix) (a : Row Ix p q → ℕ) : NN h K t a ≤ dualWeyl K n n (mu h a t) := by
  rintro f ⟨P, h1, h2, h3⟩
  have := pev_cof_mem h h1 h2 t 0
  rw [h3, pev_self] at this
  convert this using 2
  funext k
  simp [mu, res]

theorem NN_act [CharZero K] (t : Ix) (a : Row Ix p q → ℕ) (g : GL (Fin n) K) (f : MvPolynomial (Fin n × Fin n) K)
    (hf : f ∈ NN h K t a) : rowAct K (g : Matrix (Fin n) (Fin n) K) f ∈ NN h K t a := by
  obtain ⟨P, h1, h2, h3⟩ := hf
  let g' : Ix → GL (Fin n) K := fun _ => Formalism.BasicNotions.inside₂ K n g⁻¹
  have e := cof_act h g' h1
  rw [h3, Formalism.L2.DIV.trAct, (blockActTensor K K Ix n n _).1, ← map_smul] at e
  have hm : _ ∈ NN h K t a := ⟨_, act_deg g' h1, act_inv g' h2, e⟩
  rw [Submodule.smul_mem_iff] at hm
  · simpa [g', Formalism.BasicNotions.inside₂] using hm
  · refine Finset.prod_ne_zero_iff.2 fun s _ => pow_ne_zero _ (inv_ne_zero ?_)
    exact (g' s).det_ne_zero

theorem shift_rename_self {m : ℕ} {ρ : Fin m → Row Ix p q} (hρ : Function.Injective ρ) (e : Fin n → Fin n)
    (i i' : Fin m) (c : K) (H : MvPolynomial (Fin n × Fin m) K) :
    shift (ρ i) (ρ i') c (rename (fun v => ((ρ v.2, e v.1) : Lt Ix p q n)) H) =
      rename (fun v => ((ρ v.2, e v.1) : Lt Ix p q n)) (colAdd K i' i c H) := by
  rw [← AlgHom.comp_apply, ← AlgHom.comp_apply]
  congr 1
  apply algHom_ext
  intro v
  simp only [AlgHom.comp_apply, rename_X, shift, colAdd, aeval_X, hρ.eq_iff]
  split_ifs <;> simp

theorem shift_rename_ne {m : ℕ} {ρ : Fin m → Row Ix p q} (e : Fin n → Fin n) {r : Row Ix p q} (hr : ∀ i, ρ i ≠ r)
    (r' : Row Ix p q) (c : K) (H : MvPolynomial (Fin n × Fin m) K) :
    shift r r' c (rename (fun v => ((ρ v.2, e v.1) : Lt Ix p q n)) H) =
      rename (fun v => ((ρ v.2, e v.1) : Lt Ix p q n)) H := by
  rw [← AlgHom.comp_apply]
  congr 1
  apply algHom_ext
  intro v
  simp [shift, hr]

theorem aeval_hw {m : ℕ} (hm : m ≤ n) (ν : Fin m → ℕ) (z : Fin n × Fin m → K)
    (hz : ∀ v, z v = if (v.1 : ℕ) = v.2 then 1 else 0) : aeval z (hw K hm ν) = 1 := by
  simp only [hw, map_prod, map_pow, lpMinor, AlgHom.map_det]
  refine Finset.prod_eq_one fun s _ => ?_
  convert one_pow _
  refine Eq.trans ?_ (Matrix.det_one (n := Fin (s + 1)))
  congr 1
  ext a b
  simp [hz, Matrix.one_apply, Fin.ext_iff]

theorem NN_ne [CharZero K] (t : Ix) (a : Row Ix p q → ℕ) (ha : Antitone fun i => a (t, Sum.inl i))
    (hb : Antitone fun i => a (t, Sum.inr i)) : NN h K t a ≠ ⊥ := by
  have hp : p ≤ n := by omega
  have hq : q ≤ n := by omega
  obtain ⟨hA1, hA2⟩ := (dualWeylPoint _ _ _ _ _).1 (hwMem K n p hp _ ha)
  obtain ⟨hB1, hB2⟩ := (dualWeylPoint _ _ _ _ _).1 (hwMem K n q hq _ hb)
  have hA := aeval_hw (K := K) hp fun i => a (t, Sum.inl i)
  have hB := aeval_hw (K := K) hq fun i => a (t, Sum.inr i)
  generalize hw K hp _ = A at *
  generalize hw K hq _ = B at *
  let G : Matrix (Fin n) (Fin n) (MvPolynomial (Fin n × Fin n) K) := Matrix.of fun a s => X (a, s)
  rw [Submodule.ne_bot_iff]
  refine ⟨aeval (fun v => X (v.1, cx h v.2)) A * aeval (fun v => G.adjugate (cy h v.2) (Fin.rev v.1)) B,
    ⟨rename (fun v => (((t, Sum.inl v.2), id v.1) : Lt Ix p q n)) A *
      rename (fun v => (((t, Sum.inr v.2), Fin.rev v.1) : Lt Ix p q n)) B, ?_, ⟨?_, ?_⟩, ?_⟩, ?_⟩
  · refine deg_of_scale fun d _ => ?_
    have e1 := aeval_scale (w := Prod.snd) hA1 (fun i => (C (d (t, Sum.inl i)) : MvPolynomial (Lt Ix p q n) K))
      (fun v => X ((t, Sum.inl v.2), v.1))
    have e2 := aeval_scale (w := Prod.snd) hB1 (fun i => (C (d (t, Sum.inr i)) : MvPolynomial (Lt Ix p q n) K))
      (fun v => X ((t, Sum.inr v.2), Fin.rev v.1))
    rw [map_mul, aeval_rename, aeval_rename]
    simp only [Function.comp_def, id]
    rw [e1, e2, rename_eq_aeval, rename_eq_aeval, Fintype.prod_prod_type, Finset.prod_eq_single t]
    · simp only [res, if_true, Fintype.prod_sum_type, map_mul, map_prod, map_pow, Function.comp_def]
      ring
    · intro s _ hs; simp [res, hs]
    · simp
  · intro s i i' hi c
    rw [map_mul, shift_rename_ne (ρ := fun j => (t, Sum.inr j)) Fin.rev (by simp)]
    congr 1
    by_cases hs : s = t
    · subst hs
      rw [shift_rename_self (ρ := fun j => (s, Sum.inl j)) (fun _ _ => by simp) id, hA2 _ _ hi]
    · rw [shift_rename_ne (ρ := fun j => (t, Sum.inl j)) id (by simp [Ne.symm hs])]
  · intro s i i' hi c
    rw [map_mul, shift_rename_ne (ρ := fun j => (t, Sum.inl j)) id (by simp)]
    congr 1
    by_cases hs : s = t
    · subst hs
      rw [shift_rename_self (ρ := fun j => (s, Sum.inr j)) (fun _ _ => by simp) Fin.rev, hB2 _ _ hi]
    · rw [shift_rename_ne (ρ := fun j => (t, Sum.inr j)) Fin.rev (by simp [Ne.symm hs])]
  · rw [map_mul, map_mul, aeval_rename, aeval_rename, ← AlgHom.comp_apply (blockEmb K t),
      ← AlgHom.comp_apply (blockEmb K t), comp_aeval, comp_aeval]
    congr 3
    · funext v
      simp [gen, blockEmb]
    · funext v
      have := congrFun (congrFun ((blockEmb K t).map_adjugate G) (cy h v.2)) (Fin.rev v.1)
      simp only [AlgHom.mapMatrix_apply, Matrix.map_apply] at this
      rw [this]
      simp only [Function.comp_def, val_inr]
      congr 2
      ext1 b k
      simp [gen, G, blockEmb]
  · intro e
    let ev : MvPolynomial (Fin n × Fin n) K →ₐ[K] K := aeval fun v => if v.1 = v.2 then 1 else 0
    have := congrArg ev e
    rw [map_mul, ← AlgHom.comp_apply ev, ← AlgHom.comp_apply ev, comp_aeval, comp_aeval, hA, hB] at this
    · simp at this
    · intro v
      have h1 := congrFun (congrFun (ev.map_adjugate G) (cy h v.2)) (Fin.rev v.1)
      have h2 : ev.mapMatrix G = 1 := by
        ext b k
        simp [ev, G, Matrix.one_apply]
      rw [h2, Matrix.adjugate_one, AlgHom.mapMatrix_apply, Matrix.map_apply] at h1
      rw [h1, Matrix.one_apply]
      congr 1
      simp only [cy, Fin.ext_iff, Fin.val_rev, eq_iff_iff]
      have := v.1.2
      have := v.2.2
      omega
    · intro v
      simp [ev, cx, Fin.ext_iff]

theorem cof_surj (φ : K →+* ℂ) (a : Row Ix p q → ℕ) (ha : ∀ t, Antitone fun i => a (t, Sum.inl i))
    (hb : ∀ t, Antitone fun i => a (t, Sum.inr i)) (hμ : ∀ t, Antitone (mu h a t))
    {F : MvPolynomial (Ix × Fin n × Fin n) K} (hF : F ∈ tensorLat K K fun t => dualWeyl K n n (mu h a t)) :
    ∃ Q : MvPolynomial (Lt Ix p q n) K, Deg Prod.fst a Q ∧ Inv Q ∧ (∀ i, lp xl yl i Q = 0) ∧
      aeval (val h (gen K n)) Q = F := by
  haveI : CharZero K := φ.charZero
  suffices H : ∃ P : MvPolynomial (Lt Ix p q n) K, Deg Prod.fst a P ∧ Inv P ∧ aeval (val h (gen K n)) P = F by
    obtain ⟨P, h1, h2, rfl⟩ := H
    exact exists_harm_inv h φ h1 h2
  induction hF using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, hf, rfl⟩ := hx
    have := fun t => irr _ (hμ t) (NN h ℚ t a) (NN_le h t a) (NN_ne h t a (ha t) (hb t)) (NN_act h t a) (NN h K t a)
      (fun f hf => NN_map h t a hf) (hf t)
    choose P h1 h2 h3 using this
    refine ⟨∏ t, P t, ?_, ⟨fun s i j hij c => ?_, fun s i j hij c => ?_⟩, ?_⟩
    · convert IsWeightedHomogeneous.prod Finset.univ P (fun t => res t a) fun t _ => h1 t
      funext r
      simp [res]
    · rw [map_prod]
      exact Finset.prod_congr rfl fun t _ => (h2 t).1 s i j hij c
    · rw [map_prod]
      exact Finset.prod_congr rfl fun t _ => (h2 t).2 s i j hij c
    · rw [map_prod]
      exact Finset.prod_congr rfl fun t _ => h3 t
  | zero => exact ⟨0, isWeightedHomogeneous_zero _ _ _, ⟨fun _ _ _ _ _ => map_zero _, fun _ _ _ _ _ => map_zero _⟩, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨P, h1, h2, h3⟩ := hx
    obtain ⟨Q, k1, k2, k3⟩ := hy
    exact ⟨P + Q, h1.add k1, ⟨fun t i j hij c => by rw [map_add, h2.1 t i j hij, k2.1 t i j hij],
      fun t i j hij c => by rw [map_add, h2.2 t i j hij, k2.2 t i j hij]⟩, by rw [map_add, h3, k3]⟩
  | smul c x _ hx =>
    obtain ⟨P, h1, h2, h3⟩ := hx
    exact ⟨c • P, (weightedHomogeneousSubmodule K _ _).smul_mem c h1,
      ⟨fun t i j hij c => by rw [map_smul, h2.1 t i j hij], fun t i j hij c => by rw [map_smul, h2.2 t i j hij]⟩,
      by rw [map_smul, h3]⟩

def dd (K : Type) [Field K] (n : ℕ) : MvPolynomial (Fin n × Fin n) K := (Matrix.of fun a s => X (a, s)).det

theorem dd_pow_mem (e : ℕ) : dd K n ^ e ∈ dualWeyl K n n fun _ => e := by
  have := bidetMem K n n e (fun _ => n) (fun _ => le_rfl) (fun _ => id)
  have e1 : shapeDeg (n := n) (fun _ : Fin e => n) = fun _ => e := by
    funext t
    simp [shapeDeg]
  rw [e1] at this
  simpa [bideterminant, initMinor, dd] using this

theorem dd_mul_mem {ν μ : Fin n → ℕ} {e : ℕ} (hμ : ∀ k, ν k + e = μ k) {f : MvPolynomial (Fin n × Fin n) K}
    (hf : f ∈ dualWeyl K n n ν) : dd K n ^ e * f ∈ dualWeyl K n n μ := by
  convert (dualWeylMul K n n _ _ _ _).1 (dd_pow_mem e) hf
  funext k
  simp [← hμ, add_comm]

theorem rowAct_dd (g : Matrix (Fin n) (Fin n) K) : rowAct K g (dd K n) = C g.det * dd K n := by
  rw [dd, AlgHom.map_det, RingHom.map_det, ← Matrix.det_mul]
  congr 1
  ext1 a s
  simp [rowAct, Matrix.mul_apply]

theorem dd_ne : dd K n ≠ 0 := by
  intro e
  have := congrArg (eval fun v : Fin n × Fin n => if v.1 = v.2 then (1 : K) else 0) e
  rw [dd, RingHom.map_det, map_zero] at this
  refine one_ne_zero (α := K) (Eq.trans ?_ this)
  rw [← Matrix.det_one (n := Fin n)]
  congr 1
  ext a b
  simp [Matrix.one_apply]

theorem exists_dd_mul [CharZero K] {ν μ : Fin n → ℕ} {e : ℕ} (hν : Antitone ν) (hμ : ∀ k, ν k + e = μ k)
    {f : MvPolynomial (Fin n × Fin n) K} (hf : f ∈ dualWeyl K n n μ) : ∃ f' ∈ dualWeyl K n n ν, dd K n ^ e * f' = f := by
  have hμ' : Antitone μ := fun i j hij => by rw [← hμ, ← hμ]; exact Nat.add_le_add_right (hν hij) _
  refine irr μ hμ' ((dualWeyl ℚ n n ν).map (LinearMap.mulLeft ℚ (dd ℚ n ^ e))) ?_ ?_ ?_
    ((dualWeyl K n n ν).map (LinearMap.mulLeft K (dd K n ^ e))) ?_ hf
  · rintro _ ⟨f, hf, rfl⟩
    exact dd_mul_mem hμ hf
  · rw [Submodule.ne_bot_iff]
    exact ⟨_, ⟨_, hwMem ℚ n n le_rfl ν hν, rfl⟩, mul_ne_zero (pow_ne_zero _ dd_ne) (hwNe ℚ n n le_rfl ν)⟩
  · rintro g _ ⟨f, hf, rfl⟩
    refine ⟨_, Submodule.smul_mem _ ((g : Matrix (Fin n) (Fin n) ℚ).det ^ e) (dualWeylRowStable ℚ n n ν g f hf), ?_⟩
    simp only [LinearMap.mulLeft_apply, map_mul, map_pow, rowAct_dd, smul_eq_C_mul]
    ring
  · rintro _ ⟨f, hf, rfl⟩
    refine ⟨_, dualWeylMap ℚ K (algebraMap ℚ K) n n ν f hf, ?_⟩
    simp only [LinearMap.mulLeft_apply, map_mul, map_pow, dd, RingHom.map_det]
    congr 3
    ext1 a s
    simp

theorem emb_dd (t : Ix) : blockEmb K t (dd K n) = (gen K n t).det := by
  rw [dd, AlgHom.map_det]
  congr 1
  ext1 a s
  simp [gen, blockEmb]

theorem tensor_iff [CharZero K] {ν μ : Ix → Fin n → ℕ} {e : Ix → ℕ} (hν : ∀ t, Antitone (ν t))
    (hμ : ∀ t k, ν t k + e t = μ t k) (G : MvPolynomial (Ix × Fin n × Fin n) K) :
    G ∈ tensorLat K K (fun t => dualWeyl K n n (μ t)) ↔
      ∃ F ∈ tensorLat K K (fun t => dualWeyl K n n (ν t)), G = (∏ t, (gen K n t).det ^ e t) * F := by
  constructor
  · intro hG
    induction hG using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨f, hf, rfl⟩ := hx
      choose f' h1 h2 using fun t => exists_dd_mul (hν t) (hμ t) (hf t)
      refine ⟨_, Submodule.subset_span ⟨f', h1, rfl⟩, ?_⟩
      simp only [← h2, map_mul, map_pow, emb_dd, Finset.prod_mul_distrib]
    | zero => exact ⟨0, zero_mem _, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨F, h1, rfl⟩ := hx
      obtain ⟨F', h2, rfl⟩ := hy
      exact ⟨F + F', add_mem h1 h2, by ring⟩
    | smul c x _ hx =>
      obtain ⟨F, h1, rfl⟩ := hx
      exact ⟨c • F, Submodule.smul_mem _ _ h1, by simp⟩
  · rintro ⟨F, hF, rfl⟩
    induction hF using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨f, hf, rfl⟩ := hx
      refine Submodule.subset_span ⟨fun t => dd K n ^ e t * f t, fun t => dd_mul_mem (hμ t) (hf t), ?_⟩
      simp only [map_mul, map_pow, emb_dd, Finset.prod_mul_distrib]
    | zero => simp
    | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
    | smul c x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ hx

end Surj

section Main

open NumberField Formalism.GradedWeylDivisibility GlobalTheory.FrameRead Formalism.L2.DIV Formalism.L2.Pj Formalism.BasicNotions ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped Classical

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (Dw : Datum H) {n : ℕ} {Ix : Type} [Fintype Ix]
  {pl : Ix → (E →+* ℂ)} (he : IsEnum H pl)

theorem rt0_conj_neg_ne_zero (H : Host E) : starRingEnd ℂ H.rt0 = -H.rt0 ∧ H.rt0 ≠ 0 := by
  have h1 := H.sqrt_neg_disc_sq
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  have hre := congrArg Complex.re h1
  have him := congrArg Complex.im h1
  simp only [sq, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.natCast_re, Complex.natCast_im,
    neg_zero] at hre him
  have h0 : H.rt0.re = 0 := by
    by_contra h
    have : H.rt0.im = 0 := by
      have : H.rt0.re * H.rt0.im = 0 := by linarith
      exact (mul_eq_zero.1 this).resolve_left h
    rw [this] at hre
    nlinarith [mul_self_nonneg H.rt0.re]
  refine ⟨Complex.ext (by simp [h0]) (by simp), fun e => ?_⟩
  rw [e] at hre
  simp at hre
  exact H.d_prime.ne_zero hre

theorem not_psi_conj {τ : E →+* ℂ} (hτ : InPsi H τ) : ¬ InPsi H (ComplexEmbedding.conjugate τ) := by
  intro h2
  simp only [InPsi, ComplexEmbedding.conjugate_coe_eq] at hτ h2
  rw [hτ, (rt0_conj_neg_ne_zero H).1] at h2
  exact (rt0_conj_neg_ne_zero H).2 (by linear_combination (-1 / 2 : ℂ) * h2)

theorem psi_conj {τ : E →+* ℂ} (hτ : ¬ InPsi H τ) : InPsi H (ComplexEmbedding.conjugate τ) := by
  simp only [InPsi, ComplexEmbedding.conjugate_coe_eq] at hτ ⊢
  have h1 : ((H.rt : 𝓞 E) : E) ^ 2 = -(H.d : E) := by simpa using congrArg (algebraMap (𝓞 E) E) H.rt_sq
  have h2 : (τ (H.rt : E)) ^ 2 = H.rt0 ^ 2 := by rw [← map_pow, h1, H.sqrt_neg_disc_sq]; simp
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 h2 with h3 | h3
  · exact absurd h3 hτ
  · rw [h3, map_neg, (rt0_conj_neg_ne_zero H).1, neg_neg]

theorem conj_conj (τ : E →+* ℂ) : ComplexEmbedding.conjugate (ComplexEmbedding.conjugate τ) = τ := star_star τ

include he

theorem psi_pl (t : Ix) : InPsi H (pl t) := (he.2 _).2 ⟨t, rfl⟩

theorem mult_pl (t : Ix) : Dw.mult (pl t) = Dw.p := if_pos (psi_pl he t)

theorem mult_conj (t : Ix) : Dw.mult (ComplexEmbedding.conjugate (pl t)) = Dw.q := if_neg (not_psi_conj (psi_pl he t))

theorem pl_ne (s t : Ix) : pl s ≠ ComplexEmbedding.conjugate (pl t) := fun e =>
  not_psi_conj (psi_pl he t) (e ▸ psi_pl he s)

theorem conj_pl_inj {s t : Ix} (e : ComplexEmbedding.conjugate (pl s) = ComplexEmbedding.conjugate (pl t)) : s = t :=
  he.1 (by rw [← conj_conj (pl s), e, conj_conj])

theorem cover (σ : E →+* ℂ) : (∃ t, pl t = σ) ∨ ∃ t, ComplexEmbedding.conjugate (pl t) = σ := by
  by_cases h : InPsi H σ
  · exact Or.inl ((he.2 _).1 h)
  · obtain ⟨t, ht⟩ := (he.2 _).1 (psi_conj h)
    exact Or.inr ⟨t, by rw [ht, conj_conj]⟩

omit he in

def fw (he : IsEnum H pl) : Lt Ix Dw.p Dw.q n → LtN Dw n := fun ℓ =>
  Sum.elim (fun i => ⟨pl ℓ.1.1, Fin.cast (mult_pl Dw he _).symm i, ℓ.2⟩)
    (fun j => ⟨ComplexEmbedding.conjugate (pl ℓ.1.1), Fin.cast (mult_conj Dw he _).symm j, ℓ.2⟩) ℓ.1.2

theorem fw_inl (t : Ix) (i : Fin Dw.p) (b : Fin n) :
    fw Dw he ((t, Sum.inl i), b) = ⟨pl t, Fin.cast (mult_pl Dw he _).symm i, b⟩ := rfl

theorem fw_inr (t : Ix) (i : Fin Dw.q) (b : Fin n) :
    fw Dw he ((t, Sum.inr i), b) = ⟨ComplexEmbedding.conjugate (pl t), Fin.cast (mult_conj Dw he _).symm i, b⟩ := rfl

theorem fw_inj : Function.Injective (fw (n := n) Dw he) := by
  rintro ⟨⟨s, i | i⟩, b⟩ ⟨⟨t, j | j⟩, c⟩ e
  all_goals
    have h1 := congrArg (fun x : LtN Dw n => x.1) e
    have h2 := congrArg (fun x : LtN Dw n => (x.2.1 : ℕ)) e
    have h3 := congrArg (fun x : LtN Dw n => x.2.2) e
    simp only [fw_inl, fw_inr, Fin.val_cast] at h1 h2 h3
  · rw [he.1 h1, Fin.ext h2, h3]
  · exact absurd h1 (pl_ne he _ _)
  · exact absurd h1.symm (pl_ne he _ _)
  · rw [conj_pl_inj he h1, Fin.ext h2, h3]

theorem row_cover (σ : E →+* ℂ) (i : Fin (Dw.mult σ)) :
    ∃ ρ : Row Ix Dw.p Dw.q, ∀ b : Fin n, fw Dw he (ρ, b) = ⟨σ, i, b⟩ := by
  rcases cover he σ with ⟨t, rfl⟩ | ⟨t, rfl⟩
  · exact ⟨(t, Sum.inl (Fin.cast (mult_pl Dw he _) i)), fun _ => rfl⟩
  · exact ⟨(t, Sum.inr (Fin.cast (mult_conj Dw he _) i)), fun _ => rfl⟩

theorem fw_surj : Function.Surjective (fw (n := n) Dw he) := by
  rintro ⟨σ, i, b⟩
  obtain ⟨ρ, hρ⟩ := row_cover (n := n) Dw he σ i
  exact ⟨_, hρ b⟩

variable {K : Type} [Field K]

theorem cof_fw (h : Dw.p + Dw.q ≤ n) (P : MvPolynomial (Lt Ix Dw.p Dw.q n) K) :
    cof Dw pl K n (rename (fw Dw he) P) = aeval (val h (gen K n)) P := by
  rw [← AlgHom.comp_apply]
  congr 1
  apply algHom_ext
  rintro ⟨⟨t, i | i⟩, b⟩
  · have h1 : ∃ s, pl s = pl t := ⟨t, rfl⟩
    have h2 : h1.choose = t := he.1 h1.choose_spec
    have h3 : (i : ℕ) < n := by omega
    simp only [AlgHom.comp_apply, rename_X, cof, aeval_X, fw_inl, Fin.val_cast, h3, dif_pos, h1, h2, val_inl]
    rfl
  · have h0 : ¬ ∃ s, pl s = ComplexEmbedding.conjugate (pl t) := fun ⟨s, hs⟩ => pl_ne he _ _ hs
    have h1 : ∃ s, ComplexEmbedding.conjugate (pl s) = ComplexEmbedding.conjugate (pl t) := ⟨t, rfl⟩
    have h2 : h1.choose = t := conj_pl_inj he h1.choose_spec
    have h3 : (i : ℕ) < n := by omega
    simp only [AlgHom.comp_apply, rename_X, cof, aeval_X, fw_inr, Fin.val_cast, h3, dif_pos, h1, h2, val_inr, h0,
      dif_neg, not_false_eq_true]
    congr 1
    simp only [cy, Fin.ext_iff, Fin.val_rev]
    omega

theorem letAct_fw (g : Ix → GL (Fin n) K) (P : MvPolynomial (Lt Ix Dw.p Dw.q n) K) :
    letAct Dw pl K g (rename (fw Dw he) P) = rename (fw Dw he) (act g P) := by
  rw [← AlgHom.comp_apply, ← AlgHom.comp_apply]
  congr 1
  apply algHom_ext
  rintro ⟨⟨t, i | i⟩, b⟩
  · have h1 : ∃ s, pl s = pl t := ⟨t, rfl⟩
    have h2 : h1.choose = t := he.1 h1.choose_spec
    simp only [AlgHom.comp_apply, rename_X, letAct, aeval_X, fw_inl, dif_pos, h1, h2, act, map_sum, map_mul, rename_C]
    rfl
  · have h0 : ¬ ∃ s, pl s = ComplexEmbedding.conjugate (pl t) := fun ⟨s, hs⟩ => pl_ne he _ _ hs
    have h1 : ∃ s, ComplexEmbedding.conjugate (pl s) = ComplexEmbedding.conjugate (pl t) := ⟨t, rfl⟩
    have h2 : h1.choose = t := conj_pl_inj he h1.choose_spec
    simp only [AlgHom.comp_apply, rename_X, letAct, aeval_X, fw_inr, dif_pos, h1, h2, act, map_sum, map_mul, rename_C,
      h0, dif_neg, not_false_eq_true]
    rfl

theorem rowShift_fw {ρ ρ' : Row Ix Dw.p Dw.q} {σ : E →+* ℂ} {i i' : Fin (Dw.mult σ)}
    (h1 : ∀ b : Fin n, fw Dw he (ρ, b) = ⟨σ, i, b⟩) (h2 : ∀ b : Fin n, fw Dw he (ρ', b) = ⟨σ, i', b⟩) (c : K)
    (P : MvPolynomial (Lt Ix Dw.p Dw.q n) K) :
    rowShift Dw.mult n K σ i i' c (rename (fw Dw he) P) = rename (fw Dw he) (shift ρ ρ' c P) := by
  rw [← AlgHom.comp_apply, ← AlgHom.comp_apply]
  congr 1
  apply algHom_ext
  rintro ⟨r, b⟩
  simp only [AlgHom.comp_apply, rename_X, rowShift, shift, aeval_X, ← h1, (fw_inj Dw he).eq_iff, Prod.mk.injEq,
    exists_and_left, exists_eq', and_true]
  split_ifs with h3
  · subst h3
    simp only [map_add, map_mul, rename_X, rename_C, h2]
    rw [h1]
  · simp

theorem inv_fw (P : MvPolynomial (Lt Ix Dw.p Dw.q n) K) : RowInv Dw.mult n K (rename (fw Dw he) P) ↔ Inv P := by
  constructor
  · intro hP
    refine ⟨fun t i i' hi c => rename_injective _ (fw_inj Dw he) ?_, fun t i i' hi c => rename_injective _ (fw_inj Dw he) ?_⟩
    · rw [← rowShift_fw Dw he (fw_inl Dw he t i) (fw_inl Dw he t i')]
      exact hP _ _ _ hi c
    · rw [← rowShift_fw Dw he (fw_inr Dw he t i) (fw_inr Dw he t i')]
      exact hP _ _ _ hi c
  · intro hP σ i i' hi c
    rcases cover he σ with ⟨t, rfl⟩ | ⟨t, rfl⟩
    · rw [rowShift_fw Dw he (ρ := (t, Sum.inl (Fin.cast (mult_pl Dw he _) i)))
        (ρ' := (t, Sum.inl (Fin.cast (mult_pl Dw he _) i'))) (fun _ => rfl) (fun _ => rfl), hP.1 _ _ _ hi]
    · rw [rowShift_fw Dw he (ρ := (t, Sum.inr (Fin.cast (mult_conj Dw he _) i)))
        (ρ' := (t, Sum.inr (Fin.cast (mult_conj Dw he _) i'))) (fun _ => rfl) (fun _ => rfl), hP.2 _ _ _ hi]

omit he in

def aa (pl : Ix → (E →+* ℂ)) (a : (E →+* ℂ) × ℕ → ℕ) : Row Ix Dw.p Dw.q → ℕ := fun ρ =>
  Sum.elim (fun i : Fin Dw.p => a (pl ρ.1, i)) (fun j : Fin Dw.q => a (ComplexEmbedding.conjugate (pl ρ.1), j)) ρ.2

theorem deg_fw (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (Lt Ix Dw.p Dw.q n) K) :
    RowDeg Dw.mult n K (fun τ i => a (τ, i)) (rename (fw Dw he) P) ↔ Deg Prod.fst (aa Dw pl a) P := by
  have hw : ∀ (m : Lt Ix Dw.p Dw.q n →₀ ℕ) (ρ : Row Ix Dw.p Dw.q),
      Finsupp.weight (fun v : Lt Ix Dw.p Dw.q n => (Pi.single v.1 1 : Row Ix Dw.p Dw.q → ℕ)) m ρ =
        ∑ b, Finsupp.mapDomain (fw Dw he) m (fw Dw he (ρ, b)) := by
    intro m ρ
    rw [weight_apply, Fintype.sum_prod_type, Finset.sum_eq_single ρ]
    · simp [Finsupp.mapDomain_apply (fw_inj Dw he)]
    · intro r _ hr; simp [hr]
    · simp
  rw [RowDeg, support_rename_of_injective (fw_inj Dw he)]
  constructor
  · intro hP m hm
    funext ⟨t, i⟩
    have := hP _ (Finset.mem_image_of_mem _ (mem_support_iff.2 hm))
    rw [hw]
    rcases i with i | i
    · exact this (pl t) (Fin.cast (mult_pl Dw he _).symm i)
    · exact this (ComplexEmbedding.conjugate (pl t)) (Fin.cast (mult_conj Dw he _).symm i)
  · intro hP m hm σ i
    obtain ⟨m, hm', rfl⟩ := Finset.mem_image.1 hm
    have := congrFun (hP (mem_support_iff.1 hm'))
    simp only [hw] at this
    rcases cover he σ with ⟨t, rfl⟩ | ⟨t, rfl⟩
    · exact this (t, Sum.inl (Fin.cast (mult_pl Dw he _) i))
    · exact this (t, Sum.inr (Fin.cast (mult_conj Dw he _) i))

theorem lap_fw (t : Ix) (i : Fin Dw.p) (j : Fin Dw.q) (P : MvPolynomial (Lt Ix Dw.p Dw.q n) K) :
    lap Dw.mult n K 1 (pl t) (ComplexEmbedding.conjugate (pl t)) (Fin.cast (mult_pl Dw he _).symm i)
      (Fin.cast (mult_conj Dw he _).symm j) (rename (fw Dw he) P) = rename (fw Dw he) (lp xl yl (t, i, j) P) := by
  simp only [lap, lp, LinearMap.sum_apply, map_sum, LinearMap.smul_apply, LinearMap.comp_apply]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_eq_single b]
  · rw [Matrix.one_apply_eq, one_smul, ← pderiv_rename (fw_inj Dw he), ← pderiv_rename (fw_inj Dw he)]
    rfl
  · intro c _ hc
    rw [Matrix.one_apply_ne (Ne.symm hc), zero_smul]
  · simp

theorem harm_fw (P : MvPolynomial (Lt Ix Dw.p Dw.q n) K) :
    rename (fw Dw he) P ∈ harmK Dw.mult n K ComplexEmbedding.conjugate (InPsi H) (fun _ => 1) ↔
      ∀ i, lp xl yl i P = 0 := by
  simp only [harmK, Submodule.mem_iInf, LinearMap.mem_ker]
  constructor
  · rintro hP ⟨t, i, j⟩
    apply rename_injective _ (fw_inj Dw he)
    rw [← lap_fw, map_zero]
    exact hP _ (psi_pl he t) _ _
  · intro hP τ hτ i j
    obtain ⟨t, rfl⟩ := (he.2 _).1 hτ
    have := lap_fw Dw he t (Fin.cast (mult_pl Dw he _) i) (Fin.cast (mult_conj Dw he _) j) P
    rw [hP, map_zero] at this
    exact this

theorem degC_eq (a : (E →+* ℂ) × ℕ → ℕ) (t : Ix) : degC Dw pl a t = ∑ j, aa Dw pl a (t, Sum.inr j) := by
  unfold degC
  rw [Fin.sum_univ_eq_sum_range (fun i => a (ComplexEmbedding.conjugate (pl t), i)), mult_conj Dw he,
    ← Fin.sum_univ_eq_sum_range (fun i => a (ComplexEmbedding.conjugate (pl t), i))]
  rfl

theorem mu_eq (h : Dw.p + Dw.q ≤ n) {a : (E →+* ℂ) × ℕ → ℕ} {s : Ix → ℤ} {lam : Ix → DomWeight n}
    (hw : WtIs Dw pl a s lam) (t : Ix) (k : Fin n) :
    (mu h (aa Dw pl a) t k : ℤ) = (lam t).w k - s t + degC Dw pl a t := by
  rw [hw t k, mult_pl Dw he, mult_conj Dw he, degC_eq Dw he, mu]
  have h1 : (∑ i, if cx h i = k then aa Dw pl a (t, Sum.inl i) else 0) =
      if (k : ℕ) < Dw.p then a (pl t, k) else 0 := by
    split_ifs with hk
    · rw [Finset.sum_eq_single ⟨k, hk⟩]
      · exact if_pos rfl
      · intro i _ hi
        exact if_neg fun e => hi (Fin.ext (show (i : ℕ) = k from congrArg Fin.val e))
      · simp
    · refine Finset.sum_eq_zero fun i _ => if_neg fun e => hk ?_
      rw [← e]; exact i.2
  have h2 : (∑ j, if k = cy h j then aa Dw pl a (t, Sum.inr j) else 0) =
      if (Fin.rev k : ℕ) < Dw.q then a (ComplexEmbedding.conjugate (pl t), (Fin.rev k : ℕ)) else 0 := by
    have hk' := k.2
    split_ifs with hk
    · rw [Finset.sum_eq_single ⟨_, hk⟩]
      · exact if_pos (by simp only [cy, Fin.ext_iff, Fin.val_rev]; omega)
      · intro i _ hi
        refine if_neg fun e => hi ?_
        have := i.2
        simp only [cy, Fin.ext_iff, Fin.val_rev] at e ⊢
        omega
      · simp
    · refine Finset.sum_eq_zero fun i _ => if_neg fun e => hk ?_
      have := i.2
      simp only [cy, Fin.ext_iff, Fin.val_rev] at e ⊢
      omega
  have h3 : (∑ j, if k ≠ cy h j then aa Dw pl a (t, Sum.inr j) else 0) +
      (∑ j, if k = cy h j then aa Dw pl a (t, Sum.inr j) else 0) = ∑ j, aa Dw pl a (t, Sum.inr j) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases e : k = cy h j <;> simp [e]
  rw [h1, ← h3, h2]
  push_cast
  ring

omit he in
theorem shift_le (lam : DomWeight n) (k : Fin n) : lam.detShift ≤ lam.w k := by
  have hk := k.2
  rw [DomWeight.detShift, dif_pos (by omega)]
  exact lam.anti (by rw [Fin.le_def]; simp only; omega)

theorem exp_nonneg (h : Dw.p + Dw.q ≤ n) {a : (E →+* ℂ) × ℕ → ℕ} {s : Ix → ℤ} {lam : Ix → DomWeight n}
    (hw : WtIs Dw pl a s lam) (hn : 0 < n) (t : Ix) : 0 ≤ (degC Dw pl a t : ℤ) + (lam t).detShift - s t := by
  have := mu_eq Dw he h hw t ⟨n - 1, by omega⟩
  rw [DomWeight.detShift, dif_pos hn]
  omega

theorem natW_add (h : Dw.p + Dw.q ≤ n) {a : (E →+* ℂ) × ℕ → ℕ} {s : Ix → ℤ} {lam : Ix → DomWeight n}
    (hw : WtIs Dw pl a s lam) (t : Ix) (k : Fin n) :
    (lam t).natW k + ((degC Dw pl a t : ℤ) + (lam t).detShift - s t).toNat = mu h (aa Dw pl a) t k := by
  have h1 := mu_eq Dw he h hw t k
  have h2 := exp_nonneg Dw he h hw k.pos t
  have h3 := shift_le (lam t) k
  simp only [DomWeight.natW]
  omega

omit he in
theorem natW_anti (lam : DomWeight n) : Antitone lam.natW := by
  intro i j hij
  have := lam.anti hij
  simp only [DomWeight.natW]
  omega

theorem main_field (φ : K →+* ℂ) (h : Dw.p + Dw.q ≤ n) (a : (E →+* ℂ) × ℕ → ℕ) (s : Ix → ℤ) (lam : Ix → DomWeight n)
    (ha : ∀ τ : E →+* ℂ, Antitone fun i : ℕ => a (τ, i)) (hw : WtIs Dw pl a s lam) :
    (∀ P ∈ HHa Dw.mult n K ComplexEmbedding.conjugate (InPsi H) fun τ i => a (τ, i),
      ∃ F ∈ VV K lam, cof Dw pl K n P = detFac Dw pl K a s lam * F) ∧
    (∀ F ∈ VV K lam, ∃! P : MvPolynomial (Letter (E →+* ℂ) Dw.mult n) K,
      (P ∈ HHa Dw.mult n K ComplexEmbedding.conjugate (InPsi H) fun τ i => a (τ, i)) ∧
        cof Dw pl K n P = detFac Dw pl K a s lam * F) ∧
    ∀ g : Ix → GL (Fin n) K, ∀ P ∈ HHa Dw.mult n K ComplexEmbedding.conjugate (InPsi H) fun τ i => a (τ, i),
      ∀ F ∈ VV K lam, cof Dw pl K n P = detFac Dw pl K a s lam * F →
        cof Dw pl K n (letAct Dw pl K g P) =
          (∏ t : Ix, Matrix.det (Units.val (g t)) ^ (-s t)) • (detFac Dw pl K a s lam * actP lam g F) := by
  haveI : CharZero K := φ.charZero
  have hsurj : Function.Surjective (rename (R := K) (fw (n := n) Dw he)) := rename_surjective _ (fw_surj Dw he)
  have hmem : ∀ P : MvPolynomial (Lt Ix Dw.p Dw.q n) K,
      (rename (fw Dw he) P ∈ HHa Dw.mult n K ComplexEmbedding.conjugate (InPsi H) fun τ i => a (τ, i)) ↔
        (∀ i, lp xl yl i P = 0) ∧ Inv P ∧ Deg Prod.fst (aa Dw pl a) P := by
    intro P
    rw [← harm_fw Dw he, ← inv_fw Dw he, ← deg_fw Dw he]
    rfl
  have hT := tensor_iff (K := K) (fun t => natW_anti (lam t)) (natW_add Dw he h hw)
  refine ⟨?_, ?_, ?_⟩
  · intro P hP
    obtain ⟨P, rfl⟩ := hsurj P
    obtain ⟨-, h2, h3⟩ := (hmem P).1 hP
    rw [cof_fw Dw he h]
    exact (hT _).1 (cof_mem h h3 h2)
  · intro F hF
    obtain ⟨Q, h1, h2, h3, h4⟩ := cof_surj h φ (aa Dw pl a) (fun t i j hij => ha _ hij) (fun t i j hij => ha _ hij)
      (fun t i j hij => by
        rw [← natW_add Dw he h hw, ← natW_add Dw he h hw]
        exact Nat.add_le_add_right (natW_anti _ hij) _) ((hT _).2 ⟨F, hF, rfl⟩)
    refine ⟨rename (fw Dw he) Q, ⟨(hmem Q).2 ⟨h3, h2, h1⟩, by rw [cof_fw Dw he h, h4]; rfl⟩, ?_⟩
    rintro P ⟨hP, hP'⟩
    obtain ⟨P, rfl⟩ := hsurj P
    obtain ⟨k1, -, k3⟩ := (hmem P).1 hP
    rw [cof_fw Dw he h] at hP'
    congr 1
    rw [← sub_eq_zero]
    refine cof_inj h φ ((weightedHomogeneousSubmodule K _ _).sub_mem k3 h1) (fun i => ?_) ?_
    · have e1 := k1 i
      have e2 := h3 i
      simp only [lp, map_sub, Finset.sum_sub_distrib] at e1 e2 ⊢
      rw [e1, e2, sub_zero]
    · rw [map_sub, hP', h4]
      exact sub_self _
  · intro g P hP F _ hF
    obtain ⟨P, rfl⟩ := hsurj P
    obtain ⟨-, -, h3⟩ := (hmem P).1 hP
    rw [cof_fw Dw he h] at hF
    rw [letAct_fw, cof_fw Dw he h, cof_act h g h3, hF, map_mul]
    have e1 : trAct g (detFac Dw pl K a s lam) =
        (∏ t, (g t : Matrix (Fin n) (Fin n) K).det ^ ((degC Dw pl a t : ℤ) + (lam t).detShift - s t).toNat) •
          detFac Dw pl K a s lam := by
      simp only [detFac, ← emb_dd, map_prod, map_pow, trAct, (blockActTensor K K Ix n n _).1, rowAct_dd, map_mul,
        Matrix.det_transpose, smul_eq_C_mul, mul_pow, Finset.prod_mul_distrib, algHom_C, algebraMap_eq]
    rw [e1, actP, LinearMap.smul_apply, AlgHom.toLinearMap_apply, smul_mul_assoc, mul_smul_comm, smul_smul, smul_smul]
    congr 1
    rw [detTwK, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun t _ => ?_
    rw [detPow, Units.val_zpow_eq_zpow_val, Matrix.GeneralLinearGroup.val_det_apply, ← degC_eq Dw he]
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      simp
    · have h0 : (g t : Matrix (Fin n) (Fin n) K).det ≠ 0 := (g t).det_ne_zero
      rw [inv_pow, ← zpow_natCast, ← zpow_natCast, ← zpow_neg, ← zpow_add₀ h0, ← zpow_add₀ h0,
        Int.toNat_of_nonneg (exp_nonneg Dw he h hw hn t)]
      congr 1
      ring

end Main

theorem main : ∀ (E : Type) [inst : Field E] [inst_1 : NumberField E] [inst_2 : NumberField.IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (n : ℕ) (Ix : Type) [inst_3 : Fintype Ix] (pl : Ix → E →+* ℂ), GlobalTheory.FrameRead.IsEnum H pl → ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum.p Dw + ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum.q Dw ≤ n → ∀ (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l) (a : (E →+* ℂ) × ℕ → ℕ) (s : Ix → ℤ) (lam : Ix → Formalism.BasicNotions.DomWeight n), (∀ (τ : E →+* ℂ), Antitone fun (i : ℕ) ↦ a (τ, i)) → GlobalTheory.FrameRead.WtIs Dw pl a s lam → (∀ P ∈ Formalism.L2.Pj.HHa (ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum.mult Dw) n (↥(ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff.F c)) NumberField.ComplexEmbedding.conjugate (Formalism.L2.Pj.InPsi H) fun (τ : E →+* ℂ) (i : ℕ) ↦ a (τ, i), ∃ F ∈ Formalism.L2.DIV.VV (↥(ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff.F c)) lam, DFunLike.coe (GlobalTheory.FrameRead.cof Dw pl (↥(ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff.F c)) n) P = GlobalTheory.FrameRead.detFac Dw pl (↥(ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff.F c)) a s lam * F) ∧ (∀ F ∈ Formalism.L2.DIV.VV (↥(ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff.F c)) lam, ∃! P : MvPolynomial (Formalism.L2.Pj.Letter (E →+* ℂ) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum.mult Dw) n) ↥(ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff.F c), (P ∈ Formalism.L2.Pj.HHa (ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum.mult Dw) n (↥(ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff.F c)) NumberField.ComplexEmbedding.conjugate (Formalism.L2.Pj.InPsi H) fun (τ : E →+* ℂ) (i : ℕ) ↦ a (τ, i)) ∧ DFunLike.coe (GlobalTheory.FrameRead.cof Dw pl (↥(ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff.F c)) n) P = GlobalTheory.FrameRead.detFac Dw pl (↥(ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff.F c)) a s lam * F) ∧ ∀ (g : Ix → GL (Fin n) ↥(ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff.F c)), ∀ P ∈ Formalism.L2.Pj.HHa (ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum.mult Dw) n (↥(ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff.F c)) NumberField.ComplexEmbedding.conjugate (Formalism.L2.Pj.InPsi H) fun (τ : E →+* ℂ) (i : ℕ) ↦ a (τ, i), ∀ F ∈ Formalism.L2.DIV.VV (↥(ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff.F c)) lam, DFunLike.coe (GlobalTheory.FrameRead.cof Dw pl (↥(ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff.F c)) n) P = GlobalTheory.FrameRead.detFac Dw pl (↥(ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff.F c)) a s lam * F → DFunLike.coe (GlobalTheory.FrameRead.cof Dw pl (↥(ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff.F c)) n) (DFunLike.coe (GlobalTheory.FrameRead.letAct Dw pl (↥(ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff.F c)) g) P) = (∏ t : Ix, Matrix.det (Units.val (g t)) ^ (-s t)) • (GlobalTheory.FrameRead.detFac Dw pl (↥(ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff.F c)) a s lam * DFunLike.coe (Formalism.L2.DIV.actP lam g) F) :=
  fun _ _ _ _ _ Dw _ _ _ _ he h _ c a s lam ha hw =>
    main_field Dw he (c.F.val : c.F →+* ℂ) h a s lam ha hw

end GlobalTheory.WeightOrderLemmas
