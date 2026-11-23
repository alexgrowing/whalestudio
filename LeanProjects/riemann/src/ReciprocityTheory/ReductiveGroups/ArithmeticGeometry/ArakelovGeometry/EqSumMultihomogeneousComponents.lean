import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.DoubleBlock

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def i2bdeg (m : (Σ k, ι k) →₀ ℕ) : K → ℕ := fun k => ∑ i, m ⟨k, i⟩

theorem i2bdeg_add (m n : (Σ k, ι k) →₀ ℕ) : i2bdeg (m + n) = i2bdeg m + i2bdeg n := by
  funext k
  simp [i2bdeg, Finset.sum_add_distrib]

open Classical in

def i2comp (a : K → ℕ) (h : MRing ι) : MRing ι :=
  ∑ m ∈ h.support.filter (fun m => i2bdeg m = a), monomial m (coeff m h)

open Classical in
theorem coeff_i2comp (a : K → ℕ) (h : MRing ι) (m : (Σ k, ι k) →₀ ℕ) :
    coeff m (i2comp a h) = if i2bdeg m = a then coeff m h else 0 := by
  unfold i2comp
  rw [coeff_sum]
  simp only [coeff_monomial]
  rw [Finset.sum_ite_eq']
  by_cases h0 : coeff m h = 0 <;> by_cases e : i2bdeg m = a <;> simp [Finset.mem_filter, mem_support_iff, h0, e]

theorem isMultiHomog_iff_coeff (s : MRing ι) (a : K → ℕ) :
    IsMultiHomog s a ↔ ∀ m, coeff m s ≠ 0 → i2bdeg m = a := by
  constructor
  · intro h m hm
    funext k
    exact h m (mem_support_iff.mpr hm) k
  · intro h m hm k
    exact congrFun (h m (mem_support_iff.mp hm)) k

def i2compHom (a : K → ℕ) : MRing ι →+ MRing ι where
  toFun := i2comp a
  map_zero' := by
    classical
    ext m
    rw [coeff_i2comp]
    simp
  map_add' x y := by
    classical
    ext m
    rw [coeff_add, coeff_i2comp, coeff_i2comp, coeff_i2comp, coeff_add]
    split_ifs <;> simp

theorem i2comp_add (a : K → ℕ) (x y : MRing ι) : i2comp a (x + y) = i2comp a x + i2comp a y :=
  (i2compHom a).map_add x y

theorem i2comp_zero (a : K → ℕ) : i2comp a (0 : MRing ι) = 0 := (i2compHom a).map_zero

theorem isMultiHomog_i2comp (a : K → ℕ) (h : MRing ι) : IsMultiHomog (i2comp a h) a := by
  classical
  rw [isMultiHomog_iff_coeff]
  intro m hm
  rw [coeff_i2comp] at hm
  by_contra e
  exact hm (if_neg e)

theorem i2comp_of_homog {a b : K → ℕ} {h : MRing ι} (hh : IsMultiHomog h b) :
    i2comp a h = if b = a then h else 0 := by
  classical
  rw [isMultiHomog_iff_coeff] at hh
  ext m
  rw [coeff_i2comp]
  by_cases hm : coeff m h = 0
  · split_ifs <;> simp [hm]
  · have := hh m hm
    subst this
    split_ifs <;> simp_all

theorem i2comp_self {a : K → ℕ} {h : MRing ι} (hh : IsMultiHomog h a) : i2comp a h = h := by
  rw [i2comp_of_homog hh, if_pos rfl]

theorem eq_sum_multihomogeneous_components (r : MRing ι) :
    r = ∑ b ∈ r.support.image i2bdeg, i2comp b r := by
  classical
  ext m
  rw [coeff_sum]
  simp_rw [coeff_i2comp]
  rw [Finset.sum_ite_eq]
  split_ifs with hm
  · rfl
  · by_contra hne
    exact hm (Finset.mem_image_of_mem _ (mem_support_iff.mpr hne))

theorem mem_mHom_iff (s : MRing ι) (a : K → ℕ) : s ∈ mHom ι a ↔ IsMultiHomog s a := by
  constructor
  · intro hs
    induction hs using Submodule.span_induction with
    | mem x hx => exact hx
    | zero => intro m hm; simp at hm
    | add x y _ _ hx hy =>
      rw [isMultiHomog_iff_coeff] at hx hy ⊢
      intro m hm
      rw [coeff_add] at hm
      by_cases h0 : coeff m x = 0
      · rw [h0, zero_add] at hm
        exact hy m hm
      · exact hx m h0
    | smul n x _ hx =>
      rw [isMultiHomog_iff_coeff] at hx ⊢
      intro m hm
      rw [coeff_smul] at hm
      exact hx m (fun h0 => hm (by rw [h0, smul_zero]))
  · intro hs
    exact Submodule.subset_span hs

theorem isMultiHomog_mul' {f g : MRing ι} {a b : K → ℕ} (hf : IsMultiHomog f a)
    (hg : IsMultiHomog g b) : IsMultiHomog (f * g) (a + b) := by
  classical
  rw [isMultiHomog_iff_coeff] at hf hg ⊢
  intro m hm
  rw [coeff_mul] at hm
  obtain ⟨x, hx, hx0⟩ := Finset.exists_ne_zero_of_sum_ne_zero hm
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
  rw [← hx, i2bdeg_add, hf x.1 (left_ne_zero_of_mul hx0), hg x.2 (right_ne_zero_of_mul hx0)]

theorem i2bdeg_apply_add (m n : (Σ k, ι k) →₀ ℕ) (k : K) :
    i2bdeg (m + n) k = i2bdeg m k + i2bdeg n k := by
  simp [i2bdeg, Finset.sum_add_distrib]

open Classical in
theorem i2comp_mul_right {f : MRing ι} {c : K → ℕ} (hf : IsMultiHomog f c) (a : K → ℕ)
    (g : MRing ι) : i2comp a (g * f) = if c ≤ a then i2comp (a - c) g * f else 0 := by
  rw [isMultiHomog_iff_coeff] at hf
  ext m
  rw [coeff_i2comp]
  split_ifs with hm hca hca
  · rw [coeff_mul, coeff_mul]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
    rw [coeff_i2comp]
    by_cases h0 : coeff x.2 f = 0
    · simp [h0]
    · have e2 := hf x.2 h0
      have e : i2bdeg x.1 = a - c := by
        funext k
        have h1 := i2bdeg_apply_add x.1 x.2 k
        rw [hx] at h1
        have h2 := congrFun hm k
        have h3 := congrFun e2 k
        simp only [Pi.sub_apply]
        rw [← h2, h1, h3, Nat.add_sub_cancel]
      rw [if_pos e]
  · rw [coeff_zero, coeff_mul]
    refine Finset.sum_eq_zero fun x hx => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
    by_cases h0 : coeff x.2 f = 0
    · simp [h0]
    · exfalso
      apply hca
      have e2 := hf x.2 h0
      intro k
      have h1 := i2bdeg_apply_add x.1 x.2 k
      rw [hx] at h1
      have h2 := congrFun hm k
      have h3 := congrFun e2 k
      rw [← h2, h1, h3]
      exact Nat.le_add_left _ _
  · rw [coeff_mul]
    refine (Finset.sum_eq_zero fun x hx => ?_).symm
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
    rw [coeff_i2comp]
    by_cases h0 : coeff x.2 f = 0
    · simp [h0]
    · by_cases e : i2bdeg x.1 = a - c
      · exfalso
        apply hm
        funext k
        have h1 := i2bdeg_apply_add x.1 x.2 k
        rw [hx] at h1
        have h2 := congrFun e k
        have h3 := congrFun (hf x.2 h0) k
        have h4 := hca k
        simp only [Pi.sub_apply] at h2
        rw [h1, h2, h3, Nat.sub_add_cancel h4]
      · simp [e]
  · simp

open Classical in
theorem i2comp_mem {F : Ideal (MRing ι)} (hF : IsMultiHomogIdeal F) (a : K → ℕ) {u : MRing ι}
    (hu : u ∈ F) : i2comp a u ∈ F := by
  classical
  obtain ⟨S, hS, rfl⟩ := hF
  revert a
  induction hu using Submodule.span_induction with
  | mem x hx =>
    intro a
    obtain ⟨b, hb⟩ := hS x hx
    rw [i2comp_of_homog hb]
    split_ifs
    · exact Ideal.subset_span hx
    · exact zero_mem _
  | zero => intro a; rw [i2comp_zero]; exact zero_mem _
  | add x y _ _ hx hy => intro a; rw [i2comp_add]; exact add_mem (hx a) (hy a)
  | smul r x _ hx =>
    intro a
    rw [smul_eq_mul, eq_sum_multihomogeneous_components r, Finset.sum_mul]
    have : i2comp a (∑ b ∈ r.support.image i2bdeg, i2comp b r * x) =
        ∑ b ∈ r.support.image i2bdeg, i2comp a (i2comp b r * x) := map_sum (i2compHom a) _ _
    rw [this]
    refine Ideal.sum_mem _ fun b _ => ?_
    rw [mul_comm, i2comp_mul_right (isMultiHomog_i2comp b r)]
    split_ifs
    · exact Ideal.mul_mem_right _ _ (hx _)
    · exact zero_mem _

theorem isMultiHomogIdeal_sup_span {F : Ideal (MRing ι)} (hF : IsMultiHomogIdeal F) {f : MRing ι}
    {c : K → ℕ} (hf : IsMultiHomog f c) : IsMultiHomogIdeal (F ⊔ Ideal.span {f}) := by
  obtain ⟨S, hS, rfl⟩ := hF
  refine ⟨S ∪ {f}, fun g hg => ?_, (Ideal.span_union S {f}).symm⟩
  rcases hg with hg | hg
  · exact hS g hg
  · rw [Set.mem_singleton_iff] at hg
    exact ⟨c, hg ▸ hf⟩

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
