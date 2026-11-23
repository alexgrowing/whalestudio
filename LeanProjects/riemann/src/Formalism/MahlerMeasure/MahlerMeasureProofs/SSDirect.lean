import Formalism.MahlerMeasure.LevelLattice

namespace Formalism.GM.M.SSD

open MvPolynomial Finset

section Gen
variable {σ ι K : Type} [CommRing K] [Nontrivial K] [DecidableEq σ] (sv : ι → σ)

def sd (m : σ →₀ ℕ) : ι → ℕ := fun k => m (sv k)

omit [Nontrivial K] in
lemma sd_add (m m' : σ →₀ ℕ) : sd sv (m + m') = sd sv m + sd sv m' := by
  funext k; simp [sd]

def SFree (f : MvPolynomial σ K) : Prop := ∀ m ∈ f.support, sd sv m = 0

def Good (f : MvPolynomial σ K) (a : ι → ℕ) (s : σ →₀ ℕ) : Prop :=
  sd sv s = a ∧ ∀ m ∈ (f - monomial s 1).support, sd sv m ≤ a ∧ sd sv m ≠ a

lemma le_add_eq {x y a b : ι → ℕ} (hx : x ≤ a) (hy : y ≤ b) (h : x + y = a + b) : x = a := by
  funext k
  have h1 : x k ≤ a k := hx k
  have h2 : y k ≤ b k := hy k
  have h3 := congrFun h k
  simp only [Pi.add_apply] at h3
  omega

omit [Nontrivial K] in
lemma mem_support_mul {f g : MvPolynomial σ K} {m : σ →₀ ℕ} (hm : m ∈ (f * g).support) :
    ∃ u ∈ f.support, ∃ w ∈ g.support, m = u + w := by
  have := support_mul f g hm
  rw [Finset.mem_add] at this
  obtain ⟨u, hu, w, hw, rfl⟩ := this
  exact ⟨u, hu, w, hw, rfl⟩

omit [Nontrivial K] in
lemma mem_support_add {f g : MvPolynomial σ K} {m : σ →₀ ℕ} (hm : m ∈ (f + g).support) :
    m ∈ f.support ∨ m ∈ g.support := by
  have := support_add hm
  simpa [Finset.mem_union] using this

lemma mem_support_monomial_one {s m : σ →₀ ℕ} (hm : m ∈ (monomial s (1 : K)).support) : m = s := by
  have := support_monomial_subset hm
  simpa using this

lemma Good.mul {f g : MvPolynomial σ K} {a b : ι → ℕ} {s s' : σ →₀ ℕ}
    (hf : Good sv f a s) (hg : Good sv g b s') : Good sv (f * g) (a + b) (s + s') := by
  refine ⟨by rw [sd_add, hf.1, hg.1], ?_⟩
  intro m hm
  have hid : f * g - monomial (s + s') 1 =
      monomial s 1 * (g - monomial s' 1) + (f - monomial s 1) * monomial s' 1 +
        (f - monomial s 1) * (g - monomial s' 1) := by
    have : (monomial (s + s') (1 : K)) = monomial s 1 * monomial s' 1 := by
      rw [monomial_mul, mul_one]
    rw [this]; ring
  rw [hid] at hm
  rcases mem_support_add hm with hm | hm
  · rcases mem_support_add hm with hm | hm
    · obtain ⟨u, hu, w, hw, rfl⟩ := mem_support_mul hm
      rw [mem_support_monomial_one hu] at *
      obtain ⟨h1, h2⟩ := hg.2 w hw
      rw [sd_add, hf.1]
      refine ⟨add_le_add le_rfl h1, fun h => h2 (add_left_cancel h)⟩
    · obtain ⟨u, hu, w, hw, rfl⟩ := mem_support_mul hm
      rw [mem_support_monomial_one hw] at *
      obtain ⟨h1, h2⟩ := hf.2 u hu
      rw [sd_add, hg.1]
      refine ⟨add_le_add h1 le_rfl, fun h => h2 (add_right_cancel h)⟩
  · obtain ⟨u, hu, w, hw, rfl⟩ := mem_support_mul hm
    obtain ⟨h1, h2⟩ := hf.2 u hu
    obtain ⟨h3, _⟩ := hg.2 w hw
    rw [sd_add]
    exact ⟨add_le_add h1 h3, fun h => h2 (le_add_eq h1 h3 h)⟩

lemma Good.one : Good sv (1 : MvPolynomial σ K) 0 0 := by
  refine ⟨by funext k; simp [sd], ?_⟩
  intro m hm
  have : (1 : MvPolynomial σ K) - monomial 0 1 = 0 := by rw [← C_1, ← monomial_zero']; simp
  rw [this] at hm; simp at hm

lemma Good.pow {f : MvPolynomial σ K} {a : ι → ℕ} {s : σ →₀ ℕ} (hf : Good sv f a s) (n : ℕ) :
    Good sv (f ^ n) (n • a) (n • s) := by
  induction n with
  | zero => simpa using Good.one sv
  | succ n ih => rw [pow_succ, succ_nsmul, succ_nsmul]; exact ih.mul sv hf

lemma Good.prod {α : Type} (u : Finset α) (f : α → MvPolynomial σ K) (a : α → ι → ℕ) (s : α → σ →₀ ℕ)
    (h : ∀ i ∈ u, Good sv (f i) (a i) (s i)) :
    Good sv (∏ i ∈ u, f i) (∑ i ∈ u, a i) (∑ i ∈ u, s i) := by
  classical
  induction u using Finset.induction_on with
  | empty => simpa using Good.one sv
  | insert i u hi ih =>
    rw [prod_insert hi, sum_insert hi, sum_insert hi]
    exact (h i (mem_insert_self _ _)).mul sv (ih fun k hk => h k (mem_insert_of_mem hk))

omit [Nontrivial K] in
lemma SFree.mul {f g : MvPolynomial σ K} (hf : SFree sv f) (hg : SFree sv g) : SFree sv (f * g) := by
  intro m hm
  obtain ⟨u, hu, w, hw, rfl⟩ := mem_support_mul hm
  rw [sd_add, hf u hu, hg w hw, add_zero]

omit [Nontrivial K] in
lemma SFree.add {f g : MvPolynomial σ K} (hf : SFree sv f) (hg : SFree sv g) : SFree sv (f + g) := by
  intro m hm
  rcases mem_support_add hm with h | h
  · exact hf m h
  · exact hg m h

omit [Nontrivial K] in
lemma SFree.C (c : K) : SFree sv (C c : MvPolynomial σ K) := by
  classical
  intro m hm
  rw [support_C] at hm
  split_ifs at hm
  · simp at hm
  · rw [Finset.mem_singleton] at hm; subst hm; funext k; simp [sd]

lemma SFree.X {v : σ} (hv : ∀ k, v ≠ sv k) : SFree sv (X v : MvPolynomial σ K) := by
  intro m hm
  rw [support_X, Finset.mem_singleton] at hm
  subst hm
  funext k; simp [sd, hv k]

omit [Nontrivial K] in
lemma SFree.sum {α : Type} (u : Finset α) (f : α → MvPolynomial σ K) (h : ∀ i ∈ u, SFree sv (f i)) :
    SFree sv (∑ i ∈ u, f i) := by
  classical
  induction u using Finset.induction_on with
  | empty => simpa using SFree.C sv (0 : K)
  | insert i u hi ih =>
    rw [sum_insert hi]
    exact (h i (mem_insert_self _ _)).add sv (ih fun k hk => h k (mem_insert_of_mem hk))

omit [Nontrivial K] in
lemma SFree.prod {α : Type} (u : Finset α) (f : α → MvPolynomial σ K) (h : ∀ i ∈ u, SFree sv (f i)) :
    SFree sv (∏ i ∈ u, f i) := by
  classical
  induction u using Finset.induction_on with
  | empty => simpa using SFree.C sv (1 : K)
  | insert i u hi ih =>
    rw [prod_insert hi]
    exact (h i (mem_insert_self _ _)).mul sv (ih fun k hk => h k (mem_insert_of_mem hk))

omit [Nontrivial K] in
lemma SFree.pow {f : MvPolynomial σ K} (hf : SFree sv f) (n : ℕ) : SFree sv (f ^ n) := by
  induction n with
  | zero => simpa using SFree.C sv (1 : K)
  | succ n ih => rw [pow_succ]; exact ih.mul sv hf

lemma SFree.rename {τ : Type} (e : τ → σ) (he : ∀ x k, e x ≠ sv k) (y : MvPolynomial τ K) :
    SFree sv (rename e y) := by
  induction y using MvPolynomial.induction_on with
  | C a => rw [rename_C]; exact SFree.C sv a
  | add f g hf hg => rw [map_add]; exact hf.add sv hg
  | mul_X f x hf => rw [map_mul, rename_X]; exact hf.mul sv (SFree.X sv (he x))

lemma Good.mul_sfree {f Q : MvPolynomial σ K} {a : ι → ℕ} {s : σ →₀ ℕ} (hf : Good sv f a s)
    (hQ : SFree sv Q) :
    (∀ m ∈ (f * Q).support, sd sv m ≤ a) ∧ (∀ n, coeff (s + n) (f * Q) = coeff n Q) := by
  have hid : f * Q = monomial s 1 * Q + (f - monomial s 1) * Q := by ring
  have hR : ∀ m ∈ ((f - monomial s 1) * Q).support, sd sv m ≤ a ∧ sd sv m ≠ a := by
    intro m hm
    obtain ⟨u, hu, w, hw, rfl⟩ := mem_support_mul hm
    rw [sd_add, hQ w hw, add_zero]; exact hf.2 u hu
  refine ⟨?_, ?_⟩
  · intro m hm
    rw [hid] at hm
    rcases mem_support_add hm with hm | hm
    · obtain ⟨u, hu, w, hw, rfl⟩ := mem_support_mul hm
      rw [mem_support_monomial_one hu, sd_add, hQ w hw, add_zero, hf.1]
    · exact (hR m hm).1
  · intro n
    rw [hid, coeff_add, coeff_monomial_mul, one_mul]
    by_cases hn : n ∈ Q.support
    · have hz : coeff (s + n) ((f - monomial s 1) * Q) = 0 := by
        by_contra h
        have := hR _ (mem_support_iff.mpr h)
        rw [sd_add, hQ n hn, add_zero, hf.1] at this
        exact this.2 rfl
      rw [hz, add_zero]
    · rw [notMem_support_iff.mp hn]
      by_contra h
      rw [zero_add] at h
      obtain ⟨h1, h2⟩ := hR _ (mem_support_iff.mpr h)
      rw [sd_add, hf.1] at h1 h2
      apply h2
      exact le_antisymm h1 (fun k => Nat.le_add_right _ _)

end Gen

end Formalism.GM.M.SSD

namespace Formalism.GM.M.SSD

open MvPolynomial Finset

section Abs
variable {σ ι K ι' : Type} [Field K] [DecidableEq σ] [Fintype ι] (sv : ι → σ)

lemma eq_of_le_sum {x y : ι → ℕ} (h : x ≤ y) (hs : ∑ k, y k ≤ ∑ k, x k) : x = y := by
  have hle : ∀ k ∈ (univ : Finset ι), x k ≤ y k := fun k _ => h k
  have := (Finset.sum_eq_sum_iff_of_le hle).mp (le_antisymm (Finset.sum_le_sum hle) hs)
  funext k; exact this k (mem_univ k)

lemma topcoeff (a : ι' → ι → ℕ) (ha : Function.Injective a) (P : ι' → MvPolynomial σ K → Prop)
    (h1 : ∀ L v, P L v → ∀ m ∈ v.support, sd sv m ≤ a L)
    (s : Finset ι') (v : ι' → MvPolynomial σ K) (hv : ∀ L ∈ s, P L (v L)) (L : ι') (hL : L ∈ s)
    (hmax : ∀ L' ∈ s, ∑ k, a L' k ≤ ∑ k, a L k) (m : σ →₀ ℕ) (hm : sd sv m = a L) :
    coeff m (∑ L' ∈ s, v L') = coeff m (v L) := by
  rw [coeff_sum, Finset.sum_eq_single L]
  · intro L' hL' hne'
    by_contra hc'
    have hle := h1 L' (v L') (hv L' hL') m (mem_support_iff.mpr hc')
    rw [hm] at hle
    exact hne' (ha (eq_of_le_sum hle (hmax L' hL')).symm)
  · intro h; exact absurd hL h

theorem absDirect (V : ι' → Submodule K (MvPolynomial σ K)) (a : ι' → ι → ℕ) (ha : Function.Injective a)
    (h1 : ∀ L, ∀ v ∈ V L, ∀ m ∈ v.support, sd sv m ≤ a L)
    (h2 : ∀ L, ∀ v ∈ V L, (∀ m, sd sv m = a L → coeff m v = 0) → v = 0) : iSupIndep V := by
  classical
  rw [iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero]
  intro s
  refine Finset.strongInduction (p := fun s => ∀ (v : ι' → MvPolynomial σ K), (∀ i ∈ s, v i ∈ V i) →
    ∑ i ∈ s, v i = 0 → ∀ i ∈ s, v i = 0) (fun s ih => ?_) s
  intro v hv hsum
  rcases s.eq_empty_or_nonempty with rfl | hne
  · simp
  obtain ⟨L, hL, hmax⟩ := s.exists_max_image (fun L => ∑ k, a L k) hne
  have key : v L = 0 := by
    apply h2 L (v L) (hv L hL)
    intro m hm
    have := topcoeff sv a ha (fun L v => v ∈ V L) h1 s v hv L hL hmax m hm
    rw [hsum, coeff_zero] at this
    exact this.symm
  have hrest : ∀ i ∈ s.erase L, v i = 0 :=
    ih (s.erase L) (Finset.erase_ssubset hL) v (fun i hi => hv i (mem_of_mem_erase hi))
      (by rw [← Finset.add_sum_erase s v hL, key, zero_add] at hsum; exact hsum)
  intro i hi
  by_cases hiL : i = L
  · subst hiL; exact key
  · exact hrest i (mem_erase.mpr ⟨hiL, hi⟩)

theorem absSat (V : ι' → Submodule K (MvPolynomial σ K)) (a : ι' → ι → ℕ) (ha : Function.Injective a)
    (C : AddSubgroup K) (T : AddSubgroup (MvPolynomial σ K))
    (h1 : ∀ L, ∀ v ∈ V L, ∀ m ∈ v.support, sd sv m ≤ a L)
    (hT : ∀ f ∈ T, ∀ m, coeff m f ∈ C)
    (h2 : ∀ L, ∀ v ∈ V L, (∀ m, sd sv m = a L → coeff m v ∈ C) → v ∈ T)
    (s : Finset ι') (v : ι' → MvPolynomial σ K) (hv : ∀ L ∈ s, v L ∈ V L)
    (hC : ∀ m, coeff m (∑ L ∈ s, v L) ∈ C) : ∑ L ∈ s, v L ∈ T := by
  classical
  induction s using Finset.strongInduction with
  | H s ih =>
  rcases s.eq_empty_or_nonempty with rfl | hne
  · simp
  obtain ⟨L, hL, hmax⟩ := s.exists_max_image (fun L => ∑ k, a L k) hne
  have key : v L ∈ T := by
    apply h2 L (v L) (hv L hL)
    intro m hm
    rw [← topcoeff sv a ha (fun L v => v ∈ V L) h1 s v hv L hL hmax m hm]
    exact hC m
  have hsplit := Finset.add_sum_erase s v hL
  have hrest : ∑ i ∈ s.erase L, v i ∈ T := by
    apply ih (s.erase L) (Finset.erase_ssubset hL) (fun i hi => hv i (mem_of_mem_erase hi))
    intro m
    have : ∑ i ∈ s.erase L, v i = ∑ i ∈ s, v i - v L := by rw [← hsplit]; ring
    rw [this, coeff_sub]
    exact C.sub_mem (hC m) (hT _ key m)
  rw [← hsplit]
  exact T.add_mem key hrest

end Abs

end Formalism.GM.M.SSD

namespace Formalism.GM.M.SSD

open MvPolynomial Finset

section Kap
variable {σ τ K : Type} [Field K] [DecidableEq σ]

noncomputable def kap (F : (τ →₀ ℕ) → (σ →₀ ℕ)) (hF : Function.Injective F) (Q : MvPolynomial σ K) :
    MvPolynomial τ K :=
  ∑ n ∈ Q.support.preimage F hF.injOn, monomial n (coeff (F n) Q)

lemma coeff_kap (F : (τ →₀ ℕ) → (σ →₀ ℕ)) (hF : Function.Injective F) (Q : MvPolynomial σ K) (n : τ →₀ ℕ) :
    coeff n (kap F hF Q) = coeff (F n) Q := by
  classical
  rw [kap, coeff_sum]
  simp only [coeff_monomial]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [Finset.mem_preimage, mem_support_iff, not_not] at h; exact h.symm

lemma kap_add (F : (τ →₀ ℕ) → (σ →₀ ℕ)) (hF : Function.Injective F) (Q Q' : MvPolynomial σ K) :
    kap F hF (Q + Q') = kap F hF Q + kap F hF Q' := by
  ext n; simp only [coeff_kap, coeff_add]

lemma kap_smul (F : (τ →₀ ℕ) → (σ →₀ ℕ)) (hF : Function.Injective F) (c : K) (Q : MvPolynomial σ K) :
    kap F hF (c • Q) = c • kap F hF Q := by
  ext n; simp only [coeff_kap, coeff_smul]

lemma kap_zero (F : (τ →₀ ℕ) → (σ →₀ ℕ)) (hF : Function.Injective F) :
    kap F hF (0 : MvPolynomial σ K) = 0 := by
  ext n; simp only [coeff_kap, coeff_zero]

variable (e : τ → σ)

lemma coeff_rename_mul (he : Function.Injective e) (n : τ →₀ ℕ) (μ : σ →₀ ℕ) (hμ : ∀ x, μ (e x) = 0) (y : MvPolynomial τ K)
    (g : MvPolynomial σ K) (hg : ∀ w ∈ g.support, ∀ x, w (e x) = 0) :
    coeff (Finsupp.mapDomain e n + μ) (rename e y * g) = coeff n y * coeff μ g := by
  classical
  rw [coeff_mul, Finset.sum_eq_single (Finsupp.mapDomain e n, μ)]
  · rw [coeff_rename_mapDomain e he]
  · rintro ⟨u, w⟩ huw hne
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at huw
    simp only at huw
    by_contra hc
    have hu : coeff u (rename e y) ≠ 0 := left_ne_zero_of_mul hc
    have hw : coeff w g ≠ 0 := right_ne_zero_of_mul hc
    have hu' := mem_support_iff.mpr hu
    rw [support_rename_of_injective he, Finset.mem_image] at hu'
    obtain ⟨u0, _, rfl⟩ := hu'
    have hw0 := hg w (mem_support_iff.mpr hw)
    have h1 : Finsupp.mapDomain e u0 = Finsupp.mapDomain e n := by
      ext v
      by_cases hv : v ∈ Set.range e
      · obtain ⟨x, rfl⟩ := hv
        have hx := DFunLike.congr_fun huw (e x)
        rw [Finsupp.add_apply, Finsupp.add_apply, Finsupp.mapDomain_apply he, Finsupp.mapDomain_apply he,
          hμ x, hw0 x] at hx
        rw [Finsupp.mapDomain_apply he, Finsupp.mapDomain_apply he]
        omega
      · rw [Finsupp.mapDomain_of_notMem_range _ _ hv, Finsupp.mapDomain_of_notMem_range _ _ hv]
    rw [h1] at huw
    have h2 : w = μ := add_left_cancel huw
    exact hne (by rw [h1, h2])
  · intro h; exact absurd (Finset.HasAntidiagonal.mem_antidiagonal.mpr (by dsimp only)) h

lemma F_inj (he : Function.Injective e) (zm μ : σ →₀ ℕ) : Function.Injective (fun n : τ →₀ ℕ => zm + Finsupp.mapDomain e n + μ) := by
  intro n n' h
  simp only at h
  exact Finsupp.mapDomain_injective he (add_left_cancel (add_right_cancel h))

lemma kap_gen (he : Function.Injective e) (zm μ : σ →₀ ℕ) (hμ : ∀ x, μ (e x) = 0) (y : MvPolynomial τ K)
    (g : MvPolynomial σ K) (hg : ∀ w ∈ g.support, ∀ x, w (e x) = 0) :
    kap _ (F_inj e he zm μ) (monomial zm 1 * rename e y * g) = coeff μ g • y := by
  ext n
  rw [coeff_kap, coeff_smul, smul_eq_mul, mul_assoc, add_assoc, coeff_monomial_mul, one_mul,
    coeff_rename_mul e he n μ hμ y g hg, mul_comm]

end Kap

section TSat
variable {p : ℕ} [Fact p.Prime] {σ τ : Type} [DecidableEq σ] (e : τ → σ)

def IsInt {υ : Type} (f : MvPolynomial υ ℚ_[p]) : Prop := ∀ m, coeff m f ∈ (algebraMap ℤ_[p] ℚ_[p]).range

theorem tensorSat (he : Function.Injective e) (Yq : Submodule ℚ_[p] (MvPolynomial τ ℚ_[p])) (YZs : Submodule ℤ_[p] (MvPolynomial τ ℚ_[p]))
    (hYZ : ∀ y ∈ YZs, y ∈ Yq) (hYZ' : ∀ y ∈ Yq, IsInt y → y ∈ YZs)
    (G : Set (MvPolynomial σ ℚ_[p])) (Mb : Finset (σ →₀ ℕ))
    (hG1 : ∀ g ∈ G, g.support ⊆ Mb) (hG2 : ∀ μ ∈ Mb, monomial μ 1 ∈ G) (hG3 : ∀ μ ∈ Mb, ∀ x, μ (e x) = 0)
    (zm : σ →₀ ℕ) (Q : MvPolynomial σ ℚ_[p])
    (hQ : Q ∈ Submodule.span ℚ_[p] {x | ∃ y ∈ YZs, ∃ g ∈ G, x = monomial zm 1 * rename e y * g})
    (hint : IsInt Q) :
    Q ∈ Submodule.span ℤ_[p] {x | ∃ y ∈ YZs, ∃ g ∈ G, x = monomial zm 1 * rename e y * g} := by
  classical
  set Bs := {x | ∃ y ∈ YZs, ∃ g ∈ G, x = monomial zm 1 * rename e y * g}
  have hGs : ∀ g ∈ G, ∀ w ∈ g.support, ∀ x, w (e x) = 0 := fun g hg w hw x => hG3 w (hG1 g hg hw) x

  have hrec : ∀ Q ∈ Submodule.span ℚ_[p] Bs,
      Q = ∑ μ ∈ Mb, monomial zm 1 * rename e (kap _ (F_inj e he zm μ) Q) * monomial μ 1 := by
    intro Q hQ
    induction hQ using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨y, hy, g, hg, rfl⟩ := hx
      have hgs : g = ∑ μ ∈ Mb, monomial μ (coeff μ g) := by
        conv_lhs => rw [g.as_sum]
        exact Finset.sum_subset (hG1 g hg) (fun μ _ hμ => by rw [notMem_support_iff.mp hμ, monomial_zero])
      conv_lhs => rw [hgs, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun μ hμ => ?_)
      rw [kap_gen e he zm μ (hG3 μ hμ) y g (hGs g hg), map_smul, smul_eq_C_mul,
        show monomial μ (coeff μ g) = C (coeff μ g) * monomial μ 1 by rw [C_mul_monomial, mul_one]]
      ring
    | zero => simp [kap_zero]
    | add x y _ _ hx hy =>
      simp only [kap_add, map_add, mul_add, add_mul, Finset.sum_add_distrib]
      exact congrArg₂ (· + ·) hx hy
    | smul c x _ hx =>
      simp only [kap_smul, map_smul, mul_smul_comm, smul_mul_assoc, ← Finset.smul_sum]
      exact congrArg _ hx
  have hkY : ∀ μ ∈ Mb, ∀ Q ∈ Submodule.span ℚ_[p] Bs, kap _ (F_inj e he zm μ) Q ∈ Yq := by
    intro μ hμ' Q hQ
    have hμ := hG3 μ hμ'
    · induction hQ using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨y, hy, g, hg, rfl⟩ := hx
        rw [kap_gen e he zm μ hμ y g (hGs g hg)]
        exact Yq.smul_mem _ (hYZ y hy)
      | zero => rw [kap_zero]; exact Yq.zero_mem
      | add x y _ _ hx hy => rw [kap_add]; exact Yq.add_mem hx hy
      | smul c x _ hx => rw [kap_smul]; exact Yq.smul_mem c hx
  rw [hrec Q hQ]
  refine Submodule.sum_mem _ (fun μ hμ => Submodule.subset_span ⟨_, ?_, _, hG2 μ hμ, rfl⟩)
  apply hYZ' _ (hkY μ hμ Q hQ)
  intro n; rw [coeff_kap]; exact hint _

end TSat

end Formalism.GM.M.SSD

namespace Formalism.GM.M

open MvPolynomial Finset SSD

variable {p : ℕ} [Fact p.Prime] {N r : ℕ}

section Vars
variable {t : ℕ}

lemma scalS_inj : Function.Injective (scalS N r t) := by
  intro a b h; simpa [scalS] using h

lemma scalZ_ne_scalS (i k : Fin (t + 1)) : scalZ N r t i ≠ scalS N r t k := by simp [scalZ, scalS]

lemma inl_ne_scalS (x : Fin (N + 1) × Fin r) (k : Fin (t + 1)) : (Sum.inl x : BVar N r t) ≠ scalS N r t k := by
  simp [scalS]

lemma good_tie (i : Fin (t + 1)) (e : MvPolynomial (BVar N r t) ℚ_[p]) (he : SFree (scalS N r t) e) :
    Good (scalS N r t) (X (scalZ N r t i) * X (scalS N r t i) + e) (Pi.single i 1)
      (Finsupp.single (scalZ N r t i) 1 + Finsupp.single (scalS N r t i) 1) := by
  refine ⟨?_, ?_⟩
  · funext k
    simp only [sd, Finsupp.add_apply, Finsupp.single_apply]
    rw [if_neg (scalZ_ne_scalS i k)]
    by_cases h : i = k
    · subst h; simp
    · rw [if_neg (fun h' => h (scalS_inj h')), Pi.single_apply, if_neg (Ne.symm h)]; rfl
  · have : X (scalZ N r t i) * X (scalS N r t i) + e -
        monomial (Finsupp.single (scalZ N r t i) 1 + Finsupp.single (scalS N r t i) 1) (1 : ℚ_[p]) = e := by
      rw [X, X, monomial_mul, mul_one, add_sub_cancel_left]
    rw [this]
    intro m hm
    rw [he m hm]
    refine ⟨fun k => Nat.zero_le _, fun h => ?_⟩
    have := congrFun h i
    simp at this

lemma sfree_pair (u w : Fin r → Fin (N + 1) × Fin r) :
    SFree (scalS N r t) (∑ c, X (Sum.inl (u c)) * X (Sum.inl (w c)) : MvPolynomial (BVar N r t) ℚ_[p]) :=
  SFree.sum _ _ _ (fun c _ => (SFree.X _ (inl_ne_scalS _)).mul _ (SFree.X _ (inl_ne_scalS _)))

def lv (j : Fin t → ℕ) (jp : ℕ) : Fin (t + 1) → ℕ :=
  ∑ i, j i • Pi.single (Fin.castSucc i) 1 + jp • Pi.single (Fin.last t) 1

lemma lv_castSucc (j : Fin t → ℕ) (jp : ℕ) (k : Fin t) : lv j jp (Fin.castSucc k) = j k := by
  simp [lv, Finset.sum_apply, Pi.single_apply, Fin.castSucc_inj, Fin.castSucc_ne_last]

lemma lv_last (j : Fin t → ℕ) (jp : ℕ) : lv j jp (Fin.last t) = jp := by
  simp [lv, Finset.sum_apply, Pi.single_apply, (Fin.castSucc_ne_last _).symm]

lemma lv_inj {j j' : Fin t → ℕ} {jp jp' : ℕ} (h : lv j jp = lv j' jp') : j = j' ∧ jp = jp' := by
  refine ⟨funext fun k => ?_, ?_⟩
  · rw [← lv_castSucc j jp k, h, lv_castSucc]
  · rw [← lv_last j jp, h, lv_last]

end Vars

section Int
variable {σ : Type}

lemma intPol_iff_isInt (f : MvPolynomial σ ℚ_[p]) : f ∈ IntPol p σ ↔ IsInt f := by
  have e1 : f ∈ IntPol p σ ↔ (f.coeffs : Set ℚ_[p]) ⊆ Set.range (algebraMap ℤ_[p] ℚ_[p]) := by
    rw [← mem_range_map_iff_coeffs_subset]
    simp only [IntPol, LinearMap.mem_range, AlgHom.toLinearMap_apply, mapAlgHom_apply, Set.mem_range]
    rfl
  rw [e1]
  constructor
  · intro h m
    by_cases hm : m ∈ f.support
    · exact h (by rw [Finset.mem_coe]; exact coeff_mem_coeffs m (mem_support_iff.mp hm))
    · rw [notMem_support_iff.mp hm]; exact ⟨0, map_zero _⟩
  · intro h c hc
    rw [Finset.mem_coe, mem_coeffs_iff] at hc
    obtain ⟨m, _, rfl⟩ := hc
    exact h m

lemma intPol_iff' (F : MvPolynomial σ ℚ_[p]) :
    F ∈ IntPol p σ ↔ ∃ F₀ : MvPolynomial σ ℤ_[p], map (algebraMap ℤ_[p] ℚ_[p]) F₀ = F := by
  simp [IntPol, LinearMap.mem_range, MvPolynomial.mapAlgHom_apply, Algebra.ofId_apply]

lemma intPol_mul' {F G : MvPolynomial σ ℚ_[p]} (hF : F ∈ IntPol p σ) (hG : G ∈ IntPol p σ) :
    F * G ∈ IntPol p σ := by
  obtain ⟨F₀, rfl⟩ := (intPol_iff' F).mp hF
  obtain ⟨G₀, rfl⟩ := (intPol_iff' G).mp hG
  exact (intPol_iff' _).mpr ⟨F₀ * G₀, map_mul _ _ _⟩

lemma intPol_X' (x : σ) : (X x : MvPolynomial σ ℚ_[p]) ∈ IntPol p σ :=
  (intPol_iff' _).mpr ⟨X x, map_X _ _⟩

lemma intPol_monomial' (m : σ →₀ ℕ) : (monomial m 1 : MvPolynomial σ ℚ_[p]) ∈ IntPol p σ :=
  (intPol_iff' _).mpr ⟨monomial m 1, by rw [map_monomial, map_one]⟩

lemma intPol_pow' {F : MvPolynomial σ ℚ_[p]} (hF : F ∈ IntPol p σ) (k : ℕ) : F ^ k ∈ IntPol p σ := by
  obtain ⟨F₀, rfl⟩ := (intPol_iff' F).mp hF
  exact (intPol_iff' _).mpr ⟨F₀ ^ k, map_pow _ _ _⟩

lemma intPol_prod' {α : Type} (u : Finset α) (f : α → MvPolynomial σ ℚ_[p]) (h : ∀ i ∈ u, f i ∈ IntPol p σ) :
    (∏ i ∈ u, f i) ∈ IntPol p σ := by
  classical
  induction u using Finset.induction_on with
  | empty => simpa using intPol_monomial' (p := p) (σ := σ) 0
  | insert i u hi ih =>
    rw [prod_insert hi]
    exact intPol_mul' (h i (mem_insert_self _ _)) (ih fun k hk => h k (mem_insert_of_mem hk))

lemma intPol_rename' {τ : Type} (e : τ → σ) {y : MvPolynomial τ ℚ_[p]} (hy : y ∈ IntPol p τ) :
    rename e y ∈ IntPol p σ := by
  obtain ⟨y₀, rfl⟩ := (intPol_iff' y).mp hy
  exact (intPol_iff' _).mpr ⟨rename e y₀, map_rename _ _ _⟩

end Int

section Block
variable [NeZero r] (D : BlockData N)

noncomputable def zmS : BVar N r D.T.t →₀ ℕ :=
  ∑ i, Finsupp.single (scalZ N r D.T.t (Fin.castSucc i)) (D.T.z i) +
    Finsupp.single (scalZ N r D.T.t (Fin.last D.T.t)) D.zPlus

lemma zmon_eq : ((∏ i, X (scalZ N r D.T.t (Fin.castSucc i)) ^ D.T.z i) *
    X (scalZ N r D.T.t (Fin.last D.T.t)) ^ D.zPlus : MvPolynomial (BVar N r D.T.t) ℚ_[p]) =
      monomial (zmS D) 1 := by
  simp only [X_pow_eq_monomial]
  rw [zmS, ← monomial_sum_one, monomial_mul, mul_one]

noncomputable def pre (j : Fin D.T.t → ℕ) (jp : ℕ) : MvPolynomial (BVar N r D.T.t) ℚ_[p] :=
  (∏ i, D.Ehat p (r := r) i ^ j i) * D.Eplus p (r := r) ^ jp

lemma good_pre (j : Fin D.T.t → ℕ) (jp : ℕ) :
    ∃ s, Good (scalS N r D.T.t) (pre (p := p) (r := r) D j jp) (lv j jp) s := by
  have hE : ∀ i, Good (scalS N r D.T.t) (D.Ehat p (r := r) i) (Pi.single (Fin.castSucc i) 1) _ :=
    fun i => good_tie (Fin.castSucc i) _ (sfree_pair _ _)
  have hP : Good (scalS N r D.T.t) (D.Eplus p (r := r)) (Pi.single (Fin.last D.T.t) 1) _ :=
    good_tie (Fin.last D.T.t) _ (sfree_pair _ _)
  exact ⟨_, (Good.prod _ univ (fun i => D.Ehat p (r := r) i ^ j i) _ _ (fun i _ => (hE i).pow _ (j i))).mul _
    (hP.pow _ jp)⟩

def Bset (j : Fin D.T.t → ℕ) (jp : ℕ) : Set (MvPolynomial (BVar N r D.T.t) ℚ_[p]) :=
  {x | ∃ y ∈ YZ p (r := r) (D.lettersAt j jp) D.T.J D.T.thr, ∃ g ∈ XiPolZ p N r D.T.t (D.B - jp),
    x = monomial (zmS D) 1 * rename (chainEmb N r D.T.t) y * g}

lemma gens_sub (j : Fin D.T.t → ℕ) (jp : ℕ) (x : MvPolynomial (BVar N r D.T.t) ℚ_[p])
    (hx : x ∈ D.gens p (r := r) j jp) : ∃ b ∈ Bset (p := p) D j jp, x = pre D j jp * b := by
  obtain ⟨y, hy, g, hg, rfl⟩ := hx
  refine ⟨_, ⟨y, hy, g, hg, rfl⟩, ?_⟩
  rw [pre, ← zmon_eq]; ring

lemma memV (j : Fin D.T.t → ℕ) (jp : ℕ) (v : MvPolynomial (BVar N r D.T.t) ℚ_[p])
    (hv : v ∈ Submodule.span ℚ_[p] (D.gens p (r := r) j jp)) :
    ∃ Q ∈ Submodule.span ℚ_[p] (Bset (p := p) D j jp), v = pre D j jp * Q := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, hb, rfl⟩ := gens_sub D j jp x hx
    exact ⟨b, Submodule.subset_span hb, rfl⟩
  | zero => exact ⟨0, Submodule.zero_mem _, by rw [mul_zero]⟩
  | add x y _ _ hx hy =>
    obtain ⟨Q, hQ, rfl⟩ := hx
    obtain ⟨Q', hQ', rfl⟩ := hy
    exact ⟨Q + Q', Submodule.add_mem _ hQ hQ', by rw [mul_add]⟩
  | smul c x _ hx =>
    obtain ⟨Q, hQ, rfl⟩ := hx
    exact ⟨c • Q, Submodule.smul_mem _ c hQ, by rw [mul_smul_comm]⟩

lemma xi_mono {b : ℕ} {g : MvPolynomial (BVar N r D.T.t) ℚ_[p]} (hg : g ∈ XiPolZ p N r D.T.t b)
    {m : BVar N r D.T.t →₀ ℕ} (hm : m ∈ g.support) :
    (∀ v ∈ m.support, ∃ c, v = xiVar N r D.T.t c) ∧ ∑ c, m (xiVar N r D.T.t c) = b := by
  have := (Submodule.mem_inf.mp hg).1
  rw [Submodule.restrictScalars_mem, mem_restrictSupport_iff] at this
  exact this hm

lemma sfree_xi {b : ℕ} {g : MvPolynomial (BVar N r D.T.t) ℚ_[p]} (hg : g ∈ XiPolZ p N r D.T.t b) :
    SFree (scalS N r D.T.t) g := by
  intro m hm; funext k; simp only [sd, Pi.zero_apply]
  by_contra h
  obtain ⟨c, hc⟩ := (xi_mono D hg hm).1 _ (Finsupp.mem_support_iff.mpr h)
  simp [scalS, xiVar] at hc

lemma sfree_B (j : Fin D.T.t → ℕ) (jp : ℕ) (x : MvPolynomial (BVar N r D.T.t) ℚ_[p])
    (hx : x ∈ Bset (p := p) D j jp) : SFree (scalS N r D.T.t) x := by
  obtain ⟨y, _, g, hg, rfl⟩ := hx
  refine (SFree.mul _ (SFree.mul _ ?_ ?_) (sfree_xi D hg))
  · rw [← zmon_eq]
    exact SFree.mul _ (SFree.prod _ _ _ fun i _ => (SFree.X _ (scalZ_ne_scalS _)).pow _ _)
      ((SFree.X _ (scalZ_ne_scalS _)).pow _ _)
  · exact SFree.rename _ _ (fun x k => by simp [chainEmb, scalS]) y

lemma sfree_span (j : Fin D.T.t → ℕ) (jp : ℕ) (Q : MvPolynomial (BVar N r D.T.t) ℚ_[p])
    (hQ : Q ∈ Submodule.span ℚ_[p] (Bset (p := p) D j jp)) : SFree (scalS N r D.T.t) Q := by
  induction hQ using Submodule.span_induction with
  | mem x hx => exact sfree_B D j jp x hx
  | zero => simpa using SFree.C (K := ℚ_[p]) (scalS N r D.T.t) 0
  | add x y _ _ hx hy => exact hx.add _ hy
  | smul c x _ hx => exact fun m hm => hx m (support_smul hm)

end Block

end Formalism.GM.M

namespace Formalism.GM.M

open MvPolynomial Finset SSD

variable {p : ℕ} [Fact p.Prime] {N r : ℕ}

section Main
variable [NeZero r] (D : BlockData N)

lemma topV (j : Fin D.T.t → ℕ) (jp : ℕ) (v : MvPolynomial (BVar N r D.T.t) ℚ_[p])
    (hv : v ∈ Submodule.span ℚ_[p] (D.gens p (r := r) j jp)) :
    ∃ s Q, Q ∈ Submodule.span ℚ_[p] (Bset (p := p) D j jp) ∧ v = pre D j jp * Q ∧
      sd (scalS N r D.T.t) s = lv j jp ∧ (∀ m ∈ v.support, sd (scalS N r D.T.t) m ≤ lv j jp) ∧
      ∀ n, coeff (s + n) v = coeff n Q := by
  obtain ⟨Q, hQ, rfl⟩ := memV D j jp v hv
  obtain ⟨s, hs⟩ := good_pre (p := p) (r := r) D j jp
  obtain ⟨h1, h2⟩ := hs.mul_sfree _ (sfree_span D j jp Q hQ)
  exact ⟨s, Q, hQ, rfl, hs.1, h1, h2⟩

lemma Q_of_top (j : Fin D.T.t → ℕ) (jp : ℕ) (v : MvPolynomial (BVar N r D.T.t) ℚ_[p])
    (hv : v ∈ Submodule.span ℚ_[p] (D.gens p (r := r) j jp)) (P : ℚ_[p] → Prop) (hP0 : P 0)
    (htop : ∀ m, sd (scalS N r D.T.t) m = lv j jp → P (coeff m v)) :
    ∃ Q ∈ Submodule.span ℚ_[p] (Bset (p := p) D j jp), v = pre D j jp * Q ∧ ∀ n, P (coeff n Q) := by
  obtain ⟨s, Q, hQ, hvQ, hs, _, hc⟩ := topV D j jp v hv
  refine ⟨Q, hQ, hvQ, fun n => ?_⟩
  by_cases hn : n ∈ Q.support
  · rw [← hc n]; apply htop; rw [sd_add, hs, sfree_span D j jp Q hQ n hn, add_zero]
  · rw [notMem_support_iff.mp hn]; exact hP0

theorem ss_direct :
    iSupIndep (fun ij : {ij : (Fin D.T.t → ℕ) × ℕ // D.LevelOK ij.1 ij.2} =>
      Submodule.span ℚ_[p] (D.gens p (r := r) ij.1.1 ij.1.2)) := by
  apply absDirect (scalS N r D.T.t) _ (fun ij => lv ij.1.1 ij.1.2)
  · intro a b h
    obtain ⟨h1, h2⟩ := lv_inj h
    exact Subtype.ext (Prod.ext h1 h2)
  · intro L v hv
    obtain ⟨_, _, _, _, _, h1, _⟩ := topV D _ _ v hv
    exact h1
  · intro L v hv htop
    obtain ⟨Q, _, rfl, hz⟩ := Q_of_top D _ _ v hv (fun c => c = 0) rfl htop
    have : Q = 0 := by ext n; simpa using hz n
    rw [this, mul_zero]

lemma gens_mem_SSZ (j : Fin D.T.t → ℕ) (jp : ℕ) (hL : D.LevelOK j jp) (x : MvPolynomial (BVar N r D.T.t) ℚ_[p])
    (hx : x ∈ D.gens p (r := r) j jp) : x ∈ D.SSZ p (r := r) :=
  Submodule.subset_span (Set.mem_iUnion.mpr ⟨j, Set.mem_iUnion.mpr ⟨jp, Set.mem_iUnion.mpr ⟨hL, hx⟩⟩⟩)

lemma pre_span_mem (j : Fin D.T.t → ℕ) (jp : ℕ) (hL : D.LevelOK j jp) (Q : MvPolynomial (BVar N r D.T.t) ℚ_[p])
    (hQ : Q ∈ Submodule.span ℤ_[p] (Bset (p := p) D j jp)) : pre D j jp * Q ∈ D.SSZ p (r := r) := by
  induction hQ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨y, hy, g, hg, rfl⟩ := hx
    refine gens_mem_SSZ D j jp hL _ ⟨y, hy, g, hg, ?_⟩
    rw [pre, ← zmon_eq]; ring
  | zero => rw [mul_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [mul_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ c hx

lemma Ehat_int (i : Fin D.T.t) : D.Ehat p (r := r) i ∈ IntPol p (BVar N r D.T.t) := by
  unfold BlockData.Ehat
  exact Submodule.add_mem _ (intPol_mul' (intPol_X' _) (intPol_X' _))
    (Submodule.sum_mem _ fun c _ => intPol_mul' (intPol_X' _) (intPol_X' _))

lemma Eplus_int : D.Eplus p (r := r) ∈ IntPol p (BVar N r D.T.t) := by
  unfold BlockData.Eplus
  exact Submodule.add_mem _ (intPol_mul' (intPol_X' _) (intPol_X' _))
    (Submodule.sum_mem _ fun c _ => intPol_mul' (intPol_X' _) (intPol_X' _))

lemma SSZ_int (x : MvPolynomial (BVar N r D.T.t) ℚ_[p]) (hx : x ∈ D.SSZ p (r := r)) :
    x ∈ IntPol p (BVar N r D.T.t) := by
  refine (Submodule.span_le.mpr ?_) hx
  intro x hx
  simp only [Set.mem_iUnion] at hx
  obtain ⟨j, jp, _, y, hy, g, hg, rfl⟩ := hx
  have hyI : y ∈ IntPol p (Fin N × Fin r) := (Submodule.mem_inf.mp (Submodule.mem_inf.mp hy).2).2
  have hgI : g ∈ IntPol p (BVar N r D.T.t) := (Submodule.mem_inf.mp hg).2
  refine intPol_mul' (intPol_mul' (intPol_mul' (intPol_mul' (intPol_mul' ?_ ?_) ?_) ?_)
    (intPol_rename' _ hyI)) hgI
  · exact intPol_prod' _ _ fun i _ => intPol_pow' (Ehat_int D i) _
  · exact intPol_pow' (Eplus_int D) _
  · exact intPol_prod' _ _ fun i _ => intPol_pow' (intPol_X' _) _
  · exact intPol_pow' (intPol_X' _) _

lemma chainEmb_inj : Function.Injective (chainEmb N r D.T.t) := by
  rintro ⟨a, c⟩ ⟨b, d⟩ h
  simp only [chainEmb, Sum.inl.injEq, Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  rw [Fin.castSucc_inj] at h1
  rw [h1, h2]

lemma xiVar_inj : Function.Injective (xiVar N r D.T.t) := by
  intro a b h; simpa [xiVar] using h

lemma Q_sat (j : Fin D.T.t → ℕ) (jp : ℕ) (Q : MvPolynomial (BVar N r D.T.t) ℚ_[p])
    (hQ : Q ∈ Submodule.span ℚ_[p] (Bset (p := p) D j jp)) (hint : IsInt Q) :
    Q ∈ Submodule.span ℤ_[p] (Bset (p := p) D j jp) := by
  classical
  refine tensorSat (chainEmb N r D.T.t) (chainEmb_inj D) (Y p (r := r) (D.lettersAt j jp) D.T.J D.T.thr)
    (YZ p (r := r) (D.lettersAt j jp) D.T.J D.T.thr) ?_ ?_ (XiPolZ p N r D.T.t (D.B - jp))
    (finsuppAntidiag (univ.image (xiVar N r D.T.t)) (D.B - jp)) ?_ ?_ ?_ (zmS D) Q hQ hint
  · intro y hy; exact (Submodule.mem_inf.mp hy).1
  · intro y hy hi
    refine Submodule.mem_inf.mpr ⟨hy, Submodule.mem_inf.mpr ⟨?_, (intPol_iff_isInt y).mpr hi⟩⟩
    exact (Submodule.mem_inf.mp hy).1
  · intro g hg m hm
    obtain ⟨h1, h2⟩ := xi_mono D hg hm
    rw [mem_finsuppAntidiag]
    refine ⟨?_, ?_⟩
    · rw [Finset.sum_image (fun a _ b _ h => xiVar_inj D h)]; exact h2
    · intro v hv
      obtain ⟨c, rfl⟩ := h1 v hv
      exact Finset.mem_image_of_mem _ (mem_univ c)
  · intro μ hμ
    rw [mem_finsuppAntidiag] at hμ
    refine Submodule.mem_inf.mpr ⟨?_, intPol_monomial' μ⟩
    rw [Submodule.restrictScalars_mem, mem_restrictSupport_iff]
    intro m hm
    rw [Finset.mem_coe, mem_support_iff, coeff_monomial] at hm
    split_ifs at hm with h
    · subst h
      refine ⟨fun v hv => ?_, ?_⟩
      · obtain ⟨c, _, rfl⟩ := Finset.mem_image.mp (hμ.2 hv)
        exact ⟨c, rfl⟩
      · rw [← hμ.1, Finset.sum_image (fun a _ b _ h => xiVar_inj D h)]
    · exact absurd rfl hm
  · intro μ hμ x
    rw [mem_finsuppAntidiag] at hμ
    by_contra h
    obtain ⟨c, _, hc⟩ := Finset.mem_image.mp (hμ.2 (Finsupp.mem_support_iff.mpr h))
    obtain ⟨a, b⟩ := x
    simp [xiVar, chainEmb] at hc
    exact (Fin.castSucc_ne_last a) hc.1.symm

theorem ss_sat (x : MvPolynomial (BVar N r D.T.t) ℚ_[p])
    (hx : x ∈ Submodule.span ℚ_[p] (D.SSZ p (r := r) : Set (MvPolynomial (BVar N r D.T.t) ℚ_[p])))
    (hi : x ∈ IntPol p (BVar N r D.T.t)) : x ∈ D.SSZ p (r := r) := by
  classical
  rw [BlockData.SSZ, Submodule.span_span_of_tower] at hx
  have hU : (⋃ (j : Fin D.T.t → ℕ) (jp : ℕ) (_ : D.LevelOK j jp), D.gens p (r := r) j jp) =
      ⋃ (ij : {ij : (Fin D.T.t → ℕ) × ℕ // D.LevelOK ij.1 ij.2}), D.gens p (r := r) ij.1.1 ij.1.2 := by
    ext y
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨j, jp, h, hy⟩; exact ⟨⟨(j, jp), h⟩, hy⟩
    · rintro ⟨⟨⟨j, jp⟩, h⟩, hy⟩; exact ⟨j, jp, h, hy⟩
  rw [hU, Submodule.span_iUnion, Submodule.mem_iSup_iff_exists_finset] at hx
  obtain ⟨s, hs⟩ := hx
  rw [Submodule.mem_iSup_finset_iff_exists_sum] at hs
  obtain ⟨μ, hμ⟩ := hs
  rw [← hμ] at hi ⊢
  have key := absSat (scalS N r D.T.t)
    (fun ij : {ij : (Fin D.T.t → ℕ) × ℕ // D.LevelOK ij.1 ij.2} =>
      Submodule.span ℚ_[p] (D.gens p (r := r) ij.1.1 ij.1.2)) (fun ij => lv ij.1.1 ij.1.2)
    (fun a b h => by obtain ⟨h1, h2⟩ := lv_inj h; exact Subtype.ext (Prod.ext h1 h2))
    (algebraMap ℤ_[p] ℚ_[p]).range.toAddSubgroup (D.SSZ p (r := r)).toAddSubgroup
    (fun L v hv => by obtain ⟨_, _, _, _, _, h1, _⟩ := topV D _ _ v hv; exact h1)
    (fun f hf m => (intPol_iff_isInt f).mp (SSZ_int D f hf) m)
    (fun L v hv htop => by
      obtain ⟨Q, hQ, rfl, hz⟩ := Q_of_top D _ _ v hv (fun c => c ∈ (algebraMap ℤ_[p] ℚ_[p]).range)
        (Subring.zero_mem _) htop
      exact pre_span_mem D _ _ L.2 Q (Q_sat D _ _ Q hQ hz))
    s (fun i => (μ i : MvPolynomial (BVar N r D.T.t) ℚ_[p])) (fun L _ => (μ L).2)
    (fun m => (intPol_iff_isInt _).mp hi m)
  exact key

end Main

end Formalism.GM.M

namespace Formalism.GM

theorem semisimple_direct_sum : Formalism.GM.M.SSDirect := by
  intro p _ N r _ D _ _
  exact ⟨Formalism.GM.M.ss_direct D, fun x hx hi => Formalism.GM.M.ss_sat D x hx hi⟩

end Formalism.GM
