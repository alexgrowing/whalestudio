import Formalism.SharpRestriction.GrowthBounds.StatementOfDegreeAndBound

noncomputable section

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

namespace Formalism.MainNotions.LemmaBAlt

section maps
variable {P Q : Type*} [CommRing P] [CommRing Q] {n : ℕ}

theorem map_exterior_one (φ : P →+* Q) (J : Finset (Fin n)) : φ (extOne J) = extOne J := by
  unfold extOne; split_ifs <;> simp

theorem map_right_wedge (φ : P →+* Q) (x : Fin n → P) (K : Finset (Fin n) → P) (J : Finset (Fin n)) :
    φ (wedgeR x K J) = wedgeR (fun m => φ (x m)) (fun J => φ (K J)) J := by
  simp [wedgeR, map_sum]

theorem map_right_contraction (φ : P →+* Q) (x : Fin n → P) (K : Finset (Fin n) → P) (J : Finset (Fin n)) :
    φ (contrR x K J) = contrR (fun m => φ (x m)) (fun J => φ (K J)) J := by
  simp [contrR, map_sum]

theorem map_column_operator (φ : P →+* Q) (c : ℤ) (hP hN : ℕ) (x : Fin n → P) (K : Finset (Fin n) → P)
    (J : Finset (Fin n)) :
    φ (colStep c hP hN x K J) = colStep c hP hN (fun m => φ (x m)) (fun J => φ (K J)) J := by
  unfold colStep; split_ifs <;> simp [map_right_wedge, map_right_contraction]

end maps

theorem map_column_kernel {R R' : Type*} [CommRing R] [CommRing R'] (φ : R →+* R') {N n : ℕ}
    (mu : Fin (N + 1) → Fin n → ℤ) (c : ℤ) (j : ℕ) (J : Finset (Fin n)) :
    MvPolynomial.map φ (Kcol R mu c j J) = Kcol R' mu c j J := by
  induction j generalizing J with
  | zero => exact map_exterior_one _ _
  | succ j ih =>
    simp only [Kcol]
    split_ifs with h
    · rw [map_column_operator]
      have h1 : (fun m => MvPolynomial.map φ (letVec R (⟨j, h⟩ : Fin N) m)) = letVec (n := n) R' (⟨j, h⟩ : Fin N) := by
        funext m; simp [letVec]
      have h2 : (fun J => MvPolynomial.map φ (Kcol R mu c j J)) = Kcol R' mu c j := funext ih
      rw [h1, h2]
    · exact ih J

theorem map_Psi' {R R' : Type*} [CommRing R] [CommRing R'] (φ : R →+* R') {N n : ℕ}
    (mu : Fin (N + 1) → Fin n → ℤ) (I : ℤ → Finset (Fin n)) :
    MvPolynomial.map φ (Psi R mu I) = Psi R' mu I := by
  simp [Psi, map_prod, map_column_kernel]

theorem column_height_lt_iff {n : ℕ} {mu : Fin n → ℤ} (hmu : Dominant mu) (c : ℤ) (m : Fin n) :
    m.val < colH mu c ↔ c ≤ mu m := by
  constructor
  · intro h
    by_contra hc
    have hsub : (univ.filter fun x => c ≤ mu x) ⊆ Finset.Iio m := by
      intro x hx
      rw [Finset.mem_filter] at hx
      rw [Finset.mem_Iio]
      by_contra hxm
      exact hc (hx.2.trans (hmu (not_lt.1 hxm)))
    have := Finset.card_le_card hsub
    rw [Fin.card_Iio] at this
    unfold colH at h
    omega
  · intro h
    have hsub : Finset.Iic m ⊆ (univ.filter fun x => c ≤ mu x) := by
      intro x hx
      rw [Finset.mem_Iic] at hx
      rw [Finset.mem_filter]
      exact ⟨mem_univ _, h.trans (hmu hx)⟩
    have := Finset.card_le_card hsub
    rw [Fin.card_Iic] at this
    unfold colH
    omega

theorem abs_entry_le_total {N n : ℕ} (mu : Fin (N + 1) → Fin n → ℤ) (i : Fin (N + 1)) (m : Fin n) :
    |mu i m| ≤ ∑ i, ∑ m, |mu i m| := by
  calc |mu i m| ≤ ∑ m, |mu i m| := Finset.single_le_sum (f := fun m => |mu i m|) (fun _ _ => abs_nonneg _) (mem_univ m)
    _ ≤ ∑ i, ∑ m, |mu i m| :=
      Finset.single_le_sum (f := fun i => ∑ m, |mu i m|) (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (mem_univ i)

theorem canonical_column_positive {N n : ℕ} {mu : Fin (N + 1) → Fin n → ℤ} (hd : Dominant (pEnd mu)) {c : ℤ} (hc : 1 ≤ c) :
    Ican mu c = univ.filter fun m => c ≤ pEnd mu m := by
  unfold Ican; rw [if_pos hc]
  exact Finset.filter_congr fun m _ => column_height_lt_iff hd c m

theorem canonical_column_nonpositive {N n : ℕ} {mu : Fin (N + 1) → Fin n → ℤ} (hd : Dominant (pEnd mu)) {c : ℤ} (hc : ¬ 1 ≤ c) :
    Ican mu c = univ.filter fun m => ¬ c ≤ pEnd mu m := by
  unfold Ican; rw [if_neg hc]
  refine Finset.filter_congr fun m _ => ?_
  rw [← column_height_lt_iff hd c m, not_lt]

theorem tableau_column_canonical_eq {N n : ℕ} {mu : Fin (N + 1) → Fin n → ℤ} (hd : Dominant (pEnd mu)) (c : ℤ) :
    tabCol (Ican mu) c = univ.filter fun m => c ≤ pEnd mu m := by
  unfold tabCol
  by_cases hc : 1 ≤ c
  · rw [if_pos hc, canonical_column_positive hd hc]
  · rw [if_neg hc, canonical_column_nonpositive hd hc]
    ext m; simp

theorem canonical_tableau_standard {N n : ℕ} {mu : Fin (N + 1) → Fin n → ℤ} (hd : Dominant (pEnd mu)) : IsSt mu (Ican mu) := by
  refine ⟨?_, ?_, ?_⟩
  · intro c hc
    have hT := fun m => abs_entry_le_total mu (Fin.last N) m
    simp only [colRange, Finset.mem_Icc, not_and_or, not_le] at hc
    by_cases h1 : 1 ≤ c
    · rw [canonical_column_positive hd h1]
      refine Finset.filter_eq_empty_iff.2 fun m _ => ?_
      have := hT m
      have h2 := le_abs_self (mu (Fin.last N) m)
      have h0 : (0 : ℤ) ≤ ∑ i, ∑ m, |mu i m| := (abs_nonneg _).trans this
      unfold pEnd
      rcases hc with hc | hc <;> omega
    · rw [canonical_column_nonpositive hd h1]
      refine Finset.filter_eq_empty_iff.2 fun m _ => ?_
      have := hT m
      have h2 := neg_abs_le (mu (Fin.last N) m)
      have h0 : (0 : ℤ) ≤ ∑ i, ∑ m, |mu i m| := (abs_nonneg _).trans this
      unfold pEnd
      rcases hc with hc | hc <;> omega
  · intro c
    by_cases h1 : 1 ≤ c
    · rw [canonical_column_positive hd h1, if_pos h1]; rfl
    · rw [canonical_column_nonpositive hd h1, if_neg h1]
      have := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin n))) (fun m => c ≤ pEnd mu m)
      rw [Finset.card_univ, Fintype.card_fin] at this
      unfold colH
      omega
  · intro c t
    rw [tableau_column_canonical_eq hd, tableau_column_canonical_eq hd]
    refine Finset.card_le_card (Finset.filter_subset_filter _ ?_)
    intro m hm
    rw [Finset.mem_filter] at hm ⊢
    exact ⟨hm.1, by omega⟩

section a1dpAbs

variable {R : Type*} [CommRing R] {σ ι : Type*} [DecidableEq ι]

def dividedPowerShiftedExponent (src dst : ι → σ) (m : σ →₀ ℕ) (f : ι →₀ ℕ) : σ →₀ ℕ :=
  (m - Finsupp.mapDomain src f) + Finsupp.mapDomain dst f

def dividedPowerCoeff (sg : ι → R) (src : ι → σ) (s : Finset ι) (m : σ →₀ ℕ) (f : ι →₀ ℕ) : R :=
  ∏ l ∈ s, sg l ^ (f l) * ((m (src l)).choose (f l) : R)

def dividedPowerTerm (sg : ι → R) (src dst : ι → σ) (s : Finset ι) (m : σ →₀ ℕ) (f : ι →₀ ℕ) : MvPolynomial σ R :=
  monomial (dividedPowerShiftedExponent src dst m f) (dividedPowerCoeff sg src s m f)

def dividedPowerSum (sg : ι → R) (src dst : ι → σ) (s : Finset ι) (k : ℕ) (m : σ →₀ ℕ) : MvPolynomial σ R :=
  ∑ f ∈ Finset.finsuppAntidiag s k, dividedPowerTerm sg src dst s m f

def dividedPowerDerivation (sg : ι → R) (src dst : ι → σ) (l : ι) : MvPolynomial σ R →ₗ[R] MvPolynomial σ R :=
  sg l • ((LinearMap.mulLeft R (X (dst l))) ∘ₗ (pderiv (src l)).toLinearMap)

theorem derivation_divided_power_term (sg : ι → R) (src dst : ι → σ) (hs : Function.Injective src) (hd : ∀ l l', dst l' ≠ src l)
    (s : Finset ι) (m : σ →₀ ℕ) (f : ι →₀ ℕ) (l : ι) (hl : l ∈ s) :
    dividedPowerDerivation sg src dst l (dividedPowerTerm sg src dst s m f) =
      (f l + 1) • dividedPowerTerm sg src dst s m (f + Finsupp.single l 1) := by
  classical
  have h1 : Finsupp.mapDomain src f (src l) = f l := Finsupp.mapDomain_apply hs f l
  have h2 : ∀ g : ι →₀ ℕ, Finsupp.mapDomain dst g (src l) = 0 := fun g =>
    Finsupp.mapDomain_of_notMem_range _ _ (by rintro ⟨l', h⟩; exact hd l l' h)
  have hexp : Finsupp.single (dst l) 1 + (dividedPowerShiftedExponent src dst m f - Finsupp.single (src l) 1) =
      dividedPowerShiftedExponent src dst m (f + Finsupp.single l 1) := by
    ext v
    simp only [dividedPowerShiftedExponent, Finsupp.mapDomain_add, Finsupp.mapDomain_single, Finsupp.add_apply,
      Finsupp.tsub_apply, Finsupp.single_apply]
    by_cases hv : src l = v
    · subst hv
      have h3 := hd l l
      simp only [h1, h2, h3, if_true, if_false]
      omega
    · simp only [hv, if_false]
      omega
  have he : dividedPowerShiftedExponent src dst m f (src l) = m (src l) - f l := by
    simp [dividedPowerShiftedExponent, h1, h2]
  have hcf : sg l * (dividedPowerCoeff sg src s m f * ((dividedPowerShiftedExponent src dst m f (src l) : ℕ) : R)) =
      ((f l + 1 : ℕ) : R) * dividedPowerCoeff sg src s m (f + Finsupp.single l 1) := by
    rw [he]
    unfold dividedPowerCoeff
    rw [← Finset.mul_prod_erase s _ hl, ← Finset.mul_prod_erase s _ hl]
    have h4 : ∏ x ∈ s.erase l, sg x ^ ((f + Finsupp.single l 1 : ι →₀ ℕ) x) *
        ((m (src x)).choose ((f + Finsupp.single l 1 : ι →₀ ℕ) x) : R) =
        ∏ x ∈ s.erase l, sg x ^ (f x) * ((m (src x)).choose (f x) : R) := by
      apply Finset.prod_congr rfl
      intro x hx
      have hx' : x ≠ l := (Finset.mem_erase.1 hx).1
      simp [hx'.symm]
    rw [h4]
    have hc : ((m (src l)).choose (f l + 1) : R) * ((f l + 1 : ℕ) : R) =
        ((m (src l)).choose (f l) : R) * ((m (src l) - f l : ℕ) : R) := by
      exact_mod_cast congrArg (Nat.cast (R := R)) (Nat.choose_succ_right_eq (m (src l)) (f l))
    simp only [Finsupp.add_apply, Finsupp.single_eq_same, pow_succ]
    generalize (∏ x ∈ s.erase l, sg x ^ (f x) * ((m (src x)).choose (f x) : R)) = Er
    linear_combination (-(sg l ^ f l * sg l * Er)) * hc
  simp only [dividedPowerDerivation, dividedPowerTerm, LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.mulLeft_apply,
    Derivation.coeFn_coe, pderiv_monomial]
  rw [X, monomial_mul, hexp, one_mul, smul_monomial, smul_eq_mul, hcf, ← nsmul_eq_mul, map_nsmul]

theorem antidiagonal_sum_reindex {N : Type*} [AddCommMonoid N] (s : Finset ι) (k : ℕ) (l : ι) (hl : l ∈ s)
    (F : (ι →₀ ℕ) → N) :
    ∑ g ∈ Finset.finsuppAntidiag s (k + 1), (g l) • F g =
      ∑ f ∈ Finset.finsuppAntidiag s k, (f l + 1) • F (f + Finsupp.single l 1) := by
  classical
  have hone : s.sum (Finsupp.single l 1 : ι →₀ ℕ) = 1 := by
    simp [Finsupp.single_apply, hl]
  rw [← Finset.sum_filter_of_ne (p := fun g : ι →₀ ℕ => g l ≠ 0)
    (fun g _ h h0 => h (by rw [h0, zero_smul]))]
  refine Finset.sum_nbij' (fun g => g - Finsupp.single l 1) (fun f => f + Finsupp.single l 1) ?_ ?_ ?_ ?_ ?_
  · intro g hg
    rw [Finset.mem_filter, Finset.mem_finsuppAntidiag] at hg
    obtain ⟨⟨hsum, hsup⟩, hne⟩ := hg
    have hle : Finsupp.single l 1 ≤ g := by
      rw [Finsupp.single_le_iff]; omega
    have hg' : g = (g - Finsupp.single l 1) + Finsupp.single l 1 := (tsub_add_cancel_of_le hle).symm
    rw [Finset.mem_finsuppAntidiag]
    constructor
    · have : s.sum g = s.sum (g - Finsupp.single l 1 : ι →₀ ℕ) + s.sum (Finsupp.single l 1 : ι →₀ ℕ) := by
        conv_lhs => rw [hg', Finsupp.coe_add]
        exact Finset.sum_add_distrib
      omega
    · intro x hx
      apply hsup
      rw [Finsupp.mem_support_iff] at hx ⊢
      intro h0
      apply hx
      simp [h0]
  · intro f hf
    rw [Finset.mem_finsuppAntidiag] at hf
    rw [Finset.mem_filter, Finset.mem_finsuppAntidiag]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · have : s.sum (f + Finsupp.single l 1 : ι →₀ ℕ) = s.sum f + s.sum (Finsupp.single l 1 : ι →₀ ℕ) := by
        rw [Finsupp.coe_add]
        exact Finset.sum_add_distrib
      omega
    · intro x hx
      by_cases hxl : x = l
      · rw [hxl]; exact hl
      · apply hf.2
        rw [Finsupp.mem_support_iff] at hx ⊢
        simpa [Finsupp.single_apply, Ne.symm hxl] using hx
    · simp
  · intro g hg
    rw [Finset.mem_filter] at hg
    have hle : Finsupp.single l 1 ≤ g := by
      rw [Finsupp.single_le_iff]; have := hg.2; omega
    exact tsub_add_cancel_of_le hle
  · intro f _
    exact add_tsub_cancel_right _ _
  · intro g hg
    rw [Finset.mem_filter] at hg
    have hle : Finsupp.single l 1 ≤ g := by
      rw [Finsupp.single_le_iff]; have := hg.2; omega
    have h1 : (g - Finsupp.single l 1 : ι →₀ ℕ) l + 1 = g l := by
      have := hg.2
      simp only [Finsupp.tsub_apply, Finsupp.single_eq_same]; omega
    rw [h1, tsub_add_cancel_of_le hle]

theorem derivation_sum_divided_power (sg : ι → R) (src dst : ι → σ) (hs : Function.Injective src) (hd : ∀ l l', dst l' ≠ src l)
    (s : Finset ι) (m : σ →₀ ℕ) (k : ℕ) :
    (∑ l ∈ s, dividedPowerDerivation sg src dst l) (dividedPowerSum sg src dst s k m) = (k + 1) • dividedPowerSum sg src dst s (k + 1) m := by
  classical
  simp only [LinearMap.sum_apply, dividedPowerSum, map_sum]
  have h1 : ∀ l ∈ s, ∑ f ∈ Finset.finsuppAntidiag s k, dividedPowerDerivation sg src dst l (dividedPowerTerm sg src dst s m f) =
      ∑ g ∈ Finset.finsuppAntidiag s (k + 1), (g l) • dividedPowerTerm sg src dst s m g := by
    intro l hl
    rw [antidiagonal_sum_reindex s k l hl]
    exact Finset.sum_congr rfl fun f _ => derivation_divided_power_term sg src dst hs hd s m f l hl
  rw [Finset.sum_comm, Finset.sum_congr rfl h1, Finset.sum_comm, Finset.smul_sum]
  refine Finset.sum_congr rfl fun g hg => ?_
  rw [← Finset.sum_smul, (Finset.mem_finsuppAntidiag.1 hg).1]

theorem divided_power_sum_zero (sg : ι → R) (src dst : ι → σ) (s : Finset ι) (m : σ →₀ ℕ) :
    dividedPowerSum sg src dst s 0 m = monomial m 1 := by
  simp [dividedPowerSum, dividedPowerTerm, dividedPowerShiftedExponent, dividedPowerCoeff]

end a1dpAbs

section a1dpCon

variable {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] {n : ℕ}

def dividedPowerSource (LL : Letters ι) (a b : Fin n) (l : ι) : ι × Fin n := if LL.vec l then (l, b) else (l, a)

def dividedPowerTarget (LL : Letters ι) (a b : Fin n) (l : ι) : ι × Fin n := if LL.vec l then (l, a) else (l, b)

def dividedPowerSign (R : Type*) [CommRing R] (LL : Letters ι) (l : ι) : R := if LL.vec l then 1 else -1

theorem divided_power_source_injective (LL : Letters ι) (a b : Fin n) : Function.Injective (dividedPowerSource LL a b) := by
  intro l l' h
  have : (dividedPowerSource LL a b l).1 = (dividedPowerSource LL a b l').1 := by rw [h]
  simpa [dividedPowerSource, apply_ite Prod.fst] using this

theorem divided_power_target_ne_source (LL : Letters ι) (a b : Fin n) (hab : a ≠ b) (l l' : ι) :
    dividedPowerTarget LL a b l' ≠ dividedPowerSource LL a b l := by
  intro h
  have h1 : (dividedPowerTarget LL a b l').1 = (dividedPowerSource LL a b l).1 := by rw [h]
  have h2 : l' = l := by simpa [dividedPowerSource, dividedPowerTarget, apply_ite Prod.fst] using h1
  subst h2
  by_cases hv : LL.vec l' = true
  · simp [dividedPowerSource, dividedPowerTarget, hv, hab] at h
  · simp [dividedPowerSource, dividedPowerTarget, hv, hab.symm] at h

open Classical in
theorem gl_action_eq_sum_derivations (LL : Letters ι) (S : Set ι) (a b : Fin n) :
    glAct R LL S a b = ∑ l ∈ Finset.univ.filter (· ∈ S),
      dividedPowerDerivation (dividedPowerSign R LL) (dividedPowerSource LL a b) (dividedPowerTarget LL a b) l := by
  rw [Finset.sum_filter]
  unfold glAct
  refine Finset.sum_congr rfl fun l _ => ?_
  by_cases hS : l ∈ S
  · by_cases hv : LL.vec l = true <;> simp [hS, hv, dividedPowerDerivation, dividedPowerSign, dividedPowerSource, dividedPowerTarget]
  · simp [hS]

open Classical in
theorem divided_power_monomial_eq_sum (LL : Letters ι) (S : Set ι) (a b : Fin n) (k : ℕ) (m : ι × Fin n →₀ ℕ) :
    divPowMono R LL S a b k m =
      dividedPowerSum (dividedPowerSign R LL) (dividedPowerSource LL a b) (dividedPowerTarget LL a b) (Finset.univ.filter (· ∈ S)) k m := by
  unfold divPowMono dividedPowerSum dividedPowerTerm
  refine Finset.sum_congr rfl fun f hf => ?_
  have hsup := (Finset.mem_finsuppAntidiag.1 hf).2
  have he : ((m - ∑ l ∈ f.support, Finsupp.single (if LL.vec l then (l, b) else (l, a)) (f l))
        + ∑ l ∈ f.support, Finsupp.single (if LL.vec l then (l, a) else (l, b)) (f l)) =
      dividedPowerShiftedExponent (dividedPowerSource LL a b) (dividedPowerTarget LL a b) m f := rfl
  have hc : (∏ l ∈ f.support, (if LL.vec l then ((m (l, b)).choose (f l) : R)
        else (-1 : R) ^ (f l) * ((m (l, a)).choose (f l) : R))) =
      dividedPowerCoeff (dividedPowerSign R LL) (dividedPowerSource LL a b) (Finset.univ.filter (· ∈ S)) m f := by
    unfold dividedPowerCoeff
    rw [← Finset.prod_subset hsup]
    · refine Finset.prod_congr rfl fun l _ => ?_
      by_cases hv : LL.vec l = true <;> simp [hv, dividedPowerSign, dividedPowerSource]
    · intro l _ hl
      have : f l = 0 := by simpa using hl
      simp [this]
  rw [he, hc]

theorem gl_action_comp_divided_power (LL : Letters ι) (S : Set ι) (a b : Fin n) (hab : a ≠ b) (k : ℕ) :
    glAct R LL S a b ∘ₗ divPow R LL S a b k = (k + 1) • divPow R LL S a b (k + 1) := by
  classical
  refine (MvPolynomial.basisMonomials (ι × Fin n) R).ext fun m => ?_
  simp only [LinearMap.comp_apply, LinearMap.smul_apply, divPow, Module.Basis.constr_basis]
  rw [divided_power_monomial_eq_sum, divided_power_monomial_eq_sum, gl_action_eq_sum_derivations]
  exact derivation_sum_divided_power _ _ _ (divided_power_source_injective LL a b) (divided_power_target_ne_source LL a b hab) _ m k

theorem divided_power_zero (LL : Letters ι) (S : Set ι) (a b : Fin n) : divPow R LL S a b 0 = LinearMap.id := by
  classical
  refine (MvPolynomial.basisMonomials (ι × Fin n) R).ext fun m => ?_
  simp only [divPow, Module.Basis.constr_basis, LinearMap.id_apply]
  rw [divided_power_monomial_eq_sum, divided_power_sum_zero, coe_basisMonomials]

theorem gl_action_pow_eq_factorial_smul (LL : Letters ι) (S : Set ι) (a b : Fin n) (hab : a ≠ b) (k : ℕ) :
    (glAct R LL S a b : Module.End R (MvPolynomial (ι × Fin n) R)) ^ k = k.factorial • divPow R LL S a b k := by
  induction k with
  | zero => simp [divided_power_zero]; rfl
  | succ k ih =>
    rw [pow_succ', ih, mul_smul_comm, Module.End.mul_eq_comp, gl_action_comp_divided_power LL S a b hab k, smul_smul,
      Nat.factorial_succ, mul_comm]

end a1dpCon

theorem positive_path_ext {n N : ℕ} {LL : Letters (Fin N)} {B : Fin N → ℕ} {P Q : PPath n N LL B} (h : P.mu = Q.mu) :
    P = Q := by
  cases P; cases Q; cases h; rfl

theorem column_kernel_fin_zero {R : Type*} [CommRing R] {N : ℕ} (mu : Fin (N + 1) → Fin 0 → ℤ) (c : ℤ) (j : ℕ)
    (J : Finset (Fin 0)) : Kcol R mu c j J = 1 := by
  induction j with
  | zero => simp [Kcol, extOne, Finset.eq_empty_of_isEmpty J]
  | succ j ih =>
    simp only [Kcol]
    split_ifs with h
    · simpa [colStep, colH] using ih
    · exact ih

theorem Psi_fin_zero {R : Type*} [CommRing R] {N : ℕ} (mu : Fin (N + 1) → Fin 0 → ℤ) (I : ℤ → Finset (Fin 0)) :
    Psi R mu I = 1 := by
  simp [Psi, column_kernel_fin_zero]

theorem canonical_Psi_ne_zero_of_path_basis (D : Formalism.BasicNotions.D7) (h17 : PathBasisOverRing D) (R : Type) [CommRing R] [Nontrivial R] {N n : ℕ}
    {LL : Letters (Fin N)} {B : Fin N → ℕ} (P : PPath n N LL B) : Psi R P.mu (Ican P.mu) ≠ 0 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [Psi_fin_zero]; exact one_ne_zero
  · have : NeZero n := ⟨hn.ne'⟩
    have hli := (h17 R N n LL B).1
    have := hli.ne_zero (⟨(P, Ican P.mu), canonical_tableau_standard (P.dom _)⟩ :
      {x : PPath n N LL B × (ℤ → Finset (Fin n)) // IsSt x.1.mu x.2})
    exact this

theorem canonical_Psi_linear_independent (D : Formalism.BasicNotions.D7) (h17 : PathBasisOverRing D) (F : Type) [Field F] {N n : ℕ}
    (LL : Letters (Fin N)) (B : Fin N → ℕ) (mu : Fin n → ℤ) :
    LinearIndependent F (fun P : {P : PPath n N LL B // pEnd P.mu = mu} => Psi F P.1.mu (Ican P.1.mu)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have : Subsingleton {P : PPath 0 N LL B // pEnd P.mu = mu} :=
      ⟨fun P Q => Subtype.ext (positive_path_ext (funext fun i => funext fun a => a.elim0))⟩
    rw [linearIndependent_subsingleton_index_iff]
    intro P
    rw [Psi_fin_zero]; exact one_ne_zero
  · have : NeZero n := ⟨hn.ne'⟩
    refine ((h17 F N n LL B).1).comp
      (fun P : {P : PPath n N LL B // pEnd P.mu = mu} =>
        (⟨(P.1, Ican P.1.mu), canonical_tableau_standard (P.1.dom _)⟩ :
          {x : PPath n N LL B × (ℤ → Finset (Fin n)) // IsSt x.1.mu x.2})) ?_
    intro P Q h
    exact Subtype.ext (congrArg (fun x => x.1.1) h)

theorem divPow_monomial_eq_smul {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] {n : ℕ} (LL : Letters ι) (S : Set ι)
    (a b : Fin n) (k : ℕ) (m : ι × Fin n →₀ ℕ) (c : R) :
    divPow R LL S a b k (monomial m c) = c • divPowMono R LL S a b k m := by
  have : monomial m c = c • (MvPolynomial.basisMonomials (ι × Fin n) R) m := by
    rw [coe_basisMonomials, smul_monomial, smul_eq_mul, mul_one]
  rw [this, map_smul, divPow, Module.Basis.constr_basis]

theorem map_divided_power_monomial {R R' : Type*} [CommRing R] [CommRing R'] (φ : R →+* R') {ι : Type*} [Fintype ι] {n : ℕ}
    (LL : Letters ι) (S : Set ι) (a b : Fin n) (k : ℕ) (m : ι × Fin n →₀ ℕ) :
    MvPolynomial.map φ (divPowMono R LL S a b k m) = divPowMono R' LL S a b k m := by
  classical
  unfold divPowMono
  rw [map_sum]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [MvPolynomial.map_monomial, map_prod]
  congr 1
  refine Finset.prod_congr rfl fun l _ => ?_
  split_ifs <;> simp

theorem map_divided_power {R R' : Type*} [CommRing R] [CommRing R'] (φ : R →+* R') {ι : Type*} [Fintype ι] {n : ℕ}
    (LL : Letters ι) (S : Set ι) (a b : Fin n) (k : ℕ) (G : MvPolynomial (ι × Fin n) R) :
    MvPolynomial.map φ (divPow R LL S a b k G) = divPow R' LL S a b k (MvPolynomial.map φ G) := by
  induction G using MvPolynomial.induction_on' with
  | monomial m c =>
    rw [divPow_monomial_eq_smul, MvPolynomial.map_monomial, divPow_monomial_eq_smul, MvPolynomial.smul_eq_C_mul, map_mul,
      MvPolynomial.map_C, map_divided_power_monomial, MvPolynomial.smul_eq_C_mul]
  | add p q hp hq => rw [map_add, map_add, map_add, map_add, hp, hq]

theorem divided_power_zero_of_gl_action_zero {ι : Type*} [Fintype ι] {n : ℕ} (LL : Letters ι) (S : Set ι) (a b : Fin n) (hab : a ≠ b)
    (G : MvPolynomial (ι × Fin n) ℤ) (hG : glAct ℤ LL S a b G = 0) (R : Type*) [CommRing R] (k : ℕ) (hk : 1 ≤ k) :
    divPow R LL S a b k (MvPolynomial.map (Int.castRingHom R) G) = 0 := by
  have h1 : ((glAct ℤ LL S a b : Module.End ℤ (MvPolynomial (ι × Fin n) ℤ)) ^ k) G = 0 := by
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [pow_succ, Module.End.mul_apply, hG, map_zero]
  rw [gl_action_pow_eq_factorial_smul LL S a b hab k, LinearMap.smul_apply] at h1
  have h2 : divPow ℤ LL S a b k G = 0 := by
    rcases smul_eq_zero.1 h1 with h | h
    · exact absurd h (Nat.factorial_ne_zero k)
    · exact h
  rw [← map_divided_power, h2, map_zero]

section car

variable {n : ℕ} {P : Type*} [CommRing P]

def exteriorSign (P : Type*) [CommRing P] {n : ℕ} (J : Finset (Fin n)) (m : Fin n) : P :=
  (-1) ^ (J.filter fun j => m < j).card

theorem exterior_sign_mul_self (J : Finset (Fin n)) (m : Fin n) : exteriorSign P J m * exteriorSign P J m = 1 := by
  unfold exteriorSign; rw [← pow_add, ← two_mul, pow_mul]; simp

theorem exterior_sign_erase (a b : Fin n) (J : Finset (Fin n)) :
    exteriorSign P (J.erase a) b = (if a ∈ J ∧ b < a then -1 else 1) * exteriorSign P J b := by
  unfold exteriorSign
  have e : (J.erase a).filter (fun j => b < j) = (J.filter fun j => b < j).erase a := by
    ext x; simp only [mem_filter, mem_erase]; tauto
  rw [e]
  split_ifs with h
  · have hm : a ∈ J.filter fun j => b < j := mem_filter.2 h
    have hc := Finset.card_erase_add_one hm
    rw [← hc, pow_succ]; ring
  · rw [Finset.erase_eq_of_notMem (by rw [mem_filter]; exact h), one_mul]

theorem exterior_sign_insert (a b : Fin n) (J : Finset (Fin n)) :
    exteriorSign P (insert a J) b = (if a ∉ J ∧ b < a then -1 else 1) * exteriorSign P J b := by
  unfold exteriorSign
  by_cases ha : a ∈ J
  · rw [Finset.insert_eq_of_mem ha]; simp [ha]
  · rw [Finset.filter_insert]
    by_cases hb : b < a
    · rw [if_pos hb, Finset.card_insert_of_notMem (by simp [ha]), if_pos ⟨ha, hb⟩, pow_succ]; ring
    · rw [if_neg hb, if_neg (by tauto), one_mul]

def exteriorWedge (P : Type*) [CommRing P] {n : ℕ} (m : Fin n) : Module.End P (Finset (Fin n) → P) where
  toFun K := fun J => if m ∈ J then exteriorSign P J m * K (J.erase m) else 0
  map_add' K K' := by funext J; simp only [Pi.add_apply]; split_ifs <;> ring
  map_smul' c K := by funext J; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; split_ifs <;> ring

def exteriorContraction (P : Type*) [CommRing P] {n : ℕ} (m : Fin n) : Module.End P (Finset (Fin n) → P) where
  toFun K := fun J => if m ∈ J then 0 else exteriorSign P J m * K (insert m J)
  map_add' K K' := by funext J; simp only [Pi.add_apply]; split_ifs <;> ring
  map_smul' c K := by funext J; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; split_ifs <;> ring

theorem exterior_wedge_apply (m : Fin n) (K : Finset (Fin n) → P) (J : Finset (Fin n)) :
    exteriorWedge P m K J = if m ∈ J then exteriorSign P J m * K (J.erase m) else 0 := rfl

theorem exterior_contraction_apply (m : Fin n) (K : Finset (Fin n) → P) (J : Finset (Fin n)) :
    exteriorContraction P m K J = if m ∈ J then 0 else exteriorSign P J m * K (insert m J) := rfl

theorem sign_flip_of_ne {a b : Fin n} (hab : a ≠ b) : (if b < a then (-1 : P) else 1) = -(if a < b then (-1 : P) else 1) := by
  rcases lt_or_gt_of_ne hab with h | h
  · rw [if_neg (not_lt.2 h.le), if_pos h]; ring
  · rw [if_pos h, if_neg (not_lt.2 h.le)]

theorem wedge_contraction_anticommute (a b : Fin n) :
    exteriorWedge P a * exteriorContraction P b + exteriorContraction P b * exteriorWedge P a = if a = b then 1 else 0 := by
  refine LinearMap.ext fun K => funext fun J => ?_
  simp only [LinearMap.add_apply, Module.End.mul_apply, Pi.add_apply, exterior_wedge_apply, exterior_contraction_apply]
  by_cases hab : a = b
  · subst hab
    rw [if_pos rfl]
    by_cases ha : a ∈ J
    · simp only [ha, if_true, Finset.mem_erase, ne_eq, not_true_eq_false, false_and, if_false, exterior_sign_erase,
        lt_self_iff_false, and_false, one_mul, Finset.insert_erase ha, add_zero, ← mul_assoc, exterior_sign_mul_self,
        Module.End.one_apply]
    · simp only [ha, if_false, Finset.mem_insert, true_or, if_true, exterior_sign_insert,
        lt_self_iff_false, and_false, one_mul, Finset.erase_insert ha, zero_add, ← mul_assoc, exterior_sign_mul_self,
        Module.End.one_apply]
  · rw [if_neg hab]
    have hba : b ≠ a := fun h => hab h.symm
    by_cases ha : a ∈ J <;> by_cases hb : b ∈ J
    · simp [ha, hb, hba]
    · have e : (insert b J).erase a = insert b (J.erase a) := Finset.erase_insert_of_ne hba
      simp only [ha, hb, if_true, if_false, Finset.mem_erase, Finset.mem_insert, and_false, or_true, exterior_sign_erase,
        exterior_sign_insert, true_and, not_false_eq_true, e, sign_flip_of_ne hab, LinearMap.zero_apply, Pi.zero_apply]
      ring
    · simp [ha, hb]
    · simp [ha, hb, hab]

theorem wedge_anticommute (a b : Fin n) : exteriorWedge P a * exteriorWedge P b = -(exteriorWedge P b * exteriorWedge P a) := by
  refine LinearMap.ext fun K => funext fun J => ?_
  simp only [LinearMap.neg_apply, Module.End.mul_apply, Pi.neg_apply, exterior_wedge_apply]
  by_cases hab : a = b
  · subst hab; simp
  · have hba : b ≠ a := fun h => hab h.symm
    by_cases ha : a ∈ J <;> by_cases hb : b ∈ J
    · simp only [ha, hb, if_true, Finset.mem_erase, ne_eq, hab, hba, not_false_eq_true, and_self, exterior_sign_erase,
        true_and, Finset.erase_right_comm (a := a) (b := b), sign_flip_of_ne hab]
      ring
    · simp [ha, hb]
    · simp [ha, hb]
    · simp [ha, hb]

theorem contraction_anticommute (a b : Fin n) : exteriorContraction P a * exteriorContraction P b = -(exteriorContraction P b * exteriorContraction P a) := by
  refine LinearMap.ext fun K => funext fun J => ?_
  simp only [LinearMap.neg_apply, Module.End.mul_apply, Pi.neg_apply, exterior_contraction_apply]
  by_cases hab : a = b
  · subst hab; simp
  · have hba : b ≠ a := fun h => hab h.symm
    by_cases ha : a ∈ J <;> by_cases hb : b ∈ J
    · simp [ha, hb]
    · simp [ha, hb]
    · simp [ha, hb]
    · simp only [ha, hb, if_false, Finset.mem_insert, hab, hba, or_self, exterior_sign_insert,
        true_and, not_false_eq_true, Finset.insert_comm a b, sign_flip_of_ne hab]
      ring

theorem commutator_wedge (a b m : Fin n) :
    (exteriorWedge P b * exteriorContraction P a) * exteriorWedge P m - exteriorWedge P m * (exteriorWedge P b * exteriorContraction P a) = if a = m then exteriorWedge P b else 0 := by
  have h1 : exteriorContraction P a * exteriorWedge P m = (if m = a then 1 else 0) - exteriorWedge P m * exteriorContraction P a := by
    rw [← wedge_contraction_anticommute m a]; abel
  have h2 := wedge_anticommute (P := P) b m
  calc (exteriorWedge P b * exteriorContraction P a) * exteriorWedge P m - exteriorWedge P m * (exteriorWedge P b * exteriorContraction P a)
      = exteriorWedge P b * (exteriorContraction P a * exteriorWedge P m) - exteriorWedge P m * exteriorWedge P b * exteriorContraction P a := by simp only [mul_assoc]
    _ = exteriorWedge P b * (if m = a then 1 else 0) - (exteriorWedge P b * exteriorWedge P m + exteriorWedge P m * exteriorWedge P b) * exteriorContraction P a := by
        rw [h1, mul_sub, add_mul]; simp only [mul_assoc]; abel
    _ = if a = m then exteriorWedge P b else 0 := by
        rw [h2]; by_cases h : a = m
        · subst h; simp
        · have h' : m ≠ a := fun e => h e.symm
          simp [h, h']

theorem commutator_contraction (a b m : Fin n) :
    (exteriorWedge P b * exteriorContraction P a) * exteriorContraction P m - exteriorContraction P m * (exteriorWedge P b * exteriorContraction P a) = if m = b then -exteriorContraction P a else 0 := by
  have h1 : exteriorContraction P m * exteriorWedge P b = (if b = m then 1 else 0) - exteriorWedge P b * exteriorContraction P m := by
    rw [← wedge_contraction_anticommute b m]; abel
  have h2 := contraction_anticommute (P := P) a m
  calc (exteriorWedge P b * exteriorContraction P a) * exteriorContraction P m - exteriorContraction P m * (exteriorWedge P b * exteriorContraction P a)
      = exteriorWedge P b * (exteriorContraction P a * exteriorContraction P m) - (exteriorContraction P m * exteriorWedge P b) * exteriorContraction P a := by simp only [mul_assoc]
    _ = exteriorWedge P b * (exteriorContraction P a * exteriorContraction P m + exteriorContraction P m * exteriorContraction P a) - (if b = m then 1 else 0) * exteriorContraction P a := by
        rw [h1, sub_mul, mul_add]; simp only [mul_assoc]; abel
    _ = if m = b then -exteriorContraction P a else 0 := by
        rw [h2]; by_cases h : m = b
        · subst h; simp
        · have h' : b ≠ m := fun e => h e.symm
          simp [h, h']

theorem right_wedge_eq_sum (x : Fin n → P) (K : Finset (Fin n) → P) : wedgeR x K = ∑ m, x m • exteriorWedge P m K := by
  funext J
  rw [Finset.sum_apply]
  unfold wedgeR
  rw [← Finset.sum_subset (Finset.subset_univ J)]
  · refine Finset.sum_congr rfl fun m hm => ?_
    rw [Pi.smul_apply, exterior_wedge_apply, if_pos hm, smul_eq_mul]; unfold exteriorSign; ring
  · intro m _ hm
    rw [Pi.smul_apply, exterior_wedge_apply, if_neg hm, smul_zero]

theorem right_contraction_eq_sum (x : Fin n → P) (K : Finset (Fin n) → P) : contrR x K = ∑ m, x m • exteriorContraction P m K := by
  funext J
  rw [Finset.sum_apply]
  unfold contrR
  rw [← Finset.sum_subset (Finset.subset_univ (univ \ J))]
  · refine Finset.sum_congr rfl fun m hm => ?_
    have hm' : m ∉ J := (Finset.mem_sdiff.1 hm).2
    rw [Pi.smul_apply, exterior_contraction_apply, if_neg hm', smul_eq_mul]; unfold exteriorSign; ring
  · intro m _ hm
    have hm' : m ∈ J := by simpa using hm
    rw [Pi.smul_apply, exterior_contraction_apply, if_pos hm', smul_zero]

end car

section der

theorem derivation_exterior_induction {n : ℕ} {P : Type*} [CommRing P] (D : P →+ P) (hD : ∀ u v, D (u * v) = u * D v + v * D u)
    (o : Fin n → Module.End P (Finset (Fin n) → P))
    (ho : ∀ m K J, D (o m K J) = o m (fun J => D (K J)) J) (T : Module.End P (Finset (Fin n) → P))
    (x : Fin n → P) (K : Finset (Fin n) → P) (hK : ∀ J, D (K J) = T K J)
    (hc : ∑ m, x m • (T * o m - o m * T) K = ∑ m, D (x m) • o m K) (J : Finset (Fin n)) :
    D ((∑ m, x m • o m K) J) = T (∑ m, x m • o m K) J := by
  have hK' : (fun J => D (K J)) = T K := funext hK
  have h := congrFun hc J
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, LinearMap.sub_apply, Module.End.mul_apply,
    Pi.sub_apply] at h
  rw [map_sum, Finset.sum_apply, Finset.sum_apply, map_sum]
  simp only [Pi.smul_apply, smul_eq_mul, map_smul, hD, ho, hK']
  rw [Finset.sum_add_distrib]
  have h2 : ∑ m, o m K J * D (x m) = ∑ m, D (x m) * o m K J := Finset.sum_congr rfl fun m _ => mul_comm _ _
  rw [h2, ← h, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun m _ => by ring

theorem sum_ite_eq_left_smul {n : ℕ} {P F : Type*} [CommRing P] [AddCommGroup F] [Module P F] (x : Fin n → P) (a : Fin n)
    (A : Module.End P F) (K : F) : ∑ m, x m • ((if a = m then A else 0 : Module.End P F) K) = x a • A K := by
  rw [Finset.sum_eq_single a]
  · simp
  · intro m _ hm; simp [Ne.symm hm]
  · simp

theorem sum_ite_eq_left_smul' {n : ℕ} {P F : Type*} [CommRing P] [AddCommGroup F] [Module P F] (x : Fin n → P) (a : Fin n)
    (A : Module.End P F) (K : F) : ∑ m, x m • ((if m = a then A else 0 : Module.End P F) K) = x a • A K := by
  rw [Finset.sum_eq_single a]
  · simp
  · intro m _ hm; simp [hm]
  · simp

theorem sum_ite_eq_right_smul {n : ℕ} {P F : Type*} [CommRing P] [AddCommGroup F] [Module P F] (y : P) (b : Fin n)
    (o : Fin n → Module.End P F) (K : F) : ∑ m, (if m = b then y else 0) • o m K = y • o b K := by
  rw [Finset.sum_eq_single b]
  · simp
  · intro m _ hm; simp [hm]
  · simp

variable {R : Type*} [CommRing R] {N n : ℕ} (LL : Letters (Fin N))

theorem gl_action_mul (S : Set (Fin N)) (a b : Fin n) (u v : MvPolynomial (Fin N × Fin n) R) :
    glAct R LL S a b (u * v) = u * glAct R LL S a b v + v * glAct R LL S a b u := by
  classical
  unfold glAct
  simp only [LinearMap.sum_apply]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  split_ifs <;> simp [Derivation.leibniz] <;> ring

theorem gl_action_X (a b : Fin n) (l : Fin N) (m : Fin n) :
    glAct R LL Set.univ a b (X (l, m)) =
      if LL.vec l then (if m = b then X (l, a) else 0) else (if m = a then -X (l, b) else 0) := by
  classical
  unfold glAct
  rw [LinearMap.sum_apply, Finset.sum_eq_single l]
  · by_cases hv : LL.vec l = true
    · by_cases hm : m = b <;> simp [hv, hm, pderiv_X]
    · by_cases hm : m = a <;> simp [hv, hm, pderiv_X]
  · intro l' _ hne
    have hne' : l ≠ l' := fun e => hne e.symm
    by_cases hv : LL.vec l' = true <;> simp [hv, pderiv_X, hne']
  · intro h; exact absurd (Finset.mem_univ l) h

theorem gl_action_one (S : Set (Fin N)) (a b : Fin n) : glAct R LL S a b 1 = 0 := by
  have := gl_action_mul (R := R) LL S a b 1 1
  simpa using this

theorem linear_map_exterior_sign_mul (D : MvPolynomial (Fin N × Fin n) R →ₗ[R] MvPolynomial (Fin N × Fin n) R) (J : Finset (Fin n))
    (m : Fin n) (y : MvPolynomial (Fin N × Fin n) R) :
    D (exteriorSign _ J m * y) = exteriorSign _ J m * D y := by
  unfold exteriorSign
  rcases neg_one_pow_eq_or (MvPolynomial (Fin N × Fin n) R) (J.filter fun j => m < j).card with h | h <;>
    rw [h] <;> simp

theorem linear_map_exterior_wedge (D : MvPolynomial (Fin N × Fin n) R →ₗ[R] MvPolynomial (Fin N × Fin n) R) (m : Fin n)
    (K : Finset (Fin n) → MvPolynomial (Fin N × Fin n) R) (J : Finset (Fin n)) :
    D (exteriorWedge _ m K J) = exteriorWedge _ m (fun J => D (K J)) J := by
  rw [exterior_wedge_apply, exterior_wedge_apply]
  split_ifs
  · exact linear_map_exterior_sign_mul D J m _
  · exact map_zero D

theorem linear_map_exterior_contraction (D : MvPolynomial (Fin N × Fin n) R →ₗ[R] MvPolynomial (Fin N × Fin n) R) (m : Fin n)
    (K : Finset (Fin n) → MvPolynomial (Fin N × Fin n) R) (J : Finset (Fin n)) :
    D (exteriorContraction _ m K J) = exteriorContraction _ m (fun J => D (K J)) J := by
  rw [exterior_contraction_apply, exterior_contraction_apply]
  split_ifs
  · exact map_zero D
  · exact linear_map_exterior_sign_mul D J m _

theorem column_height_mono {nu mu : Fin n → ℤ} (h : ∀ a, nu a ≤ mu a) (c : ℤ) : colH nu c ≤ colH mu c := by
  unfold colH
  refine Finset.card_le_card fun m hm => ?_
  rw [Finset.mem_filter] at hm ⊢
  exact ⟨hm.1, hm.2.trans (h m)⟩

def columnOperator (P : Type*) [CommRing P] {n : ℕ} (a b : Fin n) (c : ℤ) : Module.End P (Finset (Fin n) → P) :=
  if 1 ≤ c then exteriorWedge P b * exteriorContraction P a else -(exteriorWedge P a * exteriorContraction P b)

theorem gl_action_column_kernel {B : Fin N → ℕ} (Pa : PPath n N LL B) (a b : Fin n) (c : ℤ) (j : ℕ) (J : Finset (Fin n)) :
    glAct R LL Set.univ a b (Kcol R Pa.mu c j J) = columnOperator _ a b c (Kcol R Pa.mu c j) J := by
  induction j generalizing J with
  | zero =>
    have h0 : glAct R LL Set.univ a b (Kcol R Pa.mu c 0 J) = 0 := by
      simp only [Kcol, extOne]
      split_ifs
      · exact gl_action_one LL _ a b
      · exact map_zero _
    rw [h0]
    unfold columnOperator
    split_ifs <;> simp [Kcol, exterior_wedge_apply, exterior_contraction_apply, extOne]
  | succ j ih =>
    simp only [Kcol]
    split_ifs with h
    · have hst := Pa.step ⟨j, h⟩
      set x := letVec (n := n) R (⟨j, h⟩ : Fin N) with hx
      set K := Kcol R Pa.mu c j with hKdef
      have hDx : ∀ m, glAct R LL Set.univ a b (x m) =
          if LL.vec ⟨j, h⟩ then (if m = b then x a else 0) else (if m = a then -x b else 0) := fun m =>
        gl_action_X LL a b _ m
      have hmul := gl_action_mul (R := R) LL Set.univ a b
      by_cases hv : LL.vec ⟨j, h⟩ = true
      · rw [if_pos hv] at hst
        have hle : colH (Pa.mu ⟨j, by omega⟩) c ≤ colH (Pa.mu ⟨j + 1, by omega⟩) c := column_height_mono hst.1 c
        simp only [hv, if_true] at hDx
        unfold colStep
        by_cases hlt : colH (Pa.mu ⟨j, by omega⟩) c < colH (Pa.mu ⟨j + 1, by omega⟩) c
        · rw [if_pos hlt]
          by_cases hc : 1 ≤ c
          · rw [if_pos hc, right_wedge_eq_sum]
            refine derivation_exterior_induction (glAct R LL Set.univ a b).toAddMonoidHom hmul (exteriorWedge _) (linear_map_exterior_wedge _) _ x K ih ?_ J
            simp only [columnOperator, if_pos hc, commutator_wedge, LinearMap.toAddMonoidHom_coe, hDx]
            rw [sum_ite_eq_left_smul, sum_ite_eq_right_smul]
          · rw [if_neg hc, right_contraction_eq_sum]
            refine derivation_exterior_induction (glAct R LL Set.univ a b).toAddMonoidHom hmul (exteriorContraction _) (linear_map_exterior_contraction _) _ x K ih ?_ J
            have e : ∀ m, (-(exteriorWedge (MvPolynomial (Fin N × Fin n) R) a * exteriorContraction _ b)) * exteriorContraction _ m -
                exteriorContraction _ m * (-(exteriorWedge _ a * exteriorContraction _ b)) = if m = a then exteriorContraction _ b else 0 := by
              intro m
              have := commutator_contraction (P := MvPolynomial (Fin N × Fin n) R) b a m
              rw [neg_mul, mul_neg, sub_neg_eq_add, neg_add_eq_sub, ← neg_sub, this]
              split_ifs <;> simp
            simp only [columnOperator, if_neg hc, e, LinearMap.toAddMonoidHom_coe, hDx]
            rw [sum_ite_eq_left_smul', sum_ite_eq_right_smul]
        · rw [if_neg hlt, if_neg (by omega)]
          exact ih J
      · rw [if_neg hv] at hst
        have hle : colH (Pa.mu ⟨j + 1, by omega⟩) c ≤ colH (Pa.mu ⟨j, by omega⟩) c := column_height_mono hst.1 c
        have hv' : LL.vec ⟨j, h⟩ = false := by simpa using hv
        simp only [hv', Bool.false_eq_true, if_false] at hDx
        unfold colStep
        rw [if_neg (by omega)]
        by_cases hlt : colH (Pa.mu ⟨j + 1, by omega⟩) c < colH (Pa.mu ⟨j, by omega⟩) c
        · rw [if_pos hlt]
          by_cases hc : 1 ≤ c
          · rw [if_pos hc, right_contraction_eq_sum]
            refine derivation_exterior_induction (glAct R LL Set.univ a b).toAddMonoidHom hmul (exteriorContraction _) (linear_map_exterior_contraction _) _ x K ih ?_ J
            simp only [columnOperator, if_pos hc, commutator_contraction, LinearMap.toAddMonoidHom_coe, hDx]
            rw [sum_ite_eq_left_smul', sum_ite_eq_right_smul]
            simp
          · rw [if_neg hc, right_wedge_eq_sum]
            refine derivation_exterior_induction (glAct R LL Set.univ a b).toAddMonoidHom hmul (exteriorWedge _) (linear_map_exterior_wedge _) _ x K ih ?_ J
            have e : ∀ m, (-(exteriorWedge (MvPolynomial (Fin N × Fin n) R) a * exteriorContraction _ b)) * exteriorWedge _ m -
                exteriorWedge _ m * (-(exteriorWedge _ a * exteriorContraction _ b)) = if b = m then -exteriorWedge _ a else 0 := by
              intro m
              have := commutator_wedge (P := MvPolynomial (Fin N × Fin n) R) b a m
              rw [neg_mul, mul_neg, sub_neg_eq_add, neg_add_eq_sub, ← neg_sub, this]
              split_ifs <;> simp
            simp only [columnOperator, if_neg hc, e, LinearMap.toAddMonoidHom_coe, hDx]
            rw [sum_ite_eq_left_smul, sum_ite_eq_right_smul]
            simp
        · rw [if_neg hlt]
          exact ih J
    · exact ih J

theorem column_operator_canonical_eq_zero {P : Type*} [CommRing P] {mu : Fin (N + 1) → Fin n → ℤ} {a b : Fin n} (hab : a < b) (c : ℤ)
    (K : Finset (Fin n) → P) : columnOperator P a b c K (Ican mu c) = 0 := by
  unfold columnOperator Ican
  by_cases hc : 1 ≤ c
  · simp only [if_pos hc, Module.End.mul_apply, exterior_wedge_apply, exterior_contraction_apply]
    split_ifs with h1 h2
    · rw [mul_zero]
    · exfalso
      apply h2
      rw [Finset.mem_filter] at h1
      rw [Finset.mem_erase, Finset.mem_filter]
      exact ⟨hab.ne, mem_univ _, lt_trans (Fin.lt_def.1 hab) h1.2⟩
    · rfl
  · simp only [if_neg hc, LinearMap.neg_apply, Pi.neg_apply, Module.End.mul_apply, exterior_wedge_apply, exterior_contraction_apply]
    split_ifs with h1 h2
    · simp
    · exfalso
      apply h2
      rw [Finset.mem_filter] at h1
      rw [Finset.mem_erase, Finset.mem_filter]
      exact ⟨hab.ne', mem_univ _, h1.2.trans (Fin.lt_def.1 hab).le⟩
    · simp

theorem gl_action_canonical_Psi_eq_zero {B : Fin N → ℕ} (Pa : PPath n N LL B) (a b : Fin n) (hab : a < b) :
    glAct R LL Set.univ a b (Psi R Pa.mu (Ican Pa.mu)) = 0 := by
  unfold Psi
  induction colRange Pa.mu using Finset.induction_on with
  | empty => rw [Finset.prod_empty]; exact gl_action_one LL _ a b
  | insert c s hc ih =>
    rw [Finset.prod_insert hc, gl_action_mul, ih, gl_action_column_kernel, column_operator_canonical_eq_zero hab]
    simp

end der

section wt

variable {N n : ℕ} (LL : Letters (Fin N))

theorem X_mul_pderiv_monomial_bis {R σ : Type*} [CommRing R] (v : σ) (m : σ →₀ ℕ) (c : R) :
    X v * pderiv v (monomial m c) = monomial m ((m v : R) * c) := by
  classical
  rw [pderiv_monomial]
  by_cases h : m v = 0
  · simp [h]
  · have hle : Finsupp.single v 1 ≤ m := Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 h)
    rw [X, monomial_mul, one_mul, add_tsub_cancel_of_le hle, mul_comm]

theorem gl_action_diag_monomial (S : Set (Fin N)) (a : Fin n) (m : Fin N × Fin n →₀ ℕ) (c : ℤ) :
    glAct ℤ LL S a a (monomial m c) = monomial m (wtS LL S m a * c) := by
  classical
  unfold glAct wtS
  rw [LinearMap.sum_apply, Finset.sum_mul, map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  have key := X_mul_pderiv_monomial_bis (R := ℤ) (l, a) m c
  rw [pderiv_monomial] at key
  split_ifs <;> simp [key]

theorem coeff_gl_action_diag (S : Set (Fin N)) (a : Fin n) (m : Fin N × Fin n →₀ ℕ) (G : MvPolynomial (Fin N × Fin n) ℤ) :
    coeff m (glAct ℤ LL S a a G) = wtS LL S m a * coeff m G := by
  classical
  induction G using MvPolynomial.induction_on' with
  | monomial m' c =>
    rw [gl_action_diag_monomial, coeff_monomial, coeff_monomial]
    split_ifs with h
    · rw [h]
    · rw [mul_zero]
  | add p q hp hq => rw [map_add, coeff_add, coeff_add, hp, hq, mul_add]

theorem weight_eq_of_eigen (S : Set (Fin N)) (a : Fin n) (G : MvPolynomial (Fin N × Fin n) ℤ) (lam : ℤ)
    (h : glAct ℤ LL S a a G = lam • G) (m : Fin N × Fin n →₀ ℕ) (hm : m ∈ G.support) : wtS LL S m a = lam := by
  have h1 := coeff_gl_action_diag LL S a m G
  rw [h, coeff_smul, smul_eq_mul] at h1
  exact (mul_right_cancel₀ (mem_support_iff.1 hm) h1).symm

theorem column_operator_diag {P : Type*} [CommRing P] (a : Fin n) (c : ℤ) (K : Finset (Fin n) → P) (J : Finset (Fin n)) :
    columnOperator P a a c K J = (if 1 ≤ c then (if a ∈ J then (1 : ℤ) else 0) else (if a ∈ J then -1 else 0)) • K J := by
  have key : (exteriorWedge P a * exteriorContraction P a) K J = if a ∈ J then K J else 0 := by
    rw [Module.End.mul_apply, exterior_wedge_apply, exterior_contraction_apply]
    by_cases ha : a ∈ J
    · rw [if_pos ha, if_pos ha, if_neg (Finset.notMem_erase a J), exterior_sign_erase, Finset.insert_erase ha]
      simp only [lt_self_iff_false, and_false, if_false, one_mul]
      rw [← mul_assoc, exterior_sign_mul_self, one_mul]
    · rw [if_neg ha, if_neg ha]
  unfold columnOperator
  by_cases hc : 1 ≤ c
  · rw [if_pos hc, if_pos hc, key]; split_ifs <;> simp
  · rw [if_neg hc, if_neg hc, LinearMap.neg_apply, Pi.neg_apply, key]; split_ifs <;> simp

theorem signed_column_count_eq (T x : ℤ) (h1 : -T ≤ x) (h2 : x ≤ T) :
    ∑ c ∈ Finset.Icc (-T) T, (if 1 ≤ c then (if c ≤ x then (1 : ℤ) else 0) else (if ¬ c ≤ x then -1 else 0)) = x := by
  have e : ∀ c : ℤ, (if 1 ≤ c then (if c ≤ x then (1 : ℤ) else 0) else (if ¬ c ≤ x then -1 else 0)) =
      (if c ≤ x then 1 else 0) - (if c ≤ 0 then 1 else 0) := by
    intro c; split_ifs <;> omega
  simp only [e]
  rw [Finset.sum_sub_distrib, Finset.sum_boole, Finset.sum_boole]
  have f1 : (Finset.Icc (-T) T).filter (fun c => c ≤ x) = Finset.Icc (-T) x := by
    ext c; simp only [Finset.mem_filter, Finset.mem_Icc]; omega
  have f2 : (Finset.Icc (-T) T).filter (fun c => c ≤ 0) = Finset.Icc (-T) 0 := by
    ext c; simp only [Finset.mem_filter, Finset.mem_Icc]; omega
  rw [f1, f2, Int.card_Icc, Int.card_Icc]
  push_cast
  rw [Int.toNat_of_nonneg (by omega), Int.toNat_of_nonneg (by omega)]
  ring

theorem gl_action_diag_column_product {B : Fin N → ℕ} (Pa : PPath n N LL B) (a : Fin n) (I : ℤ → Finset (Fin n)) (s : Finset ℤ) :
    glAct ℤ LL Set.univ a a (∏ c ∈ s, Kcol ℤ Pa.mu c N (I c)) =
      (∑ c ∈ s, (if 1 ≤ c then (if a ∈ I c then (1 : ℤ) else 0) else (if a ∈ I c then -1 else 0))) •
        ∏ c ∈ s, Kcol ℤ Pa.mu c N (I c) := by
  induction s using Finset.induction_on with
  | empty => simp [gl_action_one]
  | insert c s hc ih =>
    rw [Finset.prod_insert hc, Finset.sum_insert hc, gl_action_mul, ih, gl_action_column_kernel, column_operator_diag, add_smul]
    simp only [mul_smul_comm]
    rw [mul_comm (∏ c ∈ s, Kcol ℤ Pa.mu c N (I c)), add_comm]

theorem weight_of_canonical_Psi_support {B : Fin N → ℕ} (Pa : PPath n N LL B) (R : Type*) [CommRing R]
    (m : Fin N × Fin n →₀ ℕ) (hm : m ∈ (Psi R Pa.mu (Ican Pa.mu)).support) : wtS LL Set.univ m = pEnd Pa.mu := by
  rw [← map_Psi' (Int.castRingHom R)] at hm
  have hm' := MvPolynomial.support_map_subset _ _ hm
  funext a
  refine weight_eq_of_eigen LL Set.univ a _ _ ?_ m hm'
  have h := gl_action_diag_column_product LL Pa a (Ican Pa.mu) (colRange Pa.mu)
  have hd : Dominant (pEnd Pa.mu) := Pa.dom _
  have hs : (∑ c ∈ colRange Pa.mu, (if 1 ≤ c then (if a ∈ Ican Pa.mu c then (1 : ℤ) else 0)
      else (if a ∈ Ican Pa.mu c then -1 else 0))) = pEnd Pa.mu a := by
    have hT := abs_entry_le_total Pa.mu (Fin.last N) a
    rw [abs_le] at hT
    rw [← signed_column_count_eq _ (pEnd Pa.mu a) hT.1 hT.2]
    refine Finset.sum_congr rfl fun c _ => ?_
    by_cases hc : 1 ≤ c
    · rw [if_pos hc, if_pos hc, canonical_column_positive hd hc]; simp
    · rw [if_neg hc, if_neg hc, canonical_column_nonpositive hd hc]; simp
  rw [hs] at h
  exact h

end wt

theorem automorphicSideConclusion_of_pathBasis (D : Formalism.BasicNotions.D7) (h17 : PathBasisOverRing D) : AutomorphicSideConclusion D := by
  intro p _ O _ _ _ _ N n LL B mu
  refine ⟨?_, canonical_Psi_linear_independent D h17 (FF O) LL B mu⟩
  rintro P rfl
  refine ⟨canonical_Psi_ne_zero_of_path_basis D h17 O P, fun m hm => weight_of_canonical_Psi_support LL P O m hm, ?_⟩
  intro a b hab k hk
  rw [← map_Psi' (Int.castRingHom O)]
  exact divided_power_zero_of_gl_action_zero LL Set.univ a b hab.ne _ (gl_action_canonical_Psi_eq_zero LL P a b hab) O k hk

end Formalism.MainNotions.LemmaBAlt
