import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Integral
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Imports
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.EntryMod
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.AlgClosed
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoQuot

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr UpperTheory.V.Fr.PF

section Sub

variable {O R : Type} [CommRing O] [IsLocalRing O] [CommRing R] [Algebra O R] [IsCO O R] (A : Subalgebra O R)
  [IsCO O A]

private theorem mem_max (a : A) : (a : R) ∈ maximalIdeal R ↔ a ∈ maximalIdeal A := by
  rw [← res_eq_zero_iff O, ← res_eq_zero_iff O, ← res_map A.val]
  rfl

private theorem closed {x : R} (hx : ∀ N : ℕ, ∃ y ∈ A, x - y ∈ maximalIdeal R ^ N) : x ∈ A := by
  choose c hc hx using hx
  have hsep : ⨅ N : ℕ, maximalIdeal R ^ N = ⊥ :=
    Ideal.iInf_pow_eq_bot_of_isLocalRing _ (maximalIdeal.isMaximal R).ne_top
  obtain ⟨y, hy⟩ := alg_closed A (maximalIdeal R)
    ⟨inferInstance, Subtype.val_injective, hsep, Ideal.ext (mem_max A), fun d => by
      obtain ⟨a, ha⟩ := IsCO.res_surj (O := O) d
      exact ⟨algebraMap O A a, ha⟩⟩ (fun N => ⟨c (N + 1), hc _⟩) (fun N => by
      have h := sub_mem (hx (N + 1)) (Ideal.pow_le_pow_right (Nat.le_succ _) (hx (N + 1 + 1)))
      rw [sub_sub_sub_cancel_left] at h
      exact h)
  have h : x - y ∈ ⨅ N : ℕ, maximalIdeal R ^ N := Ideal.mem_iInf.2 fun N => by
    have h := sub_mem (hx (N + 1)) (show (y : R) - c (N + 1) ∈ _ from hy N)
    rw [sub_sub_sub_cancel_right] at h
    exact Ideal.pow_le_pow_right (Nat.le_succ _) h
  rw [hsep, Ideal.mem_bot, sub_eq_zero] at h
  exact h ▸ y.2

private theorem sqrt_mem (h2 : IsUnit (2 : A)) {ζ : R} (hζ : IsUnit ζ) (h : 2 * ζ ^ 2 ∈ A) : ζ ∈ A := by
  obtain ⟨u, hu⟩ := h2.exists_left_inv
  have hu' : (u : R) * 2 = 1 := congrArg A.val hu
  have h1 : ζ ^ 2 ∈ A := by
    have := mul_mem u.2 h
    rwa [← mul_assoc, hu', one_mul] at this
  obtain ⟨a, ha⟩ := IsCO.res_surj (O := O) ζ
  have ha' : IsUnit (algebraMap O A a) := by
    by_contra hn
    have := add_mem ha ((mem_max A _).2 hn)
    exact this (by simpa using hζ)
  obtain ⟨d, hd, hd'⟩ := HenselianRing.is_henselian (I := maximalIdeal A)
    (Polynomial.X ^ 2 - Polynomial.C (⟨ζ ^ 2, h1⟩ : A)) (Polynomial.monic_X_pow_sub_C _ two_ne_zero)
    (algebraMap O A a) (by
      rw [← mem_max]
      have : (((Polynomial.X ^ 2 - Polynomial.C (⟨ζ ^ 2, h1⟩ : A)).eval (algebraMap O A a) : A) : R) =
          -(ζ + algebraMap O R a) * (ζ - algebraMap O R a) := by
        simp; ring
      rw [this]
      exact Ideal.mul_mem_left _ _ ha) (by
      refine IsUnit.map _ ?_
      simpa [one_add_one_eq_two] using h2.mul ha')
  have e1 : ((d : R) + ζ) * (d - ζ) = 0 := by
    have := congrArg A.val hd
    simp at this
    linear_combination this
  have e2 : IsUnit ((d : R) + ζ) := by
    by_contra hn
    have h3 : (d : R) - algebraMap O R a ∈ maximalIdeal R := (mem_max A _).2 hd'
    have h4 := add_mem (sub_mem (show (d : R) + ζ ∈ maximalIdeal R from hn) h3) ha
    have h5 : (d : R) + ζ - (d - algebraMap O R a) + (ζ - algebraMap O R a) = 2 * ζ := by ring
    rw [h5] at h4
    exact h4 ((IsUnit.of_mul_eq_one_right _ hu').mul hζ)
  exact sub_eq_zero.1 (e2.mul_right_eq_zero.1 e1) ▸ d.2

end Sub

private theorem w_facts {n : ℕ} (hn : n = 2 ∨ n = 3) :
    (∀ i, w n i = 1 ∨ w n i = 0 ∨ w n i = -1) ∧ (∀ i j, w n i = w n j → i = j) ∧ (∀ i, w n i.rev = - w n i) ∧
    (∀ i j k m, 0 < w n i - w n j → w n k - w n m < 0 → j = k ∨ m = i ∨ i.rev = k ∨ m = j.rev) ∧
    (∑ i, w n i ^ 2 = 2) ∧ (∃ i, w n i = 1) := by
  rcases hn with rfl | rfl <;> decide

private theorem units_mem {G C K : Type} [Monoid G] [CommRing C] [CommRing K] [Algebra C K] {n : ℕ}
    (hn : n = 2 ∨ n = 3) (r : G →* Matrix (Fin n) (Fin n) K) (h2 : IsUnit (2 : C))
    (hy : (diagonal fun i => (w n i : K)) ∈ Submodule.span C (Set.range r)) (i : Fin n) :
    Matrix.single i i (1 : K) ∈ Submodule.span C (Set.range r) := by
  obtain ⟨w1, w2, -⟩ := w_facts hn
  obtain ⟨u, hu⟩ := h2.exists_left_inv
  have hu' : algebraMap C K u * 2 = 1 := by
    have := congrArg (algebraMap C K) hu
    rwa [map_mul, map_ofNat, map_one] at this
  have hyy := span_mul r hy hy
  have h1 : (1 : Matrix (Fin n) (Fin n) K) ∈ Submodule.span C (Set.range r) := Submodule.subset_span ⟨1, map_one r⟩
  have key : ∀ f : Fin n → K, f i = 1 → (∀ j, w n j ≠ w n i → f j = 0) → diagonal f = Matrix.single i i (1 : K) := by
    intro f e1 e2
    rw [← Matrix.diagonal_single]
    congr 1
    funext j
    by_cases h : j = i
    · rw [h, e1, Pi.single_eq_same]
    · rw [e2 j fun e => h (w2 _ _ e), Pi.single_eq_of_ne h]
  rw [diagonal_mul_diagonal] at hyy
  rcases w1 i with h | h | h
  · have := Submodule.smul_mem _ u (add_mem hyy hy)
    rw [diagonal_add, ← diagonal_smul] at this
    refine key _ ?_ (fun j hj => ?_) ▸ this
    · simp [h, Algebra.smul_def, one_add_one_eq_two, hu']
    · rw [h] at hj
      rcases w1 j with e | e | e <;> simp [e] at hj ⊢
  · have := sub_mem h1 hyy
    rw [← diagonal_one, diagonal_sub] at this
    refine key _ ?_ (fun j hj => ?_) ▸ this
    · simp [h]
    · rw [h] at hj
      rcases w1 j with e | e | e <;> simp [e] at hj ⊢
  · have := Submodule.smul_mem _ u (sub_mem hyy hy)
    rw [diagonal_sub, ← diagonal_smul] at this
    refine key _ ?_ (fun j hj => ?_) ▸ this
    · simp [h, Algebra.smul_def, one_add_one_eq_two, hu']
    · rw [h] at hj
      rcases w1 j with e | e | e <;> simp [e] at hj ⊢

private theorem trace_mem {G C K : Type} [Monoid G] [CommRing C] [CommRing K] [Algebra C K] {n : ℕ}
    (r : G →* Matrix (Fin n) (Fin n) K) (ht : ∀ g, ∃ c, algebraMap C K c = (r g).trace)
    {m : Matrix (Fin n) (Fin n) K} (hm : m ∈ Submodule.span C (Set.range r)) : ∃ c, algebraMap C K c = m.trace := by
  induction hm using Submodule.span_induction with
  | mem x hx => obtain ⟨g, rfl⟩ := hx; exact ht g
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨c, h1⟩ := hx
    obtain ⟨d, h2⟩ := hy
    exact ⟨c + d, by rw [map_add, h1, h2, trace_add]⟩
  | smul a x _ hx =>
    obtain ⟨c, h1⟩ := hx
    exact ⟨a * c, by rw [map_mul, h1, trace_smul, Algebra.smul_def]⟩

section Mon

variable {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] {F : Frame l k} {C₀ : ℕ} {n : ℕ}

private theorem mon_mem (hF : F.Ok C₀) (hn : n = 2 ∨ n = 3) {C K : Type} [CommRing C] [CommRing K] [Algebra C K]
    (ρ : NRep F n K) (ht : ∀ g, ∃ c, algebraMap C K c = (ρ.r g).trace)
    (hE : ∀ i, Matrix.single i i (1 : K) ∈ Submodule.span C (Set.range ρ.r)) {x : K} (hx : x ∈ ρ.mon 0) :
    ∃ c, algebraMap C K c = x := by
  obtain ⟨-, -, -, -, hs⟩ := UpperTheory.V.Fr.star hF
  obtain ⟨-, w2, w3, w4, -⟩ := w_facts hn
  obtain ⟨L, hL, rfl⟩ := hx
  let E : Fin n → Fin n → Submodule C K := fun i j => Submodule.span C (Set.range fun g => ρ.r g i j)
  have hmem : ∀ g i j, ρ.r g i j ∈ E i j := fun g i j => Submodule.subset_span ⟨g, rfl⟩
  have hrev : ∀ i j, ∀ x ∈ E i j, x ∈ E j.rev i.rev := fun i j => by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨g, rfl⟩
    have h := hmem (F.star g) j.rev i.rev
    rwa [hs, Fin.rev_rev, Fin.rev_rev] at h
  have hdiag : ∀ i, ∀ x ∈ E i i, ∃ c, algebraMap C K c = x := fun i x hx => by
    simpa using trace_mem ρ.r ht (single_mem hE hx)
  let N : ℤ → Set K := fun a => {x | ∃ i j, w n i - w n j = a ∧ x ∈ E i j}
  have step : ∀ i j k, ∀ x ∈ E i j, ∀ y ∈ E j k, ∀ s, s = w n i - w n k →
      x * y ∈ N s ∧ (s = 0 → ∃ c ∈ (⊤ : Ideal C), algebraMap C K c = x * y) := by
    intro i j k x hx y hy s hs'
    refine ⟨⟨i, k, hs'.symm, ent_mul hE hx hy⟩, fun h => ?_⟩
    obtain rfl : i = k := w2 i k (by omega)
    obtain ⟨c, hc⟩ := hdiag i _ (ent_mul hE hx hy)
    exact ⟨c, trivial, hc⟩
  obtain ⟨c, h1, -⟩ := cycles (⊤ : Ideal C) N
    (by
      rintro x ⟨i, j, h, hx⟩
      obtain rfl : i = j := w2 i j (by omega)
      exact hdiag i x hx)
    (by
      rintro _ _ ha hb x ⟨i, j, rfl, hx⟩ y ⟨k, m, rfl, hy⟩
      have e1 := w3 i
      have e2 := w3 j
      rcases w4 i j k m ha hb with rfl | rfl | rfl | rfl
      · exact step _ _ _ x hx y hy _ (by omega)
      · rw [mul_comm]
        exact step _ _ _ y hy x hx _ (by omega)
      · exact step _ _ _ x (hrev _ _ x hx) y hy _ (by omega)
      · rw [mul_comm]
        exact step _ _ _ y hy x (hrev _ _ x hx) _ (by omega))
    ((L : Multiset (F.G0 × Fin n × Fin n)).map fun s => (w n s.2.1 - w n s.2.2, ρ.r s.1 s.2.1 s.2.2))
    (fun p hp => by
      obtain ⟨s, -, rfl⟩ := Multiset.mem_map.1 hp
      exact ⟨_, _, rfl, hmem _ _ _⟩)
    (by rw [Multiset.map_map, Multiset.map_coe, Multiset.sum_coe]; exact hL)
  refine ⟨c, ?_⟩
  rw [h1, Multiset.map_map, Multiset.map_coe, Multiset.prod_coe]
  rfl

private theorem z_diag (hF : F.Ok C₀) (hn : n = 2 ∨ n = 3) {K : Type} [CommRing K] (ρ : NRep F n K) {i₀ : Fin n}
    (h0 : w n i₀ = 1) : ρ.r F.g0 - ρ.r (F.star F.g0) =
      (ρ.r F.g0 - ρ.r (F.star F.g0)) i₀ i₀ • diagonal fun i => (w n i : K) := by
  obtain ⟨-, -, -, -, hs⟩ := UpperTheory.V.Fr.star hF
  obtain ⟨w1, w2, w3, -⟩ := w_facts hn
  ext i j
  rw [Matrix.smul_apply]
  by_cases h : i = j
  · subst h
    rw [diagonal_apply_eq, Matrix.sub_apply, Matrix.sub_apply, hs, hs]
    have e := w3 i
    rcases w1 i with h | h | h
    · rw [w2 i i₀ (by omega), h0]; simp
    · rw [w2 i.rev i (by omega), h]; simp
    · rw [← w2 i.rev i₀ (by omega), h]; simp
  · rw [ρ.diag i j h, diagonal_apply_ne _ h, smul_zero]

end Mon

theorem UpperTheory.V.Fr.B_gen :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ : ℕ} {n : ℕ}, F.Ok C₀ → (n = 2 ∨ n = 3) → ∀ S : Space O F n, ∀ (C : Type) [CommRing C] [Algebra O C] [IsCO O C] (φ : C →ₐ[O] S.R), (∀ g, (S.ρ.r g).trace ∈ φ.range) → (∀ v i g, (S.ρ.ψ v i g : S.R) ∈ φ.range) → S.B ≤ φ.range := by
  intro l _ O _ _ _ _ F C₀ n hF hn S C _ _ _ φ ht hψ
  haveI : IsCO O φ.range := co_quot O C φ.range φ.rangeRestrict φ.rangeRestrict_surjective
  generalize φ.range = A at *
  obtain ⟨-, -, hΨ, -, -⟩ := UpperTheory.V.Fr.star hF
  obtain ⟨-, -, -, -, w5, i₀, h0⟩ := w_facts hn
  have ht' : ∀ g, ∃ c, algebraMap A S.R c = (S.ρ.r g).trace := fun g => ⟨⟨_, ht g⟩, rfl⟩
  have h2 : IsUnit (2 : A) := by
    by_contra h
    have h3 := (res_eq_zero_iff O A _).2 h
    rw [map_ofNat] at h3
    exact hF.l_odd ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).1
      ((CharP.cast_eq_zero_iff (ResidueField O) l 2).1 h3))
  have hz := z_diag hF hn S.ρ h0
  have hzm : S.ρ.r F.g0 - S.ρ.r (F.star F.g0) ∈ Submodule.span A (Set.range S.ρ.r) :=
    sub_mem (Submodule.subset_span ⟨_, rfl⟩) (Submodule.subset_span ⟨_, rfl⟩)
  have hζ : IsUnit ((S.ρ.r F.g0 - S.ρ.r (F.star F.g0)) i₀ i₀) := by
    by_contra h
    have h3 := (res_eq_zero_iff O S.R _).2 h
    have h4 : ∀ g, res O S.R (S.ρ.r g i₀ i₀) = (F.Ψ g : ResidueField O) := fun g => by
      simpa [h0] using S.lift.2.1.1 g i₀
    rw [Matrix.sub_apply, map_sub, h4, h4, hΨ, sub_eq_zero] at h3
    refine hF.baseSubgroup_spec ?_
    rw [sq, mul_eq_one_iff_eq_inv]
    exact Units.ext h3
  generalize (S.ρ.r F.g0 - S.ρ.r (F.star F.g0)) i₀ i₀ = ζ at hz hζ
  rw [hz] at hzm
  have hζA : ζ ∈ A := by
    refine sqrt_mem A h2 hζ ?_
    obtain ⟨c, hc⟩ := trace_mem _ ht' (span_mul _ hzm hzm)
    have h3 : ∑ i, (w n i : S.R) * w n i = 2 := by
      have := congrArg (Int.cast : ℤ → S.R) w5
      simpa [sq] using this
    rw [smul_mul_smul_comm, diagonal_mul_diagonal, trace_smul, trace_diagonal, h3, smul_eq_mul, mul_comm, ← sq] at hc
    exact hc ▸ c.2
  have hu : IsUnit (⟨ζ, hζA⟩ : A) := by
    by_contra h
    exact (mem_max A _).2 h hζ
  obtain ⟨u, hu⟩ := hu.exists_left_inv
  have hE := units_mem hn S.ρ.r h2 (by
    have := Submodule.smul_mem _ u hzm
    rwa [Subalgebra.smul_def, smul_smul, show (u : S.R) * ζ = 1 from congrArg A.val hu, one_smul] at this)
  have hadj : Algebra.adjoin O (S.ρ.mon 0 ∪ {x | ∃ v i g, x = (S.ρ.ψ v i g : S.R)}) ≤ A := by
    refine Algebra.adjoin_le ?_
    rintro x (hx | ⟨v, i, g, rfl⟩)
    · obtain ⟨c, rfl⟩ := mon_mem hF hn S.ρ ht' hE hx
      exact c.2
    · exact hψ v i g
  intro x hx
  refine closed A fun N => ?_
  obtain ⟨y, hy, h⟩ := hx N
  exact ⟨y, hadj hy, h⟩
