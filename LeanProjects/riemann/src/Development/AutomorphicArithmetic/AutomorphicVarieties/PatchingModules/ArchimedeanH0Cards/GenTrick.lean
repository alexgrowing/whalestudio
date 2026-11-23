import Mathlib

open IsLocalRing

private theorem card_coker_eq_card_ker {A M : Type} [CommRing A] [AddCommGroup M] [Module A M]
    [Finite M] (f : M →ₗ[A] M) :
    Nat.card (M ⧸ LinearMap.range f) = Nat.card (LinearMap.ker f) := by
  have h1 := Submodule.card_eq_card_quotient_mul_card (LinearMap.range f)
  have h2 := Submodule.card_eq_card_quotient_mul_card (LinearMap.ker f)
  have h3 : Nat.card (M ⧸ LinearMap.ker f) = Nat.card (LinearMap.range f) :=
    Nat.card_congr f.quotKerEquivRange.toEquiv
  rw [h3] at h2
  have hpos : 0 < Nat.card (LinearMap.range f) := Nat.card_pos
  rw [h2, mul_comm] at h1
  exact (Nat.eq_of_mul_eq_mul_left hpos h1).symm

private theorem UpperTheory.V.Pa.B2.card_quot_span_pow_irreducible_eq_pow {A : Type} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] (t : A) (ht : Irreducible t) (e : ℕ) :
    Nat.card (A ⧸ Ideal.span {t ^ e}) = Nat.card (ResidueField A) ^ e := by
  have hmax := ht.maximalIdeal_eq
  have ht0 : t ≠ 0 := ht.ne_zero
  let J : ℕ → AddSubgroup A := fun k => (Ideal.span {t ^ k}).toAddSubgroup
  have hJ : ∀ k, Nat.card (A ⧸ Ideal.span {t ^ k}) = (J k).index := fun k => rfl
  have h1 : (J 1).index = Nat.card (ResidueField A) := by
    rw [← hJ, pow_one, ← hmax]
    rfl
  rw [hJ]
  induction e with
  | zero =>
    simp [J, Ideal.span_singleton_one, AddSubgroup.index_top]
  | succ e ih =>
    have hle : J (e + 1) ≤ J e := by
      intro x hx
      simp only [J, Submodule.mem_toAddSubgroup, Ideal.mem_span_singleton] at hx ⊢
      exact (pow_dvd_pow t (Nat.le_succ e)).trans hx
    have hrel : (J (e + 1)).relIndex (J e) = Nat.card (ResidueField A) := by
      let f : A →+ A := AddMonoidHom.mulLeft (t ^ e)
      have hrange : f.range = J e := by
        ext x
        simp only [f, AddMonoidHom.mem_range, AddMonoidHom.coe_mulLeft, J,
          Submodule.mem_toAddSubgroup, Ideal.mem_span_singleton]
        constructor
        · rintro ⟨a, rfl⟩
          exact dvd_mul_right _ _
        · rintro ⟨a, rfl⟩
          exact ⟨a, rfl⟩
      have hcomap : (J (e + 1)).comap f = J 1 := by
        ext x
        simp only [f, AddSubgroup.mem_comap, AddMonoidHom.coe_mulLeft, J,
          Submodule.mem_toAddSubgroup, Ideal.mem_span_singleton, pow_one]
        rw [pow_succ, mul_dvd_mul_iff_left (pow_ne_zero e ht0)]
      rw [← h1, ← hcomap, AddSubgroup.index_comap, hrange]
    rw [← AddSubgroup.relIndex_mul_index hle, ih, hrel, pow_succ, mul_comm]

theorem UpperTheory.V.Pa.B2.genTrick :
    ∀ (A H : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Finite (ResidueField A)] [AddCommGroup H] [Module A H] [Finite H] (t : A) (g C m : ℕ), Irreducible t → (∀ y : H, t ^ m • y = 0) → (∀ e ≤ m, Nat.card (H ⧸ LinearMap.range (LinearMap.lsmul A H (t ^ e))) ≤ Nat.card (ResidueField A) ^ (g * e + C)) → ∀ ξ : Fin (g + 1) → H, ∃ c : Fin (g + 1) → A, (∃ i, IsUnit (c i)) ∧ t ^ C • ∑ i, c i • ξ i = 0 := by
  intro A H _ _ _ _ _ _ _ t g C m ht hm hcard ξ
  classical
  by_cases hCm : m ≤ C
  · refine ⟨fun _ => 1, ⟨0, isUnit_one⟩, ?_⟩
    have hp : t ^ C = t ^ (C - m) * t ^ m := by
      rw [← pow_add]
      congr 1
      omega
    rw [hp, mul_smul, hm, smul_zero]
  by_contra hne
  push_neg at hne
  set e := C + 1 with he
  have hem : e ≤ m := by omega
  let φ : (Fin (g + 1) → A) →ₗ[A] H := Fintype.linearCombination A ξ
  have hφ : ∀ c, φ c = ∑ i, c i • ξ i := fun c => Fintype.linearCombination_apply A ξ c
  have hmax := ht.maximalIdeal_eq
  have key : ∀ k ≤ e, ∀ d d0 : Fin (g + 1) → A, φ d = t ^ e • φ d0 → ∀ i, t ^ k ∣ d i := by
    intro k
    induction k with
    | zero =>
      intro _ d d0 _ i
      simp
    | succ k ih =>
      intro hk d d0 hd
      choose d' hd' using ih (by omega) d d0 hd
      by_cases hall : ∀ i, t ∣ d' i
      · intro i
        obtain ⟨w, hw⟩ := hall i
        exact ⟨w, by rw [hd' i, hw, pow_succ, mul_assoc]⟩
      · push_neg at hall
        obtain ⟨i0, hi0⟩ := hall
        exfalso
        have hdd : d = t ^ k • d' := funext fun i => by simp [hd' i]
        rw [hdd, map_smul] at hd
        have e1 : t ^ k • φ (d' - t ^ (e - k) • d0) = 0 := by
          rw [map_sub, map_smul, smul_sub, hd, smul_smul, ← pow_add,
            Nat.add_sub_cancel' (by omega : k ≤ e), sub_self]
        apply hne (d' - t ^ (e - k) • d0) ⟨i0, ?_⟩
        · rw [← hφ]
          have hp : t ^ C = t ^ (C - k) * t ^ k := by
            rw [← pow_add]
            congr 1
            omega
          rw [hp, mul_smul, e1, smul_zero]
        · rw [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, ← notMem_maximalIdeal, hmax,
            Ideal.mem_span_singleton]
          intro hdiv
          apply hi0
          have h2 : t ∣ t ^ (e - k) * d0 i0 :=
            Dvd.dvd.mul_right (dvd_pow_self t (by omega : e - k ≠ 0)) _
          simpa using dvd_add hdiv h2
  let N := LinearMap.range φ
  let Q := N ⧸ LinearMap.range (LinearMap.lsmul A N (t ^ e))
  haveI : Finite Q := Finite.of_surjective _ (Submodule.mkQ_surjective _)
  have hsurj : Function.Surjective (Ideal.Quotient.mk (Ideal.span {t ^ e})) :=
    Ideal.Quotient.mk_surjective
  let sec := Function.surjInv hsurj
  let γ : (Fin (g + 1) → A ⧸ Ideal.span {t ^ e}) → Q := fun x =>
    Submodule.Quotient.mk ⟨φ (fun i => sec (x i)), LinearMap.mem_range_self φ _⟩
  have hinj : Function.Injective γ := by
    intro x y hxy
    have h1 := (Submodule.Quotient.eq _).mp hxy
    obtain ⟨n, hn⟩ := LinearMap.mem_range.mp h1
    obtain ⟨d0, hd0⟩ := LinearMap.mem_range.mp n.2
    have hd : φ ((fun i => sec (x i)) - (fun i => sec (y i))) = t ^ e • φ d0 := by
      rw [hd0, map_sub]
      have := congrArg Subtype.val hn
      simpa using this.symm
    funext i
    have hdv := key e le_rfl _ d0 hd i
    rw [← Function.surjInv_eq hsurj (x i), ← Function.surjInv_eq hsurj (y i)]
    exact Ideal.Quotient.eq.mpr (Ideal.mem_span_singleton.mpr (by simpa using hdv))
  have hQ : Nat.card (Fin (g + 1) → A ⧸ Ideal.span {t ^ e}) ≤ Nat.card Q :=
    Nat.card_le_card_of_injective γ hinj
  rw [Nat.card_fun, Nat.card_fin, UpperTheory.V.Pa.B2.card_quot_span_pow_irreducible_eq_pow t ht e] at hQ
  have hQN : Nat.card Q = Nat.card (LinearMap.ker (LinearMap.lsmul A N (t ^ e))) :=
    card_coker_eq_card_ker _
  have hker : Nat.card (LinearMap.ker (LinearMap.lsmul A N (t ^ e))) ≤
      Nat.card (LinearMap.ker (LinearMap.lsmul A H (t ^ e))) := by
    refine Nat.card_le_card_of_injective
      (fun x => ⟨x.1.1, by
        have := x.2
        simp only [LinearMap.mem_ker, LinearMap.lsmul_apply] at this ⊢
        exact congrArg Subtype.val this⟩) ?_
    intro x y hxy
    have hv := congrArg Subtype.val hxy
    apply Subtype.ext
    apply Subtype.ext
    simpa using hv
  have hH : Nat.card (LinearMap.ker (LinearMap.lsmul A H (t ^ e))) =
      Nat.card (H ⧸ LinearMap.range (LinearMap.lsmul A H (t ^ e))) :=
    (card_coker_eq_card_ker _).symm
  have hb := hcard e hem
  have hq : 1 < Nat.card (ResidueField A) := Finite.one_lt_card
  have hlt : Nat.card (ResidueField A) ^ (g * e + C) < (Nat.card (ResidueField A) ^ e) ^ (g + 1) := by
    rw [← pow_mul]
    exact Nat.pow_lt_pow_right hq (by rw [he]; ring_nf; omega)
  omega
