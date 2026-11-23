import Mathlib

namespace GlobalTheory

theorem isSquare_one_add_of_pow_two_pow_eq_zero {A : Type} [CommRing A] (c : A)
    (hc : 2 * c = 1) : ∀ (m : ℕ) (n : A), n ^ (2 ^ m) = 0 → IsSquare (1 + n) := by
  intro m
  induction m with
  | zero =>
    intro n hn
    simp only [pow_zero, pow_one] at hn
    exact ⟨1, by rw [hn]; ring⟩
  | succ m ih =>
    intro n hn
    have hnil : IsNilpotent (c * n) := ⟨2 ^ (m + 1), by rw [mul_pow, hn, mul_zero]⟩
    obtain ⟨v, hv⟩ := (hnil.isUnit_one_add).exists_right_inv
    have hn' : (-(c ^ 2 * n ^ 2 * v ^ 2)) ^ (2 ^ m) = 0 := by
      have : -(c ^ 2 * n ^ 2 * v ^ 2) = n ^ 2 * (-(c ^ 2 * v ^ 2)) := by ring
      rw [this, mul_pow, ← pow_mul, ← pow_succ', hn, zero_mul]
    obtain ⟨z, hz⟩ := ih _ hn'
    refine ⟨(1 + c * n) * z, ?_⟩
    linear_combination (1 + c * n) ^ 2 * hz + (c ^ 2 * n ^ 2 * ((1 + c * n) * v + 1)) * hv
      + (-n) * hc

theorem isSquare_one_add_of_isNilpotent {A : Type} [CommRing A] (c : A) (hc : 2 * c = 1)
    {n : A} (hn : IsNilpotent n) : IsSquare (1 + n) := by
  obtain ⟨N, hN⟩ := hn
  exact isSquare_one_add_of_pow_two_pow_eq_zero c hc N n
    (pow_eq_zero_of_le (Nat.lt_two_pow_self).le hN)

theorem units_modSq_finite_of_fields : ∀ (k : Type) [Field k] [CharZero k],
    (∀ (L : Type) [Field L] [Algebra k L] [FiniteDimensional k L],
      Finite (Lˣ ⧸ (powMonoidHom 2 : Lˣ →* Lˣ).range)) →
    ∀ (A : Type) [CommRing A] [Algebra k A] [Module.Finite k A],
      Finite (Aˣ ⧸ (powMonoidHom 2 : Aˣ →* Aˣ).range) := by
  intro k _ _ hL A _ _ _
  classical
  haveI : IsArtinianRing A := IsArtinianRing.of_finite k A
  have hc : (2 : A) * algebraMap k A (1 / 2) = 1 := by
    have h2 : (2 : A) * algebraMap k A (1 / 2) = algebraMap k A (2 * (1 / 2)) := by
      rw [map_mul, map_ofNat]
    rw [h2]
    norm_num
  let Q : MaximalSpectrum A → Type := fun I =>
    (A ⧸ I.asIdeal)ˣ ⧸ (powMonoidHom 2 : (A ⧸ I.asIdeal)ˣ →* (A ⧸ I.asIdeal)ˣ).range
  haveI hQ : ∀ I, Finite (Q I) := by
    intro I
    have := I.isMaximal
    letI := Ideal.Quotient.field I.asIdeal
    exact hL (A ⧸ I.asIdeal)
  let φ : Aˣ →* ((I : MaximalSpectrum A) → Q I) := MonoidHom.pi fun I =>
    (QuotientGroup.mk' _).comp (Units.map (Ideal.Quotient.mk I.asIdeal).toMonoidHom)
  have key : ∀ (I : MaximalSpectrum A) (u : Aˣ), φ u I = 1 ↔
      Units.map (Ideal.Quotient.mk I.asIdeal).toMonoidHom u ∈
        (powMonoidHom 2 : (A ⧸ I.asIdeal)ˣ →* (A ⧸ I.asIdeal)ˣ).range :=
    fun I u => QuotientGroup.eq_one_iff _
  have hS : (powMonoidHom 2 : Aˣ →* Aˣ).range ≤ φ.ker := by
    rintro _ ⟨y, rfl⟩
    rw [MonoidHom.mem_ker]
    funext I
    rw [Pi.one_apply, key]
    exact ⟨Units.map (Ideal.Quotient.mk I.asIdeal).toMonoidHom y, by simp⟩
  have hk : ∀ x : Aˣ, φ x = 1 → x ∈ (powMonoidHom 2 : Aˣ →* Aˣ).range := by
    intro x hx
    have hloc : ∀ I : MaximalSpectrum A, ∃ w : (A ⧸ I.asIdeal)ˣ,
        (w : A ⧸ I.asIdeal) ^ 2 = Ideal.Quotient.mk I.asIdeal x := by
      intro I
      have h1 := (key I x).1 (congrFun hx I)
      obtain ⟨w, hw⟩ := h1
      refine ⟨w, ?_⟩
      have := congrArg (fun u : (A ⧸ I.asIdeal)ˣ => (u : A ⧸ I.asIdeal)) hw
      simpa using this
    choose w hw using hloc
    obtain ⟨a, ha⟩ := Ideal.pi_quotient_surjective (I := fun I : MaximalSpectrum A => I.asIdeal)
      (fun I J h => MaximalSpectrum.isCoprime_of_ne h) (fun I => (w I : A ⧸ I.asIdeal))
    have hmem : ∀ I : MaximalSpectrum A, (x : A) - a ^ 2 ∈ I.asIdeal := by
      intro I
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow]
      rw [ha I, hw I, sub_self]
    have hjac : (x : A) - a ^ 2 ∈ (⊥ : Ideal A).jacobson := by
      refine Ideal.mem_sInf.2 ?_
      rintro J ⟨-, hJ⟩
      exact hmem ⟨J, hJ⟩
    have hnil : IsNilpotent ((x : A) - a ^ 2) := by
      obtain ⟨N, hN⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := A)
      refine ⟨N, ?_⟩
      have := Ideal.pow_mem_pow hjac N
      rw [hN] at this
      simpa using this
    set m := (x : A) - a ^ 2 with hm
    have ha2 : IsUnit (a ^ 2) := by
      have : a ^ 2 = (x : A) + (-m) := by rw [hm]; ring
      rw [this]
      exact hnil.neg.isUnit_add_left_of_commute x.isUnit (Commute.all _ _)
    have hau : IsUnit a := (isUnit_pow_iff (by norm_num)).1 ha2
    obtain ⟨b, hb⟩ := hau
    have hn2 : IsNilpotent (((b⁻¹ : Aˣ) : A) ^ 2 * m) :=
      (Commute.all _ _).isNilpotent_mul_left hnil
    obtain ⟨z, hz⟩ := isSquare_one_add_of_isNilpotent _ hc hn2
    have hzu : IsUnit z := by
      have hu : IsUnit (1 + ((b⁻¹ : Aˣ) : A) ^ 2 * m) := hn2.isUnit_one_add
      rw [hz] at hu
      exact isUnit_of_mul_isUnit_left hu
    refine ⟨b * hzu.unit, ?_⟩
    ext
    simp only [powMonoidHom_apply, Units.val_pow_eq_pow_val, Units.val_mul, IsUnit.unit_spec]
    have hbb : (b : A) * ((b⁻¹ : Aˣ) : A) = 1 := by simp
    have hxm : (x : A) = a ^ 2 + m := by rw [hm]; ring
    rw [hxm, ← hb]
    linear_combination (b : A) ^ 2 * hz.symm + (m * ((b : A) * ((b⁻¹ : Aˣ) : A) + 1)) * hbb
  let ψ := QuotientGroup.lift _ φ hS
  have hinj : Function.Injective ψ := by
    intro p q hpq
    induction p using QuotientGroup.induction_on with
    | H x =>
    induction q using QuotientGroup.induction_on with
    | H y =>
    rw [QuotientGroup.eq]
    apply hk
    have h1 : φ x = φ y := hpq
    rw [map_mul, map_inv, h1, inv_mul_cancel]
  exact Finite.of_injective ψ hinj

end GlobalTheory
