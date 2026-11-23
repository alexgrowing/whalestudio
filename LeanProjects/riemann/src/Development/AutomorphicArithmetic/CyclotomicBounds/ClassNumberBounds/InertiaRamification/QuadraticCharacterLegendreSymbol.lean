import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.InertiaRamification.CondDvd
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.InertiaRamification.Average

namespace KStar.Ram

open DirichletCharacter

variable {N : ℕ} [NeZero N]

private lemma quad_gen {d : ℕ} [Fact d.Prime] {g : (ZMod d)ˣ} (hg : ∀ x, x ∈ Subgroup.zpowers g)
    {χ : MulChar (ZMod d) ℂ} (h2 : χ ^ 2 = 1) (h1 : χ ≠ 1) : χ g = -1 := by
  have hs : χ g ^ 2 = 1 := by
    rw [← MulChar.pow_apply_coe, h2, MulChar.one_apply_coe]
  rcases sq_eq_one_iff.mp hs with h | h
  · exact absurd ((MulChar.eq_iff hg χ 1).mpr (by rw [h, MulChar.one_apply_coe])) h1
  · exact h

private noncomputable def quadC (d : ℕ) [Fact d.Prime] : DirichletCharacter ℂ d :=
  (quadraticChar (ZMod d)).ringHomComp (Int.castRingHom ℂ)

private lemma quadC_sq (d : ℕ) [Fact d.Prime] : quadC d ^ 2 = 1 := by
  ext a
  rw [MulChar.pow_apply_coe, quadC, MulChar.ringHomComp_apply, ← map_pow,
    quadraticChar_sq_one a.ne_zero, map_one, MulChar.one_apply_coe]

private lemma quadC_ne (d : ℕ) [Fact d.Prime] (h : d ≠ 2) : quadC d ≠ 1 := by
  rw [quadC, Ne, MulChar.ringHomComp_eq_one_iff (by exact Int.cast_injective)]
  exact quadraticChar_ne_one (by rw [ZMod.ringChar_zmod_n]; exact h)

private lemma quad_unique {d : ℕ} [Fact d.Prime] {χ : DirichletCharacter ℂ d} (h2 : χ ^ 2 = 1)
    (h1 : χ ≠ 1) : χ = quadC d := by
  have hd : d ≠ 2 := by
    rintro rfl
    apply h1
    ext x
    rw [Subsingleton.elim x 1]
    simp
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod d)ˣ)
  refine (MulChar.eq_iff hg _ _).mpr ?_
  rw [quad_gen hg h2 h1, quad_gen hg (quadC_sq d) (quadC_ne d hd)]

private lemma sub_smul_mul_sub_smul_eq_zero_of_quadratic {d c : ℕ} [Fact d.Prime] (hc : c = d) {χ : DirichletCharacter ℂ c}
    (h2 : χ ^ 2 = 1) (h1 : χ ≠ 1) (m : ℕ) : χ (m : ZMod c) = (legendreSym d m : ℂ) := by
  subst hc
  rw [quad_unique h2 h1]
  simp [quadC, legendreSym]

theorem exists_isImagQuad {d : ℕ} (hd : d.Prime) (h4 : d % 4 = 3) (hN : d ∣ N) :
    ∃ ψ : DirichletCharacter ℂ N, IsImagQuad ψ d := by
  haveI : Fact d.Prime := ⟨hd⟩
  have hd2 : d ≠ 2 := by
    rintro rfl
    norm_num at h4
  refine ⟨changeLevel hN (quadC d), ?_, ?_, ?_⟩
  · rw [← map_pow, quadC_sq, map_one]
  · show changeLevel hN (quadC d) (-1) = -1
    have hc := changeLevel_eq_cast_of_dvd' (quadC d) hN (a := -1)
      (by simpa using (isCoprime_one_left (x := (N : ℤ))).neg_left)
    push_cast at hc
    rw [hc, quadC, MulChar.ringHomComp_apply,
      quadraticChar_neg_one (by rw [ZMod.ringChar_zmod_n]; exact hd2), ZMod.card,
      ZMod.χ₄_nat_three_mod_four h4]
    simp
  · rw [conductor_changeLevel]
    rcases hd.eq_one_or_self_of_dvd _ (quadC d).conductor_dvd_level with h1 | h1
    · exact absurd (eq_one_iff_conductor_eq_one.mpr h1) (quadC_ne d hd2)
    · exact h1

theorem IsImagQuad.primitiveCharacter_eq {d : ℕ} [Fact d.Prime] {ψ : DirichletCharacter ℂ N}
    (h : IsImagQuad ψ d) (m : ℕ) :
    ψ.primitiveCharacter (m : ZMod ψ.conductor) = (legendreSym d m : ℂ) := by
  obtain ⟨h2, hodd, hc⟩ := h
  refine sub_smul_mul_sub_smul_eq_zero_of_quadratic hc ?_ ?_ m
  · apply changeLevel_injective ψ.conductor_dvd_level
    rw [map_pow, changeLevel_primitiveCharacter, h2, map_one]
  · intro h1
    have := changeLevel_primitiveCharacter ψ
    rw [h1, map_one] at this
    have h3 : ψ.conductor = 1 := eq_one_iff_conductor_eq_one.mp this.symm
    exact (Fact.out : d.Prime).one_lt.ne' (hc ▸ h3)

theorem IsImagQuad.values {d q₁ : ℕ} (hd : d.Prime) (hq : q₁.Prime) (hd8 : d % 8 = 7)
    (hq8 : q₁ % 8 = 3) {ch ps : DirichletCharacter ℂ N} (hch : IsImagQuad ch d)
    (hps : IsImagQuad ps q₁) :
    SplitsFor 2 ch ∧ ps.primitiveCharacter ((2 : ℕ) : ZMod ps.conductor) = -1 ∧
      (SplitsFor q₁ ch → ps.primitiveCharacter (d : ZMod ps.conductor) = -1) := by
  have : Fact d.Prime := ⟨hd⟩
  have : Fact q₁.Prime := ⟨hq⟩
  refine ⟨?_, ?_, ?_⟩
  · unfold SplitsFor
    rw [hch.primitiveCharacter_eq]
    have : legendreSym d ((2 : ℕ) : ℤ) = 1 := by
      rw [Nat.cast_ofNat, legendreSym.at_two (by omega), ZMod.χ₈_nat_eq_if_mod_eight,
        if_neg (by omega), if_pos (by omega)]
    rw [this]; simp
  · rw [hps.primitiveCharacter_eq]
    have : legendreSym q₁ ((2 : ℕ) : ℤ) = -1 := by
      rw [Nat.cast_ofNat, legendreSym.at_two (by omega), ZMod.χ₈_nat_eq_if_mod_eight,
        if_neg (by omega), if_neg (by omega)]
    rw [this]; simp
  · unfold SplitsFor
    rw [hch.primitiveCharacter_eq, hps.primitiveCharacter_eq]
    intro h
    rw [legendreSym.quadratic_reciprocity_three_mod_four (p := d) (q := q₁) (by omega) (by omega)]
    push_cast
    rw [h]

end KStar.Ram
