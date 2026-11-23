import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.InertiaGenAlt

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.V.Published
open UpperTheory.Gal.UnramifiedFromSplittingCriterion

private theorem chi_of_pow {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] {p : ℕ} [Fact p.Prime] {ζ : Ω}
    (hζ : IsPrimitiveRoot ζ p) (g : G F Ω) (k : ℕ) (h : g ζ = ζ ^ k) :
    ((hζ.autToPow F g : (ZMod p)ˣ) : ZMod p) = (k : ZMod p) := by
  have h1 := hζ.autToPow_spec F g
  have hfin : IsOfFinOrder ζ :=
    isOfFinOrder_iff_pow_eq_one.2 ⟨p, (Fact.out : p.Prime).pos, hζ.pow_eq_one⟩
  rw [h, hfin.pow_eq_pow_iff_modEq, ← hζ.eq_orderOf] at h1
  rw [← ZMod.natCast_zmod_val ((hζ.autToPow F g : (ZMod p)ˣ) : ZMod p)]
  exact (ZMod.natCast_eq_natCast_iff _ _ _).2 h1

private theorem chi_one {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] {p : ℕ} [Fact p.Prime] {ζ : Ω}
    (hζ : IsPrimitiveRoot ζ p) (g : G F Ω) (h : g ζ = ζ) : hζ.autToPow F g = 1 := by
  apply Units.ext
  rw [chi_of_pow hζ g 1 (by rw [h, pow_one])]
  simp

private theorem exists_prim {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    (p : ℕ) [Fact p.Prime] : ∃ ζ : Ω, IsPrimitiveRoot ζ p := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  haveI : NeZero (p : Ω) := ⟨by exact_mod_cast (Fact.out : p.Prime).ne_zero⟩
  exact HasEnoughRootsOfUnity.exists_primitiveRoot Ω p

private theorem chi_conj {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] {p : ℕ} [Fact p.Prime] {ζ : Ω}
    (hζ : IsPrimitiveRoot ζ p) (j : Ω →+* ℂ) (c : G F Ω) (hc : ∀ x, j (c x) = starRingEnd ℂ (j x)) :
    hζ.autToPow F c = -1 := by
  have hp := (Fact.out : p.Prime)
  have hw : (j ζ) ^ p = 1 := by rw [← map_pow, hζ.pow_eq_one, map_one]
  have hn : ‖j ζ‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hw hp.ne_zero
  have hcz : c ζ = ζ ^ (p - 1) := by
    apply j.injective
    rw [hc, ← Complex.inv_eq_conj hn, map_pow]
    symm
    apply eq_inv_of_mul_eq_one_left
    rw [← pow_succ, Nat.sub_add_cancel hp.one_lt.le, hw]
  apply Units.ext
  rw [chi_of_pow hζ c (p - 1) hcz, Nat.cast_sub hp.one_lt.le, ZMod.natCast_self]
  simp

private theorem good_ker {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {p : ℕ}
    [Fact p.Prime] {ζ : Ω} (hζ : IsPrimitiveRoot ζ p) (lam : (ZMod p)ˣ →* ℂˣ) (h1 : lam (-1) = 1) :
    Good (lam.comp (hζ.autToPow F)).ker := by
  haveI : Algebra.IsIntegral F Ω := (IsAlgClosure.isAlgebraic (R := F) (K := Ω)).isIntegral
  refine ⟨?_, Abelianization.commutator_subset_ker _, ?_⟩
  · refine Subgroup.isOpen_mono (H₁ := MulAction.stabilizer (G F Ω) ζ) ?_
      (stabilizer_isOpen_of_isIntegral (K := F) ζ)
    intro g hg
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, chi_one hζ g hg, map_one]
  · intro j c hc
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, chi_conj hζ j c hc, h1]

private theorem lam_pow {p n : ℕ} [Fact p.Prime] (lam : (ZMod p)ˣ →* ℂˣ) (hn : lam ^ n = 1) (a : (ZMod p)ˣ) :
    lam a ^ n = 1 := by
  rw [← MonoidHom.pow_apply, hn, MonoidHom.one_apply]

theorem UpperTheory.Gal.UnramifiedFromSplittingCriterion.freshChar :
    PowChar → InertiaGen → DecPow → FreshPrime → FreshChar := by
  intro hPow hIG hDP hFP F Ω _ _ _ _ _ U hU T hT n hn
  obtain ⟨u, huT, hpr, hpu, hpu2, hdec, hdvd, hTt⟩ := hFP F Ω U hU T hT n hn
  haveI : Fact (Nat.Prime (normV u)) := ⟨hpr⟩
  obtain ⟨lam, hlamn, hlam1, hlamord⟩ := hPow (normV u) n hn hdvd
  obtain ⟨ζ, hζ⟩ := exists_prim (F := F) (Ω := Ω) (normV u)
  refine ⟨lam.comp (hζ.autToPow F), good_ker hζ lam hlam1, ?_, ?_, u, huT, hpr, ?_, ?_⟩
  · refine MonoidHom.ext fun g => ?_
    rw [MonoidHom.pow_apply, MonoidHom.comp_apply, lam_pow lam hlamn, MonoidHom.one_apply]
  · intro t ht A hA g hg
    obtain ⟨hpt, b, hb⟩ := hTt t ht
    obtain ⟨hD, -⟩ := hDP F Ω A t hA (normV u) hpr hpt ζ hζ
    obtain ⟨k, hk⟩ := hD g hg
    have hχ := chi_of_pow hζ g _ hk
    push_cast at hχ
    rw [← hb] at hχ
    rw [MonoidHom.comp_apply]
    by_cases hb0 : b = 0
    · rcases Nat.eq_zero_or_pos k with rfl | hk0
      · simp only [pow_zero] at hχ
        rw [show hζ.autToPow F g = 1 from Units.ext (by simpa using hχ), map_one]
      · exfalso
        rw [hb0, zero_pow hn.ne', zero_pow hk0.ne'] at hχ
        exact (Units.ne_zero _) hχ
    · have hunit : hζ.autToPow F g = (Units.mk0 b hb0) ^ (n * k) :=
        Units.ext (by rw [hχ]; simp [pow_mul])
      rw [hunit, map_pow, pow_mul, lam_pow lam hlamn, one_pow]
  · intro A hA
    refine ⟨hdec A hA, ?_⟩
    obtain ⟨τ, hτ, a, ha, hτz⟩ := hIG F Ω A u hA (normV u) hpu hpu2 ζ hζ
    refine ⟨τ, hτ, ?_⟩
    have hχ := chi_of_pow hζ τ _ hτz
    rw [ZMod.natCast_zmod_val] at hχ
    rw [MonoidHom.comp_apply, show hζ.autToPow F τ = a from Units.ext hχ]
    exact hlamord a ha
  · intro t A hA hpt τ hτ
    obtain ⟨-, hI⟩ := hDP F Ω A t hA (normV u) hpr hpt ζ hζ
    rw [MonoidHom.comp_apply, chi_one hζ τ (hI τ hτ), map_one]
