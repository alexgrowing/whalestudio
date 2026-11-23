import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCptGen

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.CptModel

open AlgebraicGeometry CategoryTheory

section General

variable {X : Scheme.{0}} {Ω : Type} [Field Ω]

def self (ξ : Spec (CommRingCat.of Ω) ⟶ X) : Cpt ξ := ⟨genPt ξ, specializes_refl _⟩

theorem genMap_self (ξ : Spec (CommRingCat.of Ω) ⟶ X) :
    genMap ξ (self ξ) = (Scheme.stalkClosedPointTo ξ).hom := by
  have h : X.presheaf.stalkSpecializes (self ξ).2 = 𝟙 _ := X.presheaf.stalkSpecializes_refl _
  unfold genMap
  rw [h]
  rfl

theorem unitAt_iff (ξ : Spec (CommRingCat.of Ω) ⟶ X) (p : Cpt ξ) (a : Ω) :
    unitAt ξ p a ↔ ∃ s : X.presheaf.stalk p.1, IsUnit s ∧ genMap ξ p s = a := by
  constructor
  · rintro ⟨h0, ⟨s, hs⟩, ⟨t, ht⟩⟩
    refine ⟨s, ?_, hs⟩
    have h1 : genMap ξ p (1 - s * t) = 0 := by
      rw [map_sub, map_mul, map_one, hs, ht, mul_inv_cancel₀ h0, sub_self]
    rcases IsLocalRing.isUnit_or_isUnit_one_sub_self (s * t) with h | h
    · exact isUnit_of_mul_isUnit_left h
    · exact absurd (h1 ▸ h.map (genMap ξ p)) not_isUnit_zero
  · rintro ⟨s, ⟨u, rfl⟩, rfl⟩
    refine ⟨(u.isUnit.map (genMap ξ p)).ne_zero, ⟨_, rfl⟩, ⟨(u⁻¹ : _ˣ), ?_⟩⟩
    exact (map_units_inv (genMap ξ p) u)

theorem isDomain_stalk {ξ : Spec (CommRingCat.of Ω) ⟶ X} (h : IsCptGen ξ) (p : Cpt ξ) :
    IsDomain (X.presheaf.stalk p.1) :=
  Function.Injective.isDomain (genMap ξ p) (h.inj p)

theorem regAt_self {ξ : Spec (CommRingCat.of Ω) ⟶ X} (h : IsCptGen ξ) : regAt ξ (self ξ) = ⊤ := by
  rw [regAt, RingHom.range_eq_top, genMap_self]
  exact h.bij.2

theorem eq_of_specializes {ξ : Spec (CommRingCat.of Ω) ⟶ X} (h : IsCptGen ξ) {y : X}
    (hy : y ⤳ genPt ξ) : y = genPt ξ := by
  have hF : IsField (X.presheaf.stalk (genPt ξ)) :=
    MulEquiv.isField (Field.toIsField Ω) (RingEquiv.ofBijective _ h.bij).toMulEquiv
  have hr : y ∈ Set.range (X.fromSpecStalk (genPt ξ)) := by
    rw [Scheme.range_fromSpecStalk]; exact hy
  obtain ⟨z, rfl⟩ := hr
  let _ := hF.toField
  have : z = IsLocalRing.closedPoint (X.presheaf.stalk (genPt ξ)) :=
    Subsingleton.elim (α := PrimeSpectrum (X.presheaf.stalk (genPt ξ))) _ _
  rw [this, Scheme.fromSpecStalk_closedPoint]

end General

section Affine

variable {R K : Type} [CommRing R] [Field K]

abbrev pt (φ : R →+* K) : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom φ)

def tS (p : Spec (CommRingCat.of R)) : R →+* (Spec (CommRingCat.of R)).presheaf.stalk p :=
  (StructureSheaf.toStalk R p).hom

theorem genMap_toStalk (φ : R →+* K) (p : Cpt (pt φ)) (r : R) :
    genMap (pt φ) p (tS p.1 r) = φ r := by
  have h1 := Scheme.germ_stalkClosedPointTo_Spec (R := CommRingCat.of R) (S := CommRingCat.of K)
    (CommRingCat.ofHom φ)
  have h2 := (Spec (CommRingCat.of R)).presheaf.germ_stalkSpecializes (U := ⊤) (y := p.1) trivial p.2
  have h3 : (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (Spec (CommRingCat.of R)).presheaf.germ ⊤ p.1 trivial ≫
      ((Spec (CommRingCat.of R)).presheaf.stalkSpecializes p.2 ≫ Scheme.stalkClosedPointTo (pt φ)) =
      CommRingCat.ofHom φ := by
    have h4 : (Spec (CommRingCat.of R)).presheaf.germ ⊤ p.1 trivial ≫
      ((Spec (CommRingCat.of R)).presheaf.stalkSpecializes p.2 ≫ Scheme.stalkClosedPointTo (pt φ)) =
        (Scheme.ΓSpecIso (CommRingCat.of R)).hom ≫ CommRingCat.ofHom φ :=
      (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ Scheme.stalkClosedPointTo (pt φ)) h2).trans h1)
    exact (congrArg ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ ·) h4).trans (Iso.inv_hom_id_assoc _ _)
  exact congrArg (fun f => f.hom r) h3

theorem exists_frac (φ : R →+* K) (p : Cpt (pt φ)) (x : (Spec (CommRingCat.of R)).presheaf.stalk p.1) :
    ∃ a s : R, s ∉ p.1.asIdeal ∧
      x * tS p.1 s = tS p.1 a := by
  have key : ∀ (q : PrimeSpectrum R) (y : (Spec.structureSheaf R).presheaf.stalk q), ∃ a s : R, s ∉ q.asIdeal ∧
      y * algebraMap R _ s = algebraMap R _ a := fun q y => by
    obtain ⟨⟨a, s⟩, h⟩ := IsLocalization.surj q.asIdeal.primeCompl y
    exact ⟨a, s, s.2, h⟩
  exact key p.1 x

theorem isUnit_toStalk (p : PrimeSpectrum R) {s : R} (hs : s ∉ p.asIdeal) :
    IsUnit (tS p s) :=
  IsLocalization.map_units (M := p.asIdeal.primeCompl)
    ((Spec.structureSheaf R).presheaf.stalk p) ⟨s, hs⟩

theorem mem_regAt_iff (φ : R →+* K) (p : Cpt (pt φ)) (c : K) :
    c ∈ regAt (pt φ) p ↔ ∃ a s : R, s ∉ p.1.asIdeal ∧ φ s ≠ 0 ∧ c * φ s = φ a := by
  have hne : ∀ s : R, s ∉ p.1.asIdeal → φ s ≠ 0 := fun s hs => by
    rw [← genMap_toStalk φ p]
    exact ((isUnit_toStalk p.1 hs).map (genMap (pt φ) p)).ne_zero
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨a, s, hs, h⟩ := exists_frac φ p x
    refine ⟨a, s, hs, hne s hs, ?_⟩
    rw [← genMap_toStalk φ p, ← genMap_toStalk φ p]
    exact (map_mul (genMap (pt φ) p) _ _).symm.trans (congrArg (genMap (pt φ) p) h)
  · rintro ⟨a, s, hs, h0, h⟩
    obtain ⟨v, hv⟩ := (isUnit_toStalk p.1 hs).exists_right_inv
    refine ⟨tS p.1 a * v, ?_⟩
    have e : φ s * genMap (pt φ) p v = 1 := by
      rw [← genMap_toStalk φ p]
      exact (map_mul (genMap (pt φ) p) _ _).symm.trans
        ((congrArg (genMap (pt φ) p) hv).trans (map_one _))
    refine (map_mul (genMap (pt φ) p) _ _).trans ?_
    rw [genMap_toStalk, ← h, mul_assoc, e, mul_one]

theorem genPt_asIdeal (φ : R →+* K) : (genPt (pt φ)).asIdeal = RingHom.ker φ := by
  change Ideal.comap φ (IsLocalRing.maximalIdeal K) = _
  rw [IsLocalRing.maximalIdeal_eq_bot]
  rfl

theorem genMap_injective (φ : R →+* K) (hφ : Function.Injective φ) (p : Cpt (pt φ)) :
    Function.Injective (genMap (pt φ) p) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨a, s, hs, h⟩ := exists_frac φ p x
  have h1 := (map_mul (genMap (pt φ) p) _ _).symm.trans (congrArg (genMap (pt φ) p) h)
  rw [hx, zero_mul, genMap_toStalk] at h1
  have ha : a = 0 := hφ (by rw [← h1, map_zero])
  rw [ha, map_zero] at h
  exact (isUnit_toStalk p.1 hs).mul_left_eq_zero.mp h

theorem isCptGen_fractionRing [IsDomain R] [Algebra R K] [IsFractionRing R K] :
    IsCptGen (pt (algebraMap R K)) := by
  have hi := IsFractionRing.injective R K
  refine ⟨?_, genMap_injective _ hi⟩
  rw [← genMap_self]
  refine ⟨genMap_injective _ hi _, fun c => ?_⟩
  obtain ⟨a, s, hs, rfl⟩ := IsFractionRing.div_surjective (A := R) c
  have h0 : algebraMap R K s ≠ 0 := (map_ne_zero_iff _ hi).2 (nonZeroDivisors.ne_zero hs)
  refine (mem_regAt_iff _ (self _) _).2 ⟨a, s, ?_, h0, div_mul_cancel₀ _ h0⟩
  change s ∉ (genPt (pt (algebraMap R K))).asIdeal
  rw [genPt_asIdeal]
  exact h0

theorem injective_of_isCptGen [IsDomain R] (φ : R →+* K) (h : IsCptGen (pt φ)) :
    Function.Injective φ := by
  have hb : (⊥ : PrimeSpectrum R) ⤳ (genPt (pt φ) : PrimeSpectrum R) :=
    (PrimeSpectrum.le_iff_specializes _ _).1 bot_le
  have e := eq_of_specializes h hb
  rw [RingHom.injective_iff_ker_eq_bot, ← genPt_asIdeal, ← e]
  rfl

end Affine

section Int

theorem isCptGen_int : IsCptGen (pt (algebraMap ℤ ℚ)) := isCptGen_fractionRing

def two : Cpt (pt (algebraMap ℤ ℚ)) :=
  ⟨(⟨Ideal.span {2}, (Ideal.span_singleton_prime two_ne_zero).2 Int.prime_two⟩ : PrimeSpectrum ℤ),
    (PrimeSpectrum.le_iff_specializes _ _).1 (by
      change (genPt (pt (algebraMap ℤ ℚ))).asIdeal ≤ _
      rw [genPt_asIdeal, (RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective ℤ ℚ)]
      exact bot_le)⟩

theorem half_notMem : (2 : ℚ)⁻¹ ∉ regAt _ two := by
  rw [mem_regAt_iff]
  rintro ⟨a, s, hs, -, h⟩
  apply hs
  change s ∈ Ideal.span {(2 : ℤ)}
  rw [Ideal.mem_span_singleton]
  refine ⟨a, ?_⟩
  simp only [algebraMap_int_eq, eq_intCast] at h
  have : (s : ℚ) = 2 * a := by rw [← h]; ring
  exact_mod_cast this

theorem not_unitAt_two : ¬ unitAt _ two (2 : ℚ) := fun h => half_notMem h.2.2

theorem unitAt_three : unitAt _ two (3 : ℚ) := by
  have h : ∀ n : ℤ, ¬ (2 : ℤ) ∣ n → n ∉ two.1.asIdeal := fun n hn hm =>
    hn (Ideal.mem_span_singleton.1 hm)
  refine ⟨by norm_num, (mem_regAt_iff _ _ _).2 ⟨3, 1, h 1 (by decide), by simp, by simp⟩,
    (mem_regAt_iff _ _ _).2 ⟨1, 3, h 3 (by decide), by simp, by simp⟩⟩

theorem not_isCptGen_closed : ¬ IsCptGen (pt (Int.castRingHom (ZMod 2))) := fun h => by
  have := injective_of_isCptGen _ h (a₁ := 2) (a₂ := 0) (by decide)
  exact absurd this (by decide)

theorem not_isCptGen_real : ¬ IsCptGen (pt (algebraMap ℤ ℝ)) := fun h => by
  have h1 : Real.sqrt 2 ∈ regAt _ (self (pt (algebraMap ℤ ℝ))) := by rw [regAt_self h]; trivial
  obtain ⟨a, s, -, h0, e⟩ := (mem_regAt_iff _ _ _).1 h1
  simp only [algebraMap_int_eq, eq_intCast] at h0 e
  exact irrational_sqrt_two ⟨(a : ℚ) / s, by push_cast; rw [← e, mul_div_cancel_right₀ _ h0]⟩

end Int

end GlobalTheory.CompanionTheory.Ar.CptModel
