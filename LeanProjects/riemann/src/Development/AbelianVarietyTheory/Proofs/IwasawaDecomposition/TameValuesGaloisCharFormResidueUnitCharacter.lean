import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExponentAndTwistData
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemZpowersOfTameGen
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTameGenAtOfValuationSubring
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FixedOfPowFixed
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteDimensionalForms
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDoubleCosetsDefiniteUnitaryMaximalLevelStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitPlOfNotIsConjPl
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OpenKerCharWildEqOneOfPowEqOneStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPowJointStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsInertiaTameCharPrimitiveRootOfUniformizerRStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConjInertiaTameCharOtherPlaceStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsZetaPowCloseToUnitZpowStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.TameValChar

theorem L_wildKill : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {M : Type} [CommGroup M] (φ : Formalism.ConjugateSelfDual.G E Ω →* M) (P : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (m : ℕ),
    Formalism.ConjugateSelfDual.IsPlaceOver A P → IsOpen (φ.ker : Set (Formalism.ConjugateSelfDual.G E Ω)) → ((m : ℕ) : 𝓞 E) ∉ P.asIdeal →
    ∀ τ : Formalism.ConjugateSelfDual.G E Ω, (∀ y : Ω, y ≠ 0 → A.valuation (τ y / y - 1) < 1) → (∃ N : ℕ, φ τ ^ (m ^ N) = 1) → φ τ = 1 := GlobalTheory.T.openKerChar_wild_eq_one_of_pow_eq_one

theorem L_joint : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {M : Type} [CommGroup M] (φ : Formalism.ConjugateSelfDual.G E Ω →* M) (P : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (L : ℕ)
    (γ : Formalism.ConjugateSelfDual.G E Ω) (π : Ω) (w : E),
    Formalism.ConjugateSelfDual.IsPlaceOver A P → IsOpen (φ.ker : Set (Formalism.ConjugateSelfDual.G E Ω)) → ((L : ℕ) : 𝓞 E) ∉ P.asIdeal → Formalism.BasicNotions.TameGenAt A γ →
    (∀ τ : Formalism.ConjugateSelfDual.G E Ω, (∀ y : Ω, y ≠ 0 → A.valuation (τ y / y - 1) < 1) → φ τ = 1) → φ γ ^ L = 1 →
    π ≠ 0 → π ^ L = algebraMap E Ω w →
    ∀ σ ∈ ReciprocityTheory.Gal.Ine (F := E) A, ∃ b : ℕ, φ σ = φ γ ^ b ∧ σ π = (γ π / π) ^ b * π := GlobalTheory.T.inertia_of_tameGenAt_of_char_pow_eq_one

theorem L_surj : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (P : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (L : ℕ) (ϖ : 𝓞 E) (π : Ω),
    Formalism.ConjugateSelfDual.IsPlaceOver A P → ((L : ℕ) : 𝓞 E) ∉ P.asIdeal → ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 →
    π ^ L = algebraMap E Ω (ϖ : E) → ∃ σ ∈ ReciprocityTheory.Gal.Ine (F := E) A, IsPrimitiveRoot (σ π / π) L := GlobalTheory.T.exists_inertia_tameChar_primitiveRoot_of_uniformizerRoot

theorem L_move : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (P : HeightOneSpectrum (𝓞 E)) (e : ℤ) (σ : Formalism.ConjugateSelfDual.G E Ω) (u : 𝓞 E) (A₀ : ValuationSubring Ω) (ϖ₀ : 𝓞 E) (π₀ : Ω),
    Formalism.ConjugateSelfDual.IsPlaceOver A₀ P → ϖ₀ ∈ P.asIdeal → ϖ₀ ∉ P.asIdeal ^ 2 →
    π₀ ^ (Formalism.ConjugateSelfDual.normV P - 1) = algebraMap E Ω (ϖ₀ : E) → Formalism.L2.NX.TameRep P e σ u →
    ∃ g : Formalism.ConjugateSelfDual.G E Ω, g * σ * g⁻¹ ∈ ReciprocityTheory.Gal.Ine (F := E) A₀ ∧
      A₀.valuation ((g * σ * g⁻¹) π₀ / π₀ - (algebraMap E Ω (u : E)) ^ e) < 1 := GlobalTheory.T.exists_conj_inertia_tameChar_other_place

theorem L_teich : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    (P : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (ζ : Ω),
    Formalism.ConjugateSelfDual.IsPlaceOver A P → IsPrimitiveRoot ζ (Formalism.ConjugateSelfDual.normV P - 1) → ∀ (u : 𝓞 E) (e : ℤ), u ∉ P.asIdeal →
    ∃ a : ℕ, A.valuation (ζ ^ a - (algebraMap E Ω (u : E)) ^ e) < 1 := GlobalTheory.T.exists_zeta_pow_close_to_unit_zpow

theorem L_vone : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    (P : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω), Formalism.ConjugateSelfDual.IsPlaceOver A P →
    ∀ u : 𝓞 E, u ∉ P.asIdeal → A.valuation (algebraMap E Ω (u : E)) = 1 := by
  intro E Ω _ _ _ _ P A hA u hu
  apply le_antisymm
  · rw [A.valuation_le_one_iff]
    apply ReciprocityTheory.Gal.mem_of_isIntegral_int
    exact (RingOfIntegers.isIntegral_coe u).algebraMap
  · exact not_lt.1 ((hA u).not.2 hu)

theorem two_le_normV_and_not_mem : ∀ {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)),
    2 ≤ Formalism.ConjugateSelfDual.normV P ∧ (((Formalism.ConjugateSelfDual.normV P - 1 : ℕ) : ℕ) : 𝓞 E) ∉ P.asIdeal := by
  intro E _ _ P
  classical
  have hmax : P.asIdeal.IsMaximal := P.isMaximal
  letI : Field (𝓞 E ⧸ P.asIdeal) := Ideal.Quotient.field P.asIdeal
  haveI : Finite (𝓞 E ⧸ P.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot P.asIdeal P.ne_bot
  letI : Fintype (𝓞 E ⧸ P.asIdeal) := Fintype.ofFinite _
  have hcard : Formalism.ConjugateSelfDual.normV P = Fintype.card (𝓞 E ⧸ P.asIdeal) := by
    rw [Formalism.ConjugateSelfDual.normV, Nat.card_eq_fintype_card]
  have h2 : 2 ≤ Formalism.ConjugateSelfDual.normV P := by
    rw [hcard]; exact Fintype.one_lt_card
  refine ⟨h2, fun h => ?_⟩
  have h0 : (Ideal.Quotient.mk P.asIdeal) (((Formalism.ConjugateSelfDual.normV P - 1 : ℕ) : ℕ) : 𝓞 E) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2 h
  rw [map_natCast, Nat.cast_sub (by omega), hcard, FiniteField.cast_card_eq_zero, Nat.cast_one, zero_sub,
    neg_eq_zero] at h0
  exact one_ne_zero h0

section Small

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]

theorem not_val_lt_one {A : ValuationSubring Ω} {P : HeightOneSpectrum (𝓞 E)} (hA : Formalism.ConjugateSelfDual.IsPlaceOver A P) {k : ℕ}
    (hk : ((k : ℕ) : 𝓞 E) ∉ P.asIdeal) : ¬ A.valuation (k : Ω) < 1 := by
  intro h
  apply hk
  rw [← hA]
  simpa using h

theorem ne_zero_of_not_mem {P : HeightOneSpectrum (𝓞 E)} {k : ℕ} (hk : ((k : ℕ) : 𝓞 E) ∉ P.asIdeal) : k ≠ 0 := by
  rintro rfl
  exact hk (by simp)

theorem ine_fix_root {A : ValuationSubring Ω} {P : HeightOneSpectrum (𝓞 E)} (hA : Formalism.ConjugateSelfDual.IsPlaceOver A P) {k : ℕ}
    (hk : ((k : ℕ) : 𝓞 E) ∉ P.asIdeal) {σ : Formalism.ConjugateSelfDual.G E Ω} (hσ : σ ∈ ReciprocityTheory.Gal.Ine (F := E) A) {ζ : Ω}
    (hζ : ζ ^ k = 1) : σ ζ = ζ := by
  refine ReciprocityTheory.Gal.eq_of_pow_eq_one A (not_val_lt_one hA hk) ?_ hζ
    (hσ.2 ζ (ReciprocityTheory.Gal.valuation_eq_one_of_pow_eq_one A (ne_zero_of_not_mem hk) hζ).le)
  rw [← map_pow, hζ, map_one]

theorem frob_root {A : ValuationSubring Ω} {P : HeightOneSpectrum (𝓞 E)} (hA : Formalism.ConjugateSelfDual.IsPlaceOver A P) {k : ℕ}
    (hk : ((k : ℕ) : 𝓞 E) ∉ P.asIdeal) {τ : Formalism.ConjugateSelfDual.G E Ω} (hτ : Formalism.ConjugateSelfDual.IsFrob A (Formalism.ConjugateSelfDual.normV P) τ) {ζ : Ω}
    (hζ : ζ ^ k = 1) : τ ζ = ζ ^ Formalism.ConjugateSelfDual.normV P := by
  refine ReciprocityTheory.Gal.eq_of_pow_eq_one A (not_val_lt_one hA hk) ?_ ?_
    (hτ.2 ζ (ReciprocityTheory.Gal.valuation_eq_one_of_pow_eq_one A (ne_zero_of_not_mem hk) hζ).le)
  · rw [← map_pow, hζ, map_one]
  · rw [← pow_mul, mul_comm, pow_mul, hζ, one_pow]

theorem modEq_of_pow_eq {ζ : Ω} {k a b : ℕ} (h : IsPrimitiveRoot ζ k) (hk : k ≠ 0) (hab : ζ ^ a = ζ ^ b) :
    a ≡ b [MOD k] := by
  have hu : IsPrimitiveRoot (h.isUnit hk).unit k := IsPrimitiveRoot.coe_units_iff.mp (by simpa using h)
  rw [hu.eq_orderOf]
  apply pow_eq_pow_iff_modEq.1
  ext
  simpa using hab

theorem zpow_close {A : ValuationSubring Ω} {x y : Ω} (hy : A.valuation y = 1) (hxy : A.valuation (x - y) < 1)
    (e : ℤ) : A.valuation (x ^ e - y ^ e) < 1 := by
  have hy0 : y ≠ 0 := by rintro rfl; simp at hy
  have hw : A.valuation (x / y - 1) < 1 := by
    rw [show x / y - 1 = (x - y) / y by field_simp, map_div₀, hy, div_one]
    exact hxy
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [zero_div, zero_sub, Valuation.map_neg, map_one] at hw
    exact lt_irrefl _ hw
  have hmem : Units.mk0 (x / y) (div_ne_zero hx0 hy0) ∈ A.principalUnitGroup := by
    rw [ValuationSubring.mem_principalUnitGroup_iff]
    exact hw
  have hmem' := zpow_mem hmem e
  rw [ValuationSubring.mem_principalUnitGroup_iff] at hmem'
  simp only [Units.val_zpow_eq_zpow_val, Units.val_mk0] at hmem'
  have e1 : x ^ e - y ^ e = y ^ e * ((x / y) ^ e - 1) := by
    rw [div_zpow, mul_sub, mul_div_cancel₀ _ (zpow_ne_zero e hy0), mul_one]
  rw [e1, map_mul, map_zpow₀, hy, one_zpow, one_mul]
  exact hmem'

end Small

theorem main : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {M : Type} [CommGroup M]
    (φ : Formalism.ConjugateSelfDual.G E Ω →* M) (P : HeightOneSpectrum (𝓞 E)) (e : ℤ) (m : ℕ),
    IsOpen (φ.ker : Set (Formalism.ConjugateSelfDual.G E Ω)) → ((m : ℕ) : 𝓞 E) ∉ P.asIdeal →
    (∀ A : ValuationSubring Ω, IsPlaceOver A P → ∀ σ ∈ Ine (F := E) A, ∃ N : ℕ, φ σ ^ (m ^ N) = 1) →
    (∀ u u' : 𝓞 E, u ∉ P.asIdeal → u' ∉ P.asIdeal → NX.tameVal φ P e (u * u') = NX.tameVal φ P e u * NX.tameVal φ P e u') ∧
    ∀ u u' : 𝓞 E, u ∉ P.asIdeal → u - u' ∈ P.asIdeal → NX.tameVal φ P e u = NX.tameVal φ P e u' := by
  intro E Ω _ _ _ _ _ M _ φ P e m hopen hm hI
  classical
  have hAC : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  obtain ⟨A0, hA0⟩ := ReciprocityTheory.Gal.exists_isPlaceOver Ω P
  obtain ⟨γ, hγ⟩ := GlobalTheory.TameInertiaGen.exists_tameGenAt E Ω P A0 hA0
  obtain ⟨hq2, hq1⟩ := two_le_normV_and_not_mem P
  set q := Formalism.ConjugateSelfDual.normV P with hqdef
  set n := q - 1 with hndef
  obtain ⟨N0, hN0⟩ := hI A0 hA0 γ hγ.1
  set L := n * m ^ N0 with hLdef
  have hL : ((L : ℕ) : 𝓞 E) ∉ P.asIdeal := by
    rw [hLdef, Nat.cast_mul, Nat.cast_pow]
    exact P.isPrime.mul_notMem hq1 (fun h => hm (P.isPrime.mem_of_pow_mem _ h))
  have hL0 : L ≠ 0 := ne_zero_of_not_mem hL
  obtain ⟨ϖ0, hϖ0, hϖ0'⟩ : ∃ ϖ0 : 𝓞 E, ϖ0 ∈ P.asIdeal ∧ ϖ0 ∉ P.asIdeal ^ 2 := by
    have hlt := Ideal.pow_succ_lt_pow (P := P.asIdeal) P.ne_bot 1
    rw [pow_one] at hlt
    obtain ⟨x, hx, hx'⟩ := SetLike.exists_of_lt hlt
    exact ⟨x, hx, hx'⟩
  have hϖ0ne : algebraMap E Ω (ϖ0 : E) ≠ 0 := by
    intro h
    apply hϖ0'
    have : ϖ0 = 0 := by
      have h' : ((ϖ0 : E)) = 0 := (map_eq_zero _).1 h
      exact_mod_cast h'
    rw [this]
    exact zero_mem _
  obtain ⟨π1, hπ1⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap E Ω (ϖ0 : E)) (Nat.pos_of_ne_zero hL0)
  have hπ1ne : π1 ≠ 0 := by
    rintro rfl
    rw [zero_pow hL0] at hπ1
    exact hϖ0ne hπ1.symm
  have hw : ∀ τ : Formalism.ConjugateSelfDual.G E Ω, (∀ y : Ω, y ≠ 0 → A0.valuation (τ y / y - 1) < 1) → φ τ = 1 := fun τ hτ =>
    L_wildKill φ P A0 m hA0 hopen hm τ hτ (hI A0 hA0 τ (GlobalTheory.TameGenPowers.wild_mem_Ine hτ))
  have hγL : φ γ ^ L = 1 := by
    rw [hLdef, mul_comm, pow_mul, hN0, one_pow]
  have hJ := L_joint φ P A0 L γ π1 (ϖ0 : E) hA0 hopen hL hγ hw hγL hπ1ne hπ1
  set ζ1 := γ π1 / π1 with hζ1def
  have hγπ1 : γ π1 = ζ1 * π1 := by rw [hζ1def, div_mul_cancel₀ _ hπ1ne]
  have hζ1L : ζ1 ^ L = 1 := by
    rw [hζ1def, div_pow, ← map_pow, hπ1, AlgEquiv.commutes, div_self hϖ0ne]
  obtain ⟨σ0, hσ0, hprim⟩ := L_surj P A0 L ϖ0 π1 hA0 hL hϖ0 hϖ0' hπ1
  obtain ⟨b0, -, hb0⟩ := hJ σ0 hσ0
  have hζ1prim : IsPrimitiveRoot ζ1 L := by
    rw [hb0, mul_div_cancel_right₀ _ hπ1ne] at hprim
    have h1 : L ∣ orderOf ζ1 := hprim.eq_orderOf ▸ orderOf_pow_dvd b0
    have h2 : orderOf ζ1 ∣ L := orderOf_dvd_of_pow_eq_one hζ1L
    have h3 : orderOf ζ1 = L := Nat.dvd_antisymm h2 h1
    exact h3 ▸ IsPrimitiveRoot.orderOf ζ1

  obtain ⟨τ, hτ⟩ := ReciprocityTheory.Gal.exists_isFrob hA0
  have hσF : τ * γ * τ⁻¹ ∈ ReciprocityTheory.Gal.Ine (F := E) A0 := ReciprocityTheory.Gal.conj_mem_Ine hτ.1 hγ.1
  set η := (τ⁻¹ : Formalism.ConjugateSelfDual.G E Ω) π1 / π1 with hηdef
  have hη : η ^ L = 1 := by
    rw [hηdef, div_pow, ← map_pow, hπ1, AlgEquiv.commutes, div_self hϖ0ne]
  have hyη : (τ⁻¹ : Formalism.ConjugateSelfDual.G E Ω) π1 = η * π1 := by rw [hηdef, div_mul_cancel₀ _ hπ1ne]
  have hγη : γ η = η := ine_fix_root hA0 hL hγ.1 hη
  have hcalc : (τ * γ * τ⁻¹) π1 = ζ1 ^ q * π1 := by
    have e1 : (τ * γ * τ⁻¹) π1 = τ (γ ((τ⁻¹ : Formalism.ConjugateSelfDual.G E Ω) π1)) := rfl
    have e2 : γ ((τ⁻¹ : Formalism.ConjugateSelfDual.G E Ω) π1) = ζ1 * (τ⁻¹ : Formalism.ConjugateSelfDual.G E Ω) π1 := by
      rw [hyη, map_mul, hγη, hγπ1]; ring
    rw [e1, e2, map_mul, ReciprocityTheory.Gal.mul_inv_apply, frob_root hA0 hL hτ hζ1L]
  obtain ⟨b, hbφ, hbπ⟩ := hJ _ hσF
  have hφconj : φ (τ * γ * τ⁻¹) = φ γ := by
    rw [map_mul, map_mul, mul_comm (φ τ), mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one]
  rw [hcalc] at hbπ
  have hζq : ζ1 ^ q = ζ1 ^ b := mul_right_cancel₀ hπ1ne hbπ
  have hmod : q ≡ b [MOD L] := modEq_of_pow_eq hζ1prim hL0 hζq
  have hordγ : orderOf (φ γ) ∣ L := orderOf_dvd_of_pow_eq_one hγL
  have hγq : φ γ ^ q = φ γ ^ b := pow_eq_pow_iff_modEq.2 (hmod.of_dvd hordγ)
  have hγn : φ γ ^ n = 1 := by
    have h1 : φ γ ^ n * φ γ = φ γ := by
      rw [← pow_succ, show n + 1 = q by omega, hγq, ← hbφ, hφconj]
    exact mul_eq_right.1 h1

  set π0 := π1 ^ (m ^ N0) with hπ0def
  have hπ0 : π0 ^ n = algebraMap E Ω (ϖ0 : E) := by
    rw [hπ0def, ← pow_mul, mul_comm, ← hLdef]
    exact hπ1
  have hπ0ne : π0 ≠ 0 := pow_ne_zero _ hπ1ne
  set ζ0 := ζ1 ^ (m ^ N0) with hζ0def
  have hζ0prim : IsPrimitiveRoot ζ0 n := hζ1prim.pow (Nat.pos_of_ne_zero hL0) (by rw [hLdef, mul_comm])
  have hC : ∀ σ ∈ ReciprocityTheory.Gal.Ine (F := E) A0, ∃ b : ℕ, φ σ = φ γ ^ b ∧ σ π0 = ζ0 ^ b * π0 := by
    intro σ hσ
    obtain ⟨b, h1, h2⟩ := hJ σ hσ
    refine ⟨b, h1, ?_⟩
    rw [hπ0def, map_pow, h2, hζ0def, mul_pow, ← pow_mul, ← pow_mul, mul_comm b]
  have hn1A : ¬ A0.valuation (n : Ω) < 1 := not_val_lt_one hA0 hq1
  have hordn : orderOf (φ γ) ∣ n := orderOf_dvd_of_pow_eq_one hγn
  have hK : ∀ (σ : Formalism.ConjugateSelfDual.G E Ω) (u : 𝓞 E) (a : ℕ), Formalism.L2.NX.TameRep P e σ u →
      A0.valuation (ζ0 ^ a - (algebraMap E Ω (u : E)) ^ e) < 1 → φ σ = φ γ ^ a := by
    intro σ u a hσ ha
    obtain ⟨g, hg, hgv⟩ := L_move P e σ u A0 ϖ0 π0 hA0 hϖ0 hϖ0' hπ0 hσ
    obtain ⟨b, hbφ, hbπ⟩ := hC _ hg
    have hφg : φ (g * σ * g⁻¹) = φ σ := by
      rw [map_mul, map_mul, mul_comm (φ g), mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one]
    rw [hbπ, mul_div_cancel_right₀ _ hπ0ne] at hgv
    have hab : ζ0 ^ a = ζ0 ^ b := by
      refine ReciprocityTheory.Gal.eq_of_pow_eq_one A0 hn1A ?_ ?_ ?_
      · rw [← pow_mul, mul_comm, pow_mul, hζ0prim.pow_eq_one, one_pow]
      · rw [← pow_mul, mul_comm, pow_mul, hζ0prim.pow_eq_one, one_pow]
      · have e1 : ζ0 ^ a - ζ0 ^ b = (ζ0 ^ a - (algebraMap E Ω (u : E)) ^ e) - (ζ0 ^ b - (algebraMap E Ω (u : E)) ^ e) := by
          ring
        rw [e1]
        exact lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt ha hgv)
    have hmod' : a ≡ b [MOD n] := modEq_of_pow_eq hζ0prim (ne_zero_of_not_mem hq1) hab
    rw [← hφg, hbφ]
    exact (pow_eq_pow_iff_modEq.2 (hmod'.of_dvd hordn)).symm
  have hγfix : γ ζ0 = ζ0 := ine_fix_root hA0 hq1 hγ.1 hζ0prim.pow_eq_one
  have hγpow : ∀ a : ℕ, (γ ^ a) π0 = ζ0 ^ a * π0 := by
    have hγπ0 : γ π0 = ζ0 * π0 := by
      rw [hπ0def, map_pow, hγπ1, mul_pow, hζ0def]
    intro a
    induction a with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, AlgEquiv.mul_apply, hγπ0, map_mul, ih,
        ine_fix_root hA0 hq1 (pow_mem hγ.1 k) hζ0prim.pow_eq_one, pow_succ]
      ring
  have hX : ∀ u : 𝓞 E, u ∉ P.asIdeal → ∃ a : ℕ, A0.valuation (ζ0 ^ a - (algebraMap E Ω (u : E)) ^ e) < 1 ∧
      Formalism.L2.NX.TameRep P e (γ ^ a) u := by
    intro u hu
    obtain ⟨a, ha⟩ := L_teich P A0 ζ0 hA0 hζ0prim u e hu
    refine ⟨a, ha, A0, hA0, pow_mem hγ.1 a, ϖ0, π0, hϖ0, hϖ0', hπ0, ?_⟩
    rw [hγpow, mul_div_cancel_right₀ _ hπ0ne]
    exact ha
  have hval : ∀ u : 𝓞 E, u ∉ P.asIdeal → ∀ a : ℕ,
      A0.valuation (ζ0 ^ a - (algebraMap E Ω (u : E)) ^ e) < 1 → Formalism.L2.NX.tameVal φ P e u = φ γ ^ a := by
    intro u hu a ha
    obtain ⟨a', -, hrep⟩ := hX u hu
    have hex : ∃ σ, Formalism.L2.NX.TameRep P e σ u := ⟨_, hrep⟩
    rw [Formalism.L2.NX.tameVal, dif_pos hex]
    exact hK _ u a hex.choose_spec ha
  have hU : ∀ u : 𝓞 E, u ∉ P.asIdeal → A0.valuation ((algebraMap E Ω (u : E)) ^ e) = 1 := by
    intro u hu
    rw [map_zpow₀, L_vone P A0 hA0 u hu, one_zpow]
  have hζa : ∀ a : ℕ, A0.valuation (ζ0 ^ a) = 1 := fun a =>
    ReciprocityTheory.Gal.valuation_eq_one_of_pow_eq_one A0 (ne_zero_of_not_mem hq1)
      (by rw [← pow_mul, mul_comm, pow_mul, hζ0prim.pow_eq_one, one_pow])
  refine ⟨fun u u' hu hu' => ?_, fun u u' hu huu' => ?_⟩
  · obtain ⟨a, ha, -⟩ := hX u hu
    obtain ⟨a', ha', -⟩ := hX u' hu'
    have huu : u * u' ∉ P.asIdeal := P.isPrime.mul_notMem hu hu'
    rw [hval u hu a ha, hval u' hu' a' ha', hval (u * u') huu (a + a'), pow_add]
    have e1 : ζ0 ^ (a + a') - (algebraMap E Ω ((u * u' : 𝓞 E) : E)) ^ e =
        ζ0 ^ a * (ζ0 ^ a' - (algebraMap E Ω (u' : E)) ^ e) +
          (algebraMap E Ω (u' : E)) ^ e * (ζ0 ^ a - (algebraMap E Ω (u : E)) ^ e) := by
      have hc : ((u * u' : 𝓞 E) : E) = (u : E) * (u' : E) := by simp
      rw [hc, map_mul, mul_zpow, pow_add]
      ring
    rw [e1]
    refine Valuation.map_add_lt _ ?_ ?_
    · rw [map_mul, hζa, one_mul]; exact ha'
    · rw [map_mul, hU u' hu', one_mul]; exact ha
  · have hu' : u' ∉ P.asIdeal := by
      intro h
      apply hu
      have : u = (u - u') + u' := by ring
      rw [this]
      exact add_mem huu' h
    obtain ⟨a, ha, -⟩ := hX u hu
    rw [hval u hu a ha, hval u' hu' a ?_]
    have hclose : A0.valuation (algebraMap E Ω (u : E) - algebraMap E Ω (u' : E)) < 1 := by
      have h0 := (hA0 (u - u')).2 huu'
      simpa [map_sub] using h0
    have h2 := zpow_close (L_vone P A0 hA0 u' hu') hclose e
    have e1 : ζ0 ^ a - (algebraMap E Ω (u' : E)) ^ e =
        (ζ0 ^ a - (algebraMap E Ω (u : E)) ^ e) + ((algebraMap E Ω (u : E)) ^ e - (algebraMap E Ω (u' : E)) ^ e) := by
      ring
    rw [e1]
    exact Valuation.map_add_lt _ ha h2

end GlobalTheory.TameValChar
