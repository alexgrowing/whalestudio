import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.WeilDeligneParamMonodromyEqZeroIff
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTameGenAtOfValuationSubring
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FixedOfPowFixed

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
open Pointwise

namespace GlobalTheory.TameConjInv

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω]

theorem wild_mem_Ine (B : ValuationSubring Ω) {σ : G ℚ Ω}
    (hσ : ∀ y : Ω, y ≠ 0 → B.valuation (σ y / y - 1) < 1) : σ ∈ Ine (F := ℚ) B := by
  have hv : ∀ y : Ω, B.valuation (σ y) = B.valuation y := by
    intro y
    rcases eq_or_ne y 0 with rfl | hy
    · simp
    · have h1 : B.valuation (σ y / y) = 1 := by
        have e : σ y / y = 1 + (σ y / y - 1) := by ring
        rw [e, Valuation.map_one_add_of_lt _ (hσ y hy)]
      rw [map_div₀] at h1
      exact (div_eq_one_iff_eq (by simpa using hy)).1 h1
  refine ⟨?_, fun x hx => ?_⟩
  · show σ • B = B
    ext y
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def,
      ← B.valuation_le_one_iff, ← B.valuation_le_one_iff, ← hv ((σ⁻¹ : G ℚ Ω) y), mul_inv_apply]
  · rcases eq_or_ne x 0 with rfl | hx0
    · simp
    · have e : σ x - x = x * (σ x / x - 1) := by field_simp
      rw [e, map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_left' hx) (hσ x hx0)

theorem map_one_eq_zero (B : ValuationSubring Ω) {P : Type} [AddCommGroup P] (F : G ℚ Ω → P)
    (hadd : ∀ s ∈ Ine (F := ℚ) B, ∀ t ∈ Ine (F := ℚ) B, F (s * t) = F s + F t) : F 1 = 0 := by
  have h := hadd 1 (one_mem _) 1 (one_mem _)
  rw [mul_one] at h
  simpa using h

theorem map_pow_eq (B : ValuationSubring Ω) {P : Type} [AddCommGroup P] (F : G ℚ Ω → P)
    (hadd : ∀ s ∈ Ine (F := ℚ) B, ∀ t ∈ Ine (F := ℚ) B, F (s * t) = F s + F t)
    {s : G ℚ Ω} (hs : s ∈ Ine (F := ℚ) B) (k : ℕ) : F (s ^ k) = k • F s := by
  induction k with
  | zero => simpa using map_one_eq_zero B F hadd
  | succ k ih =>
    rw [pow_succ, hadd _ (pow_mem hs k) _ hs, ih, succ_nsmul]

variable [IsAlgClosure ℚ Ω]

theorem eq_zero_of_wild (l : ℕ) [Fact l.Prime] (n : ℕ) (B : ValuationSubring Ω)
    (hlB : ¬ B.valuation (l : Ω) < 1) {P : Type} [AddCommGroup P] (F : G ℚ Ω → P)
    (htor : ∀ x : P, l ^ n • x = 0)
    (hlc : IsLocallyConstant (fun s : Ine (F := ℚ) B => F s))
    (hadd : ∀ s ∈ Ine (F := ℚ) B, ∀ t ∈ Ine (F := ℚ) B, F (s * t) = F s + F t)
    (σ : G ℚ Ω) (hσ : ∀ y : Ω, y ≠ 0 → B.valuation (σ y / y - 1) < 1) : F σ = 0 := by
  have hl : l.Prime := Fact.out
  have hvl1 : B.valuation (l : Ω) = 1 :=
    le_antisymm ((B.valuation_le_one_iff _).mpr (natCast_mem B l)) (not_lt.mp hlB)
  have hσI := wild_mem_Ine B hσ
  have h0 := map_one_eq_zero B F hadd
  obtain ⟨t, ht, hte⟩ := isOpen_induced_iff.mp (hlc.isOpen_fiber (0 : P))
  have h1t : (1 : G ℚ Ω) ∈ t := by
    have : ((⟨1, one_mem _⟩ : Ine (F := ℚ) B) : G ℚ Ω) ∈ t := by
      show (⟨1, one_mem _⟩ : Ine (F := ℚ) B) ∈ Subtype.val ⁻¹' t
      rw [hte]; exact h0
    exact this
  obtain ⟨L, hL, hsub⟩ := (krullTopology_mem_nhds_one_iff ℚ Ω _).mp (ht.mem_nhds h1t)
  have : IsGalois ℚ Ω := IsAlgClosure.isGalois ℚ Ω
  have hidx : L.fixingSubgroup.index ≠ 0 := by
    rw [← IntermediateField.finrank_eq_fixingSubgroup_index]
    exact Module.finrank_pos.ne'
  obtain ⟨N, hN, -, hmem⟩ := Subgroup.exists_pow_mem_of_index_ne_zero hidx σ
  obtain ⟨a, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hN.ne' l hl.ne_one
  have hτ : σ ^ m ∈ L.fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff] at hmem ⊢
    intro x hx
    refine GlobalTheory.WildInertiaChar.fixed_of_pow_fixed B (σ ^ m) (GlobalTheory.WildInertiaChar.wild_pow B σ hσ m) (l ^ a) ?_ x ?_
    · rw [Nat.cast_pow, map_pow, hvl1, one_pow]; exact lt_irrefl _
    · rw [← pow_mul, mul_comm]; exact hmem x hx
  have hm0 : m • F σ = 0 := by
    rw [← map_pow_eq B F hadd hσI m]
    have : (⟨σ ^ m, pow_mem hσI m⟩ : Ine (F := ℚ) B) ∈ Subtype.val ⁻¹' t := hsub hτ
    rw [hte] at this
    exact this
  have hc : Nat.Coprime (l ^ n) m := ((Nat.Prime.coprime_iff_not_dvd hl).mpr hm).pow_left n
  have hd : addOrderOf (F σ) ∣ Nat.gcd (l ^ n) m :=
    Nat.dvd_gcd (addOrderOf_dvd_of_nsmul_eq_zero (htor _)) (addOrderOf_dvd_of_nsmul_eq_zero hm0)
  rw [hc, Nat.dvd_one] at hd
  have := addOrderOf_nsmul_eq_zero (F σ)
  rwa [hd, one_nsmul] at this

end GlobalTheory.TameConjInv

namespace GlobalTheory.TameConjInv

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω]

theorem exists_zsmul (B : ValuationSubring Ω) {γ : G ℚ Ω} (hγ : Formalism.BasicNotions.TameGenAt B γ) {P : Type}
    [AddCommGroup P] (F : G ℚ Ω → P)
    (hlc : IsLocallyConstant (fun s : Ine (F := ℚ) B => F s))
    (hadd : ∀ s ∈ Ine (F := ℚ) B, ∀ t ∈ Ine (F := ℚ) B, F (s * t) = F s + F t)
    (hw : ∀ σ : G ℚ Ω, (∀ y : Ω, y ≠ 0 → B.valuation (σ y / y - 1) < 1) → F σ = 0)
    (s : G ℚ Ω) (hs : s ∈ Ine (F := ℚ) B) : ∃ k : ℤ, F s = k • F γ := by
  have h0 := map_one_eq_zero B F hadd
  have hinv : ∀ x ∈ Ine (F := ℚ) B, F x⁻¹ = - F x := by
    intro x hx
    have := hadd x hx x⁻¹ (inv_mem hx)
    rw [mul_inv_cancel, h0] at this
    exact (neg_eq_of_add_eq_zero_right this.symm).symm
  have key : ∀ h ∈ Subgroup.closure (insert γ {σ : G ℚ Ω | ∀ y : Ω, y ≠ 0 → B.valuation (σ y / y - 1) < 1}),
      h ∈ Ine (F := ℚ) B ∧ ∃ k : ℤ, F h = k • F γ := by
    intro h hh
    induction hh using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with rfl | hx
      · exact ⟨hγ.1, 1, by simp⟩
      · exact ⟨wild_mem_Ine B hx, 0, by simp [hw x hx]⟩
    | one => exact ⟨one_mem _, 0, by simp [h0]⟩
    | mul x y _ _ ihx ihy =>
      obtain ⟨hx, k, hk⟩ := ihx
      obtain ⟨hy, k', hk'⟩ := ihy
      exact ⟨mul_mem hx hy, k + k', by rw [hadd x hx y hy, hk, hk', add_zsmul]⟩
    | inv x _ ihx =>
      obtain ⟨hx, k, hk⟩ := ihx
      exact ⟨inv_mem hx, -k, by rw [hinv x hx, hk, neg_zsmul]⟩
  obtain ⟨t, ht, hte⟩ := isOpen_induced_iff.mp (hlc.isOpen_fiber (F s))
  have hst : s ∈ t := by
    show (⟨s, hs⟩ : Ine (F := ℚ) B) ∈ Subtype.val ⁻¹' t
    rw [hte]; rfl
  obtain ⟨h, hht, hhH⟩ := mem_closure_iff.mp (hγ.2 hs) t ht hst
  obtain ⟨hhI, k, hk⟩ := key h hhH
  refine ⟨k, ?_⟩
  have : (⟨h, hhI⟩ : Ine (F := ℚ) B) ∈ Subtype.val ⁻¹' t := hht
  rw [hte] at this
  rw [← hk]
  exact this.symm

theorem prime_normV (v : Pl) : (normV v).Prime := by
  haveI := v.isPrime
  haveI := v.isMaximal
  haveI : Finite (𝓞 ℚ ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ v.ne_bot
  have hp : (ringChar (𝓞 ℚ ⧸ v.asIdeal)).Prime := CharP.char_is_prime (𝓞 ℚ ⧸ v.asIdeal) _
  haveI : Fact (ringChar (𝓞 ℚ ⧸ v.asIdeal)).Prime := ⟨hp⟩
  have hs : Function.Surjective (ZMod.castHom (dvd_refl (ringChar (𝓞 ℚ ⧸ v.asIdeal))) (𝓞 ℚ ⧸ v.asIdeal)) := by
    intro y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨n, rfl⟩ := Rat.ringOfIntegersEquiv.symm.surjective x
    exact ⟨(n : ZMod _), by simp⟩
  have hb := Nat.card_eq_of_bijective _ ⟨RingHom.injective _, hs⟩
  rw [normV, ← hb, Nat.card_zmod]
  exact hp

theorem not_mem_of_dvd (l : ℕ) [Fact l.Prime] {n : ℕ} {w : Pl} (hn : 1 ≤ n) (hdiv : l ^ n ∣ normV w - 1) :
    ((l : ℕ) : 𝓞 ℚ) ∉ w.asIdeal := by
  intro hlw
  have hpos : 1 < normV w := (prime_normV w).one_lt
  obtain ⟨k, hk⟩ := (dvd_pow_self l (by omega : n ≠ 0)).trans hdiv
  have e : normV w = l * k + 1 := by omega
  have hmem : ((normV w : ℕ) : 𝓞 ℚ) ∈ w.asIdeal := Ideal.absNorm_mem w.asIdeal
  rw [e] at hmem
  push_cast at hmem
  have h1 : (1 : 𝓞 ℚ) ∈ w.asIdeal := by
    have := w.asIdeal.sub_mem hmem (w.asIdeal.mul_mem_right (k : 𝓞 ℚ) hlw)
    simpa using this
  exact w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1)

theorem exists_residue_hom (B : ValuationSubring Ω) {g : G ℚ Ω} (hg : g ∈ Dec (F := ℚ) B) :
    ∃ σ : IsLocalRing.ResidueField B →+* IsLocalRing.ResidueField B, ∀ (x : Ω) (hx : x ∈ B),
      σ (IsLocalRing.residue B ⟨x, hx⟩) =
        IsLocalRing.residue B ⟨g x, (apply_mem_iff_of_mem_Dec hg x).2 hx⟩ := by
  let φ : B →+* B := (g : Ω →+* Ω).restrict B B fun x hx => (apply_mem_iff_of_mem_Dec hg x).2 hx
  haveI : IsLocalHom φ := ⟨fun a ha => by
    by_contra hn
    have h1 : B.valuation (a : Ω) < 1 := (B.valuation_lt_one_iff a).1 hn
    have h2 := (valuation_apply_lt_one_iff (F := ℚ) hg _).2 h1
    exact (B.valuation_lt_one_iff (φ a)).2 h2 ha⟩
  exact ⟨IsLocalRing.ResidueField.map φ, fun x hx => IsLocalRing.ResidueField.map_residue φ _⟩

theorem exists_frob_pow (k : Type) [Field k] (p : ℕ) [Fact p.Prime] [Algebra (ZMod p) k] (σ : k →+* k)
    (x : k) (hx : IsAlgebraic (ZMod p) x) : ∃ i : ℕ, σ x = x ^ p ^ i := by
  let L := IntermediateField.adjoin (ZMod p) {x}
  haveI : FiniteDimensional (ZMod p) L := IntermediateField.adjoin.finiteDimensional hx.isIntegral
  haveI : Finite L := Module.finite_of_finite (ZMod p)
  let τ : k →ₐ[ZMod p] k :=
    { σ with commutes' := fun r => RingHom.congr_fun (Subsingleton.elim (σ.comp (algebraMap (ZMod p) k)) (algebraMap (ZMod p) k)) r }
  obtain ⟨⟨i, hi⟩, h⟩ := (FiniteField.bijective_frobeniusAlgHom_pow (ZMod p) L).2 (τ.restrictNormal L)
  refine ⟨i, ?_⟩
  have h1 := τ.restrictNormal_commutes L ⟨x, IntermediateField.mem_adjoin_simple_self _ x⟩
  rw [← h] at h1
  simp only [AlgHom.coe_pow, FiniteField.coe_frobeniusAlgHom, pow_iterate, ZMod.card, map_pow] at h1
  exact h1.symm

variable [IsAlgClosure ℚ Ω]

theorem cycZ_toZModPow_of_mem_Dec {l : ℕ} [Fact l.Prime] {n : ℕ} {w : Pl} {B : ValuationSubring Ω}
    (hB : IsPlaceOver B w) (hl : ((l : ℕ) : 𝓞 ℚ) ∉ w.asIdeal) (hdiv : l ^ n ∣ normV w - 1)
    {g : G ℚ Ω} (hg : g ∈ Dec (F := ℚ) B) :
    PadicInt.toZModPow n ((cycZ ℚ Ω l g : ℤ_[l]ˣ) : ℤ_[l]) = 1 := by
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  have : NeZero ((l : ℕ) : Ω) := ⟨Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ n)
  have hN0 : l ^ n ≠ 0 := pow_ne_zero _ (Fact.out : l.Prime).ne_zero
  set m := (((cyclotomicCharacter (Ω) l)
    (MulSemiringAction.toRingAut (G ℚ Ω) (Ω) g)) : ℤ_[l]).toZModPow n |>.val with hm
  have hgζ : g ζ = ζ ^ m := cyclotomicCharacter.spec (L := Ω) l
    (MulSemiringAction.toRingAut (G ℚ Ω) (Ω) g) ζ hζ.pow_eq_one
  have hζB : ζ ∈ B :=
    (B.valuation_le_one_iff _).1 (valuation_eq_one_of_pow_eq_one B hN0 hζ.pow_eq_one).le
  have hp := prime_normV w
  haveI : Fact (normV w).Prime := ⟨hp⟩
  have hlt : B.valuation (g ζ - ζ) < 1 := by
    have hpB : B.valuation ((normV w : ℕ) : Ω) < 1 := by
      have := (hB ((normV w : ℕ) : 𝓞 ℚ)).2 (Ideal.absNorm_mem w.asIdeal)
      simpa using this
    haveI : CharP (IsLocalRing.ResidueField B) (normV w) := by
      refine (CharP.charP_iff_prime_eq_zero hp).2 ?_
      rw [← map_natCast (IsLocalRing.residue B), IsLocalRing.residue_eq_zero_iff, B.valuation_lt_one_iff]
      simpa using hpB
    letI : Algebra (ZMod (normV w)) (IsLocalRing.ResidueField B) := ZMod.algebra _ (normV w)
    obtain ⟨σ, hσ⟩ := exists_residue_hom B hg
    have hζp : ζ ^ normV w = ζ := by
      obtain ⟨k, hk⟩ := hdiv
      have e : normV w = l ^ n * k + 1 := by have := hp.one_lt; omega
      rw [e, pow_succ, pow_mul, hζ.pow_eq_one, one_pow, one_mul]
    have hyp : (IsLocalRing.residue B ⟨ζ, hζB⟩) ^ normV w = IsLocalRing.residue B ⟨ζ, hζB⟩ := by
      rw [← map_pow]
      congr 1
      exact Subtype.ext (by simpa using hζp)
    have ha : IsAlgebraic (ZMod (normV w)) (IsLocalRing.residue B ⟨ζ, hζB⟩) :=
      ⟨Polynomial.X ^ normV w - Polynomial.X, FiniteField.X_pow_card_sub_X_ne_zero _ hp.one_lt,
        by simp [hyp]⟩
    obtain ⟨i, hi⟩ := exists_frob_pow _ (normV w) σ _ ha
    have hfix : σ (IsLocalRing.residue B ⟨ζ, hζB⟩) = IsLocalRing.residue B ⟨ζ, hζB⟩ := by
      rw [hi]
      clear hi
      induction i with
      | zero => simp
      | succ i ih => rw [pow_succ, pow_mul, ih, hyp]
    rw [hσ] at hfix
    have := sub_eq_zero.2 hfix
    rw [← map_sub, IsLocalRing.residue_eq_zero_iff, B.valuation_lt_one_iff] at this
    exact this
  rw [hgζ] at hlt
  have heq : ζ ^ m = ζ ^ 1 := by
    refine eq_of_pow_eq_one B (not_valuation_lt_one_of_isPlaceOver hl hB n) ?_ ?_ (by simpa using hlt)
    · rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
    · rw [pow_one, hζ.pow_eq_one]
  have heq' : (hζ.isUnit hN0).unit ^ m = (hζ.isUnit hN0).unit ^ 1 := Units.ext (by simpa using heq)
  have hu : IsPrimitiveRoot (hζ.isUnit hN0).unit (l ^ n) := IsPrimitiveRoot.coe_units_iff.mp (by simpa using hζ)
  rw [pow_eq_pow_iff_modEq, ← hu.eq_orderOf] at heq'
  show ((cyclotomicCharacter (Ω) l)
    (MulSemiringAction.toRingAut (G ℚ Ω) (Ω) g) : ℤ_[l]).toZModPow n = _
  rw [← ZMod.natCast_zmod_val (((cyclotomicCharacter (Ω) l)
    (MulSemiringAction.toRingAut (G ℚ Ω) (Ω) g) : ℤ_[l]).toZModPow n), ← hm]
  have := (ZMod.natCast_eq_natCast_iff _ _ _).mpr heq'
  simpa using this

theorem kummer_conj_dec {l : ℕ} [Fact l.Prime] {n : ℕ} {w : Pl} {B : ValuationSubring Ω}
    (hB : IsPlaceOver B w) (hl : ((l : ℕ) : 𝓞 ℚ) ∉ w.asIdeal) (a : ℚˣ) {g s : G ℚ Ω}
    (hg1 : PadicInt.toZModPow n ((cycZ ℚ Ω l g : ℤ_[l]ˣ) : ℤ_[l]) = 1) (hs : s ∈ Ine (F := ℚ) B) :
    PadicInt.toZModPow n (GlobalTheory.WeilDeligne.kummer l a (g * s * g⁻¹)) =
      PadicInt.toZModPow n (GlobalTheory.WeilDeligne.kummer l a s) := by
  have h0 := GlobalTheory.WeilDeligne.kummer_mul l a g g⁻¹
  rw [mul_inv_cancel, GlobalTheory.WeilDeligne.kummer_one] at h0
  have hs1 := GlobalTheory.WeilDeligne.cycZ_of_mem_Ine hB hl hs
  have e : GlobalTheory.WeilDeligne.kummer l a (g * s * g⁻¹) =
      (cycZ ℚ Ω l g : ℤ_[l]) * GlobalTheory.WeilDeligne.kummer l a s := by
    rw [mul_assoc, GlobalTheory.WeilDeligne.kummer_mul, GlobalTheory.WeilDeligne.kummer_mul, hs1, Units.val_one, one_mul]
    linear_combination -h0
  rw [e, map_mul, hg1, one_mul]

end GlobalTheory.TameConjInv

namespace GlobalTheory.TameConjInv

theorem conj_invariant : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (n : ℕ) (w : Pl)
    (B : ValuationSubring Ω) (M : Type) [AddCommGroup M] (u : G ℚ Ω → M), IsPlaceOver B w → l ^ n ∣ normV w - 1 →
    1 ≤ n → (∀ x : M, l ^ n • x = 0) → IsLocallyConstant (fun s : Ine (F := ℚ) B => u s) →
    (∀ s ∈ Ine (F := ℚ) B, ∀ t ∈ Ine (F := ℚ) B, u (s * t) = u s + u t) →
    ∀ g ∈ Dec (F := ℚ) B, ∀ s ∈ Ine (F := ℚ) B, u (g * s * g⁻¹) = u s := by
  intro l _ Ω _ _ _ n w B M _ u hB hdiv hn htor hlc hadd g hg s hs
  have hl := not_mem_of_dvd l hn hdiv
  have hlB : ¬ B.valuation (l : Ω) < 1 := by
    have := (hB (l : 𝓞 ℚ)).not.mpr hl
    simpa using this
  set a : ℚˣ := GlobalTheory.WeilDeligne.unifUnit w
  let t : G ℚ Ω → ZMod (l ^ n) := fun x => PadicInt.toZModPow n (GlobalTheory.WeilDeligne.kummer l a x)
  have htlc : IsLocallyConstant t := by
    refine (IsLocallyConstant.iff_isOpen_fiber).2 fun y => ?_
    by_cases hy : ∃ x₀, t x₀ = y
    · obtain ⟨x₀, rfl⟩ := hy
      have e : t ⁻¹' {t x₀} = {τ : G ℚ Ω | τ (GlobalTheory.WeilDeligne.rootOf Ω l (a : ℚ) n) =
          x₀ (GlobalTheory.WeilDeligne.rootOf Ω l (a : ℚ) n)} := by
        ext τ
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq]
        exact GlobalTheory.WeilDeligne.toZModPow_kummer_eq_iff l a τ x₀ n
      rw [e]
      exact isOpen_setOf_apply _ (fun z => z = x₀ (GlobalTheory.WeilDeligne.rootOf Ω l (a : ℚ) n))
    · have e : t ⁻¹' {y} = ∅ := by
        ext τ
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
        exact fun h => hy ⟨τ, h⟩
      rw [e]; exact isOpen_empty
  have htadd : ∀ s ∈ Ine (F := ℚ) B, ∀ s' ∈ Ine (F := ℚ) B, t (s * s') = t s + t s' := by
    intro s hs s' _
    simp only [t]
    rw [GlobalTheory.WeilDeligne.kummer_mul, GlobalTheory.WeilDeligne.cycZ_of_mem_Ine hB hl hs, Units.val_one, one_mul, map_add]
  let F : G ℚ Ω → M × ZMod (l ^ n) := fun x => (u x, t x)
  have hFlc : IsLocallyConstant (fun s : Ine (F := ℚ) B => F s) :=
    IsLocallyConstant.prodMk hlc (htlc.comp_continuous continuous_subtype_val)
  have hFadd : ∀ s ∈ Ine (F := ℚ) B, ∀ s' ∈ Ine (F := ℚ) B, F (s * s') = F s + F s' := by
    intro s hs s' hs'
    exact Prod.ext (hadd s hs s' hs') (htadd s hs s' hs')
  have hFtor : ∀ x : M × ZMod (l ^ n), l ^ n • x = 0 := by
    intro x
    refine Prod.ext (htor x.1) ?_
    simp [nsmul_eq_mul]
  have hFw : ∀ σ : G ℚ Ω, (∀ y : Ω, y ≠ 0 → B.valuation (σ y / y - 1) < 1) → F σ = 0 :=
    eq_zero_of_wild l n B hlB F hFtor hFlc hFadd
  obtain ⟨γ, hγ⟩ := GlobalTheory.TameInertiaGen.exists_tameGenAt ℚ Ω w B hB

  obtain ⟨τ, hτ⟩ := (GlobalTheory.WeilDeligne.isTameChar_tameL hB hl).2 (Multiplicative.ofAdd 1)
  have htτ : t τ = 1 := by
    have : GlobalTheory.WeilDeligne.kummer l a (τ : G ℚ Ω) = 1 := by
      have := congrArg Multiplicative.toAdd hτ
      simpa [GlobalTheory.WeilDeligne.tameL] using this
    simp only [t, this, map_one]
  obtain ⟨k₀, hk₀⟩ := exists_zsmul B hγ F hFlc hFadd hFw τ τ.2
  have hunit : IsUnit (t γ) := by
    have h2 := congrArg Prod.snd hk₀
    simp only [F, Prod.smul_snd, htτ, zsmul_eq_mul] at h2
    exact isUnit_iff_exists_inv.2 ⟨(k₀ : ZMod (l ^ n)), by rw [mul_comm]; exact h2.symm⟩
  have hgs : g * s * g⁻¹ ∈ Ine (F := ℚ) B := conj_mem_Ine hg hs
  obtain ⟨k₁, hk₁⟩ := exists_zsmul B hγ F hFlc hFadd hFw s hs
  obtain ⟨k₂, hk₂⟩ := exists_zsmul B hγ F hFlc hFadd hFw _ hgs
  have hteq : t (g * s * g⁻¹) = t s :=
    kummer_conj_dec hB hl a (cycZ_toZModPow_of_mem_Dec hB hl hdiv hg) hs
  have hk : ((k₂ - k₁ : ℤ) : ZMod (l ^ n)) = 0 := by
    have h1 := congrArg Prod.snd hk₁
    have h2 := congrArg Prod.snd hk₂
    simp only [F, Prod.smul_snd, zsmul_eq_mul] at h1 h2
    rw [hteq, h1] at h2
    have h3 : ((k₂ - k₁ : ℤ) : ZMod (l ^ n)) * t γ = 0 := by
      push_cast; rw [sub_mul, h2, sub_self]
    exact (hunit.mul_left_eq_zero).1 h3
  obtain ⟨j, hj⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 hk
  have h1 := congrArg Prod.fst hk₁
  have h2 := congrArg Prod.fst hk₂
  simp only [F, Prod.smul_fst] at h1 h2
  have hl0 : ((l ^ n : ℕ) : ℤ) • u γ = 0 := by rw [natCast_zsmul]; exact htor _
  have hz : (k₂ - k₁) • u γ = 0 := by
    rw [hj, mul_comm, ← smul_smul, hl0, smul_zero]
  rw [h2, h1, ← sub_eq_zero, ← sub_smul, hz]

end GlobalTheory.TameConjInv
