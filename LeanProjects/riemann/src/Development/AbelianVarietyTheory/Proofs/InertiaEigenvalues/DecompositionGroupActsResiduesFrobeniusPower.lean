import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPowCharPowEqSelf
open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne

noncomputable section

namespace GlobalTheory.DecFrobPow

theorem frob_pow_apply {F R : Type} [Field F] [Fintype F] [CommRing R] [Algebra F R] (n : ℕ) (x : R) :
    ((FiniteField.frobeniusAlgHom F R) ^ n) x = x ^ (Fintype.card F ^ n) := by
  rw [AlgHom.coe_pow, FiniteField.coe_frobeniusAlgHom, pow_iterate]

theorem exists_pow_of_algHom {k F : Type} [Field k] [Field F] [Fintype F] [Algebra F k]
    (τ : k →ₐ[F] k) {a : ℕ} (ha : 0 < a) :
    ∃ j : ℕ, ∀ x : k, x ^ (Fintype.card F ^ a) = x → τ x = x ^ (Fintype.card F ^ j) := by
  set q := Fintype.card F with hq
  let S : Subalgebra F k := AlgHom.equalizer ((FiniteField.frobeniusAlgHom F k) ^ a) (AlgHom.id F k)
  have hS : ∀ x, x ∈ S ↔ x ^ (q ^ a) = x := by
    intro x
    show ((FiniteField.frobeniusAlgHom F k) ^ a) x = (AlgHom.id F k) x ↔ _
    rw [frob_pow_apply]; rfl
  let L : IntermediateField F k := S.toIntermediateField (fun x hx => by
    rw [hS] at hx ⊢; rw [inv_pow, hx])
  have hL : ∀ x, x ∈ L ↔ x ^ (q ^ a) = x := hS
  have hq1 : 1 < q := Fintype.one_lt_card
  have hfin : (L : Set k).Finite := by
    have hP : (X ^ q ^ a - X : k[X]) ≠ 0 := FiniteField.X_pow_card_pow_sub_X_ne_zero k ha.ne' hq1
    refine (Polynomial.finite_setOfPred_isRoot hP).subset fun x hx => ?_
    have := (hL x).mp hx
    simp [Polynomial.IsRoot, this]
  haveI : Finite L := hfin.to_subtype
  let σ : L →ₐ[F] L := (τ.comp L.val).codRestrict L.toSubalgebra fun x => by
    show τ (x : k) ∈ L
    rw [hL, ← map_pow, (hL x).mp x.2]
  obtain ⟨n, hn⟩ := (FiniteField.bijective_frobeniusAlgHom_pow F L).2 σ
  refine ⟨n, fun x hx => ?_⟩
  have h1 := congrArg (fun f : L →ₐ[F] L => ((f ⟨x, (hL x).mpr hx⟩ : L) : k)) hn
  simp only [frob_pow_apply] at h1
  have h2 : ((σ ⟨x, (hL x).mpr hx⟩ : L) : k) = τ x := rfl
  rw [← h2, ← h1, SubmonoidClass.coe_pow]

end GlobalTheory.DecFrobPow

namespace GlobalTheory.DecFrobPow

theorem exists_place {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω]
    (A : ValuationSubring Ω) {p : ℕ} (hp : p.Prime) (hpA : A.valuation (p : Ω) < 1) :
    ∃ wK : HeightOneSpectrum (𝓞 K), IsPlaceOver A wK := by
  let g : 𝓞 K →+* A := ((algebraMap K Ω).comp (algebraMap (𝓞 K) K)).codRestrict A fun x =>
    ReciprocityTheory.Gal.mem_of_isIntegral_int A (x.2.algebraMap (B := Ω))
  let P : Ideal (𝓞 K) := (IsLocalRing.maximalIdeal A).comap g
  have hmem : ∀ x : 𝓞 K, x ∈ P ↔ A.valuation (algebraMap K Ω (x : K)) < 1 := fun x =>
    A.valuation_lt_one_iff (g x)
  have hne : P ≠ ⊥ := by
    intro h0
    have hpP : ((p : ℕ) : 𝓞 K) ∈ P := by
      rw [hmem]; simpa using hpA
    rw [h0, Ideal.mem_bot] at hpP
    exact hp.ne_zero (by exact_mod_cast hpP)
  exact ⟨⟨P, Ideal.comap_isPrime g _, hne⟩, fun x => (hmem x).symm⟩

theorem exists_pow_cong_of_mem {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω]
    [IsAlgClosure K Ω] (A : ValuationSubring Ω) {p : ℕ} (hp : p.Prime) (hpA : A.valuation (p : Ω) < 1) :
    ∃ c : ℕ, 0 < c ∧ ∀ z : K, A.valuation (algebraMap K Ω z) ≤ 1 →
      A.valuation ((algebraMap K Ω z) ^ (p ^ c) - algebraMap K Ω z) < 1 := by
  obtain ⟨wK, hwK⟩ := exists_place (K := K) A hp hpA
  obtain ⟨φ, hφD, hφ⟩ := exists_isFrob (F := K) hwK
  obtain ⟨p', c, hp', hc, hN, hp'A⟩ := GlobalTheory.FrobTeich.exists_prime_pow_normV A wK hwK
  have hchar : ∀ r : ℕ, r.Prime → A.valuation (r : Ω) < 1 → CharP (IsLocalRing.ResidueField A) r := by
    intro r hr hrA
    refine (CharP.charP_iff_prime_eq_zero hr).2 ?_
    rw [← map_natCast (IsLocalRing.residue A), IsLocalRing.residue_eq_zero_iff,
      A.valuation_lt_one_iff]
    simpa using hrA
  have hpp : p' = p := by
    haveI := hchar p hp hpA
    haveI := hchar p' hp' hp'A
    exact CharP.eq (IsLocalRing.ResidueField A) ‹CharP _ p'› ‹CharP _ p›
  subst hpp
  refine ⟨c, hc, fun z hz => ?_⟩
  have h1 := hφ _ hz
  rw [hN, φ.commutes] at h1
  rw [← Valuation.map_neg, neg_sub]
  exact h1

end GlobalTheory.DecFrobPow

namespace GlobalTheory.DecFrobPow

theorem pow_pow_eq_self {R : Type} [Monoid R] {r : R} {M : ℕ} (h : r ^ M = r) (b : ℕ) :
    r ^ (M ^ b) = r := by
  induction b with
  | zero => simp
  | succ b ih => rw [pow_succ, pow_mul, ih, h]

theorem exists_field_cong_pow : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (_h : IsPlaceOver A w),
    ∀ d ∈ Dec (F := E) A, ∀ y : Ω, ∃ K : IntermediateField E Ω, FiniteDimensional E K ∧ y ∈ K ∧
      ∃ j : ℕ, ∀ z ∈ K, A.valuation z ≤ 1 → A.valuation (d z - z ^ (normV w ^ j)) < 1 := by
  intro E Ω _ _ _ _ _ A w h d hd y
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective
  haveI : Algebra.IsAlgebraic E Ω := IsAlgClosure.isAlgebraic
  set K := IntermediateField.adjoin E ({y} : Set Ω) with hK
  haveI hKfin : FiniteDimensional E K :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral y)
  haveI : FiniteDimensional ℚ K := Module.Finite.trans E K
  haveI : NumberField K := ⟨⟩
  haveI : IsAlgClosure K Ω := ⟨IsAlgClosure.isAlgClosed E, Algebra.IsAlgebraic.tower_top (K := E) K⟩
  refine ⟨K, hKfin, IntermediateField.mem_adjoin_simple_self E y, ?_⟩
  obtain ⟨p, b, hp, hb, hq, hpA⟩ := GlobalTheory.FrobTeich.exists_prime_pow_normV A w h
  obtain ⟨c, hc, hcK⟩ := exists_pow_cong_of_mem (K := K) A hp hpA
  haveI : w.asIdeal.IsMaximal := w.isMaximal
  letI : Field (𝓞 E ⧸ w.asIdeal) := Ideal.Quotient.field _
  haveI : Finite (𝓞 E ⧸ w.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ w.ne_bot
  letI : Fintype (𝓞 E ⧸ w.asIdeal) := Fintype.ofFinite _
  have hcard : Fintype.card (𝓞 E ⧸ w.asIdeal) = normV w := Fintype.card_eq_nat_card
  let gE : 𝓞 E →+* A := ((algebraMap E Ω).comp (algebraMap (𝓞 E) E)).codRestrict A fun x =>
    ReciprocityTheory.Gal.mem_of_isIntegral_int A (x.2.algebraMap (B := Ω))
  let ι : 𝓞 E ⧸ w.asIdeal →+* IsLocalRing.ResidueField A :=
    Ideal.Quotient.lift w.asIdeal ((IsLocalRing.residue A).comp gE) (fun x hx => by
      show IsLocalRing.residue A (gE x) = 0
      rw [IsLocalRing.residue_eq_zero_iff, A.valuation_lt_one_iff]
      exact (h x).mpr hx)
  letI : Algebra (𝓞 E ⧸ w.asIdeal) (IsLocalRing.ResidueField A) := ι.toAlgebra
  let D : A.decompositionSubgroup E := ⟨d, hd⟩
  let τ0 : IsLocalRing.ResidueField A →+* IsLocalRing.ResidueField A :=
    MulSemiringAction.toRingHom (A.decompositionSubgroup E) (IsLocalRing.ResidueField A) D
  have hτ0 : ∀ a : A, τ0 (IsLocalRing.residue A a) = IsLocalRing.residue A (D • a) := fun a =>
    (IsLocalRing.ResidueField.residue_smul (g := D) (r := a)).symm
  have hval : ∀ a : A, ((D • a : A) : Ω) = d a := fun a => rfl
  let τ : IsLocalRing.ResidueField A →ₐ[𝓞 E ⧸ w.asIdeal] IsLocalRing.ResidueField A :=
    { τ0 with
      commutes' := fun c => by
        obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective c
        show τ0 (ι (Ideal.Quotient.mk _ x)) = ι (Ideal.Quotient.mk _ x)
        have e1 : ι (Ideal.Quotient.mk _ x) = IsLocalRing.residue A (gE x) := Ideal.Quotient.lift_mk _ _ _
        rw [e1, hτ0]
        congr 1
        apply Subtype.ext
        rw [hval]
        exact d.commutes _ }
  obtain ⟨j, hj⟩ := exists_pow_of_algHom τ hc
  rw [hcard] at hj
  refine ⟨j, fun z hzK hz => ?_⟩
  let a : A := ⟨z, (A.valuation_le_one_iff z).mp hz⟩
  have h1 : A.valuation (z ^ (p ^ c) - z) < 1 := hcK ⟨z, hzK⟩ hz
  have h2 : IsLocalRing.residue A a ^ (p ^ c) = IsLocalRing.residue A a := by
    rw [← sub_eq_zero, ← map_pow, ← map_sub, IsLocalRing.residue_eq_zero_iff,
      A.valuation_lt_one_iff]
    exact h1
  have h3 : IsLocalRing.residue A a ^ (normV w ^ c) = IsLocalRing.residue A a := by
    rw [hq, ← pow_mul, mul_comm, pow_mul]
    exact pow_pow_eq_self h2 b
  have h4 := hj _ h3
  have h5 : τ (IsLocalRing.residue A a) = IsLocalRing.residue A (D • a) := hτ0 a
  rw [h5, ← sub_eq_zero, ← map_pow, ← map_sub, IsLocalRing.residue_eq_zero_iff,
    A.valuation_lt_one_iff] at h4
  exact h4

end GlobalTheory.DecFrobPow
