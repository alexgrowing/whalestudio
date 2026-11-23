import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.DataTheta
import Formalism.SharpRestriction.ParConsts
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.Decomp
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.DiscriminantRealSubfield
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.DiscrB
import Lemmata.GeneralBFactRightVariant.Imports

noncomputable section

namespace Formalism.MainNotions.KudlaSiegelWeil

open NumberField IsDedekindDomain MeasureTheory
open Formalism.BasicNotions (D7 ThetaX)
open Formalism.BasicNotions.TH (tauE)
open scoped Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

abbrev HS (D : D7) : Type 1 := Formalism.BasicNotions.TH.HSp D

abbrev FF (D : D7) : Type := ↥D.host.F

abbrev FinF (D : D7) : Type := HeightOneSpectrum (𝓞 (FF D))

abbrev FinE (D : D7) : Type := HeightOneSpectrum (𝓞 D.host.E)

abbrev FI (D : D7) : Type := FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E

abbrev Pl (D : D7) : Type := FinF D ⊕ D.what₂.Tau

def Over (D : D7) (w : FinE D) (v : FinF D) : Prop :=
  w.asIdeal.comap (algebraMap (𝓞 (FF D)) (𝓞 D.host.E)) = v.asIdeal

def Split (D : D7) (v : FinF D) : Prop :=
  ∃ w w' : FinE D, w ≠ w' ∧ Over D w v ∧ Over D w' v

def SplitsCompletely (D : D7) (ℓ : ℕ) : Prop :=
  Nat.card {P : FinE D // ((ℓ : ℤ) : 𝓞 D.host.E) ∈ P.asIdeal} = Module.finrank ℚ D.host.E

def InertPlaceConditions (D : D7) : Prop :=
  ∀ v : FinF D, ¬ Split D v →
    (2 : 𝓞 (FF D)) ∉ v.asIdeal ∧ 3 < Ideal.absNorm v.asIdeal ∧
    ¬ differentIdeal ℤ (𝓞 (FF D)) ≤ v.asIdeal ∧
    ∀ w : FinE D, Over D w v → w.valuation D.host.E D.host.xi0 = 1

namespace InertConditionsOfHost

open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition
open scoped Pointwise

section

variable {L : Type} [Field L]

def thP (ζ : L) (m : ℕ) : L := ζ ^ (2 ^ m) + (ζ ^ (2 ^ m))⁻¹

theorem pow_two_pow_add_inv_succ (ζ : L) (hζ : ζ ≠ 0) (m : ℕ) : thP ζ (m + 1) = thP ζ m ^ 2 - 2 := by
  unfold thP
  have h : ζ ^ (2 ^ m) ≠ 0 := pow_ne_zero _ hζ
  rw [pow_succ 2 m, pow_mul]
  field_simp
  ring

theorem pow_two_pow_add_inv_mem_adjoin [Algebra ℚ L] (ζ : L) (hζ : ζ ≠ 0) (m : ℕ) : thP ζ m ∈ F1 ζ := by
  induction m with
  | zero => simpa [thP, F1] using IntermediateField.mem_adjoin_simple_self ℚ (ζ + ζ⁻¹)
  | succ m ih =>
    rw [pow_two_pow_add_inv_succ ζ hζ]
    exact sub_mem (pow_mem ih 2) (by exact_mod_cast (F1 ζ).natCast_mem 2)

theorem pow_two_pow_add_inv_sq_eq_two [CharZero L] (ζ : L) (e : ℕ) (he : 1 ≤ e) (h : IsPrimitiveRoot ζ (2 ^ (e + 2))) :
    thP ζ (e - 1) ^ 2 = 2 := by
  have hζ : ζ ≠ 0 := h.ne_zero (by positivity)
  have h1 : ζ ^ (2 ^ (e + 1)) = -1 := by
    have hsq : (ζ ^ (2 ^ (e + 1))) ^ 2 = 1 := by
      rw [← pow_mul, ← pow_succ]; exact h.pow_eq_one
    have hne : ζ ^ (2 ^ (e + 1)) ≠ 1 := by
      intro h0
      have := h.dvd_of_pow_eq_one _ h0
      have h2 : 2 ^ (e + 2) ≤ 2 ^ (e + 1) := Nat.le_of_dvd (by positivity) this
      have h3 : 2 ^ (e + 1) < 2 ^ (e + 2) := Nat.pow_lt_pow_right (by norm_num) (by omega)
      omega
    rcases mul_self_eq_one_iff.mp ((sq _).symm.trans hsq) with h | h
    · exact absurd h hne
    · exact h
  have h2 : thP ζ (e + 1) = -2 := by
    unfold thP; rw [h1]; norm_num
  have h3 : thP ζ e ^ 2 = 0 := by
    have := pow_two_pow_add_inv_succ ζ hζ e
    rw [h2] at this; linear_combination -this
  have h4 : thP ζ e = 0 := by simpa using h3
  have h5 := pow_two_pow_add_inv_succ ζ hζ (e - 1)
  rw [Nat.sub_add_cancel he, h4] at h5
  linear_combination -h5

end

private theorem cycRat (m : ℕ) : IsCyclotomicExtension {m} ℚ (CyclotomicField m ℚ) := by
  convert (inferInstance : @IsCyclotomicExtension {m} ℚ (CyclotomicField m ℚ) _ _ (CyclotomicField.algebra m ℚ))
  exact Subsingleton.elim _ _

private theorem fix_or_inv {φ : Formalism.HC.Frame} (H : Formalism.HC.HostRaw φ)
    (τ : CyclotomicField H.condN ℚ ≃ₐ[ℚ] CyclotomicField H.condN ℚ) (hτ : ∀ x, τ (H.cycEmb x) = H.cycEmb x)
    (ζ : CyclotomicField H.condN ℚ) (hζ : ζ ^ 2 ^ (φ.e + 2) = 1) : τ ζ = ζ ∨ τ ζ = ζ⁻¹ := by
  have : NeZero H.condN := ⟨by have := H.QS_pos; have := H.hyp.1.pos; have := H.hyp.2.1.pos; positivity⟩
  have := cycRat H.condN
  have hdvd : 2 ^ (φ.e + 2) ∣ H.condN := (H.tower_dvd.mul_right _).mul_right _
  have hroot := IsCyclotomicExtension.Rat.galEquivZMod_apply_of_pow_eq H.condN (CyclotomicField H.condN ℚ) τ
    (x := ζ) (orderOf_dvd_iff_pow_eq_one.1 ((orderOf_dvd_iff_pow_eq_one.2 hζ).trans hdvd))
  have hz := IsCyclotomicExtension.Rat.galEquivZMod_apply_of_pow_eq H.condN (CyclotomicField H.condN ℚ) τ
    (x := H.cycZeta) H.cycZeta_prim.pow_eq_one
  set u := IsCyclotomicExtension.Rat.galEquivZMod H.condN (CyclotomicField H.condN ℚ) τ
  have h1 : H.art u = 1 := by
    rw [← H.gal.symm.map_eq_one_iff]
    exact AlgEquiv.ext fun x => H.cycEmb.injective ((H.art_spec u τ hz x).trans (hτ x))
  have hv : ((ZMod.unitsMap hdvd u : (ZMod (2 ^ (φ.e + 2)))ˣ) : ZMod (2 ^ (φ.e + 2))) =
      (((u : ZMod H.condN).val : ℕ) : ZMod (2 ^ (φ.e + 2))) := by
    rw [ZMod.unitsMap_val, ZMod.cast_eq_val]
  have h2 := H.art_h u _ hv
  rw [h1, Prod.snd_one, map_one] at h2
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp ((QuotientGroup.eq_one_iff _).mp h2.symm)
  rw [← hk] at hv
  rw [hroot]
  rcases Int.even_or_odd k with h3 | h3
  · left
    rw [h3.neg_one_zpow, Units.val_one, ← Nat.cast_one, ZMod.natCast_eq_natCast_iff] at hv
    rw [← pow_eq_pow_of_modEq hv hζ, pow_one]
  · right
    rw [h3.neg_one_zpow] at hv
    have h4 : (((u : ZMod H.condN).val + 1 : ℕ) : ZMod (2 ^ (φ.e + 2))) = 0 := by
      rw [Nat.cast_add, ← hv]; simp
    obtain ⟨m, hm⟩ := (ZMod.natCast_eq_zero_iff _ _).1 h4
    apply eq_inv_of_mul_eq_one_left
    rw [← pow_succ, hm, pow_mul, hζ, one_pow]

private theorem exists_sqrt_two_E {φ : Formalism.HC.Frame} (H : Formalism.HC.HostRaw φ) : ∃ s : H.E, s ^ 2 = 2 := by
  have hN : H.condN ≠ 0 := by have := H.QS_pos; have := H.hyp.1.pos; have := H.hyp.2.1.pos; positivity
  have : NeZero H.condN := ⟨hN⟩
  have := cycRat H.condN
  have : IsGalois ℚ (CyclotomicField H.condN ℚ) := IsCyclotomicExtension.isGalois {H.condN} ℚ _
  obtain ⟨k, hk⟩ : 2 ^ (φ.e + 2) ∣ H.condN := (H.tower_dvd.mul_right _).mul_right _
  have hζ : IsPrimitiveRoot (H.cycZeta ^ k) (2 ^ (φ.e + 2)) :=
    H.cycZeta_prim.pow (Nat.pos_of_ne_zero hN) (hk.trans (mul_comm _ _))
  have he : 1 ≤ φ.e := le_trans (by norm_num) H.two_le_e
  have h2 := pow_two_pow_add_inv_sq_eq_two _ _ he hζ
  let _ : Algebra H.E (CyclotomicField H.condN ℚ) := H.cycEmb.toRingHom.toAlgebra
  have : IsScalarTower ℚ H.E (CyclotomicField H.condN ℚ) :=
    IsScalarTower.of_algebraMap_eq fun x => (H.cycEmb.commutes x).symm
  have : IsGalois H.E (CyclotomicField H.condN ℚ) := IsGalois.tower_top_of_isGalois ℚ H.E _
  have : FiniteDimensional H.E (CyclotomicField H.condN ℚ) := Module.Finite.of_restrictScalars_finite ℚ _ _
  obtain ⟨s, hs⟩ := (IsGalois.mem_range_algebraMap_iff_fixed (F := H.E) (thP (H.cycZeta ^ k) (φ.e - 1))).2 (by
    intro τ
    have h3 : τ (H.cycZeta ^ k) = H.cycZeta ^ k ∨ τ (H.cycZeta ^ k) = (H.cycZeta ^ k)⁻¹ :=
      fix_or_inv H (τ.restrictScalars ℚ) (fun x => τ.commutes x) _ hζ.pow_eq_one
    generalize H.cycZeta ^ k = z at h3 ⊢
    rw [thP, map_add, map_inv₀, map_pow]
    rcases h3 with h | h
    · rw [h]
    · rw [h, inv_pow, inv_inv, add_comm])
  refine ⟨s, (algebraMap H.E (CyclotomicField H.condN ℚ)).injective ?_⟩
  rw [map_pow, map_ofNat, hs, h2]

theorem exists_sqrt_two (D : D7) : ∃ s : 𝓞 (FF D), s ^ 2 = 2 := by
  obtain ⟨t, htE⟩ := exists_sqrt_two_E D.host.toHostRaw
  have hF : t ∈ D.host.F := by
    rw [mem_maximalRealSubfield_iff]
    intro ψ
    have h1 : (ψ t) ^ 2 = ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 := by
      rw [← map_pow, htE, map_ofNat, ← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; rfl
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 h1 with h | h <;> rw [h] <;> simp
  have htF : (⟨t, hF⟩ : FF D) ^ 2 = 2 := by
    apply D.host.F.subtype.injective
    rw [map_pow, map_ofNat]; exact htE
  have hint : IsIntegral ℤ (⟨t, hF⟩ : FF D) :=
    ⟨Polynomial.X ^ 2 - 2, by monicity!, by simp [htF]⟩
  refine ⟨IsIntegralClosure.mk' (𝓞 (FF D)) _ hint, ?_⟩
  apply RingOfIntegers.coe_injective
  rw [map_pow, map_ofNat, IsIntegralClosure.algebraMap_mk']; exact htF

theorem three_lt_absNorm (D : D7) (v : FinF D) (h2 : (2 : 𝓞 (FF D)) ∉ v.asIdeal) :
    3 < Ideal.absNorm v.asIdeal := by
  by_contra hle
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
  have h1 : Ideal.absNorm v.asIdeal ≠ 1 := by rw [Ne, Ideal.absNorm_eq_one_iff]; exact v.isPrime.ne_top
  have hm := Ideal.absNorm_mem v.asIdeal
  have h2' : Ideal.absNorm v.asIdeal ≠ 2 := by
    intro h; rw [h] at hm; exact h2 (by exact_mod_cast hm)
  have h3 : Ideal.absNorm v.asIdeal = 3 := by omega
  rw [h3] at hm
  obtain ⟨s, hs⟩ := exists_sqrt_two D
  have hcard : Nat.card (𝓞 (FF D) ⧸ v.asIdeal) = 3 := by
    rw [← h3, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have : v.asIdeal.IsMaximal := v.isMaximal
  let _ := Ideal.Quotient.field v.asIdeal
  have : Finite (𝓞 (FF D) ⧸ v.asIdeal) := Nat.finite_of_card_ne_zero (by omega)
  let _ := Fintype.ofFinite (𝓞 (FF D) ⧸ v.asIdeal)
  have hx3 := FiniteField.pow_card (Ideal.Quotient.mk v.asIdeal s)
  rw [← Nat.card_eq_fintype_card, hcard] at hx3
  have hx2 : (Ideal.Quotient.mk v.asIdeal s) ^ 2 = 2 := by
    rw [← map_pow, hs, map_ofNat]
  have h3K : (3 : 𝓞 (FF D) ⧸ v.asIdeal) = 0 := by
    have := Ideal.Quotient.eq_zero_iff_mem.mpr hm
    rw [Nat.cast_ofNat, map_ofNat] at this
    exact this
  have hx0 : Ideal.Quotient.mk v.asIdeal s = 0 := by
    linear_combination hx3 - (Ideal.Quotient.mk v.asIdeal s) * hx2
  have : (1 : 𝓞 (FF D) ⧸ v.asIdeal) = 0 := by
    linear_combination h3K + hx2 - (Ideal.Quotient.mk v.asIdeal s) * hx0
  exact one_ne_zero this

theorem conj_conj (D : D7) (x : D.host.E) : D.host.conj (D.host.conj x) = x := by
  apply D.host.φ₀.injective
  rw [D.host.conjE_apply, D.host.conjE_apply]
  simp

theorem conj_b (D : D7) : D.host.conj (D.host.sqd) = -D.host.sqd := by
  rw [D.host.galE_bE, D.host.galE_conjE]
  simp [Formalism.HC.Frame.cc, c0]

theorem b_sq (D : D7) : D.host.sqd ^ 2 = -(D.host.d : D.host.E) := D.host.sqd_sq

def sgO (D : D7) : 𝓞 D.host.E →+* 𝓞 D.host.E := RingOfIntegers.mapRingHom D.host.conj

theorem sgO_coe (D : D7) (x : 𝓞 D.host.E) : ((sgO D x : 𝓞 D.host.E) : D.host.E) = D.host.conj (x : D.host.E) := rfl

theorem sgO_sgO (D : D7) (x : 𝓞 D.host.E) : sgO D (sgO D x) = x := by
  apply RingOfIntegers.ext; rw [sgO_coe, sgO_coe, conj_conj]

theorem sgO_F (D : D7) (x : 𝓞 (FF D)) :
    sgO D (algebraMap (𝓞 (FF D)) (𝓞 D.host.E) x) = algebraMap (𝓞 (FF D)) (𝓞 D.host.E) x := by
  apply RingOfIntegers.ext; rw [sgO_coe]
  exact (D.host.conjE_mem_hostF_iff (x : FF D).1).1 (x : FF D).2

theorem algFE_inj (D : D7) : Function.Injective (algebraMap (𝓞 (FF D)) (𝓞 D.host.E)) :=
  FaithfulSMul.algebraMap_injective _ _

theorem exists_over (D : D7) (v : FinF D) : ∃ w : FinE D, Over D w v := by
  obtain ⟨Q, -, hQp, hQ⟩ := Ideal.exists_ideal_over_prime_of_isIntegral v.asIdeal
    (⊥ : Ideal (𝓞 D.host.E)) (by rw [Ideal.comap_bot_of_injective _ (algFE_inj D)]; exact bot_le)
  have hQne : Q ≠ ⊥ := by
    intro h; rw [h, Ideal.comap_bot_of_injective _ (algFE_inj D)] at hQ; exact v.ne_bot hQ.symm
  exact ⟨⟨Q, hQp, hQne⟩, hQ⟩

theorem fixed_of_not_split (D : D7) (v : FinF D) (hv : ¬ Split D v) (w : FinE D) (hw : Over D w v) :
    w.asIdeal.comap (sgO D) = w.asIdeal := by
  by_contra hne
  apply hv
  have hne' : w.asIdeal.comap (sgO D) ≠ ⊥ := by
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot w.ne_bot
    intro h
    have h1 : sgO D x ∈ w.asIdeal.comap (sgO D) := by rw [Ideal.mem_comap, sgO_sgO]; exact hx
    rw [h, Ideal.mem_bot] at h1
    apply hx0; rw [← sgO_sgO D x, h1, map_zero]
  have := w.isPrime
  refine ⟨w, ⟨w.asIdeal.comap (sgO D), Ideal.comap_isPrime (sgO D) w.asIdeal, hne'⟩, ?_, hw, ?_⟩
  · intro h
    exact hne (congrArg HeightOneSpectrum.asIdeal h).symm
  · show (w.asIdeal.comap (sgO D)).comap (algebraMap (𝓞 (FF D)) (𝓞 D.host.E)) = v.asIdeal
    rw [Ideal.comap_comap, show (sgO D).comp (algebraMap (𝓞 (FF D)) (𝓞 D.host.E)) = algebraMap _ _ from
      RingHom.ext (sgO_F D)]
    exact hw

theorem one_mem_of_coprime {R : Type*} [CommRing R] (P : Ideal R) {m n : ℕ} (h : Nat.Coprime m n)
    (hm : (m : R) ∈ P) (hn : (n : R) ∈ P) : (1 : R) ∈ P := by
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.mpr h
  have : ((a : R) * m + (b : R) * n) = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → R) hab
  rw [← this]
  exact P.add_mem (P.mul_mem_left _ hm) (P.mul_mem_left _ hn)

theorem exists_prime_mem {R : Type*} [CommRing R] (P : Ideal R) [hP : P.IsPrime] (n : ℕ) :
    n ≠ 0 → (n : R) ∈ P → ∃ p : ℕ, p.Prime ∧ p ∣ n ∧ (p : R) ∈ P := by
  first | exact Bl.general_b_fact_right_variant.goal1 .. | (apply Bl.general_b_fact_right_variant.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_right_variant.goal1 <;> assumption) | (apply @Bl.general_b_fact_right_variant.goal1 <;> assumption) | (intros; apply @Bl.general_b_fact_right_variant.goal1 <;> assumption) | (apply @Bl.general_b_fact_right_variant.goal1 <;> first | assumption | infer_instance) | exact @Bl.general_b_fact_right_variant.goal1 R ‹_› P hP n ‹_› ‹_› | exact @Bl.general_b_fact_right_variant.goal1 R ‹_› P hP n ‹_› | exact @Bl.general_b_fact_right_variant.goal1 R ‹_› P hP n | exact @Bl.general_b_fact_right_variant.goal1 R ‹_› P hP | exact @Bl.general_b_fact_right_variant.goal1 R ‹_› P | exact @Bl.general_b_fact_right_variant.goal1 R ‹_› | exact @Bl.general_b_fact_right_variant.goal1 R

theorem not_fixed_condN (D : D7) (w : FinE D) (p : ℕ) (hpp : p.Prime) (hp : p ∣ D.host.condN)
    (hpw : (p : 𝓞 D.host.E) ∈ w.asIdeal) : w.asIdeal.comap (sgO D) ≠ w.asIdeal := by
  intro hfix
  have := w.isPrime
  have hlo : w.asIdeal.LiesOver (Ideal.span {(p : ℤ)}) := by
    constructor
    have hmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
      PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hpp).irreducible
    refine hmax.eq_of_le (Ideal.comap_ne_top _ w.isPrime.ne_top) ?_
    rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap]
    simpa using hpw
  apply D.host.der.decompConj p hpp hp w.asIdeal
  rw [MulAction.mem_stabilizer_iff]
  ext x
  rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem]
  have hx : ((D.host.conj)⁻¹ • x : 𝓞 D.host.E) = sgO D x := by
    apply RingOfIntegers.ext
    rw [sgO_coe]
    show (D.host.conj).symm (x : D.host.E) = D.host.conj (x : D.host.E)
    rw [AlgEquiv.symm_apply_eq, conj_conj]
  rw [hx, ← Ideal.mem_comap, hfix]

theorem not_fixed_ram (D : D7) (w : FinE D) (p : ℕ) (hp : p = 2 ∨ p = D.host.q ∨ p = D.host.d)
    (hpw : (p : 𝓞 D.host.E) ∈ w.asIdeal) : w.asIdeal.comap (sgO D) ≠ w.asIdeal := by
  rcases hp with h | h | h <;> subst h
  · exact not_fixed_condN D w 2 Nat.prime_two
      ((((dvd_pow_self 2 (by omega)).trans D.host.tower_dvd).mul_right _).mul_right _) hpw
  · exact not_fixed_condN D w _ D.host.hyp.1 ((dvd_mul_left _ _).mul_right _) hpw
  · exact not_fixed_condN D w _ D.host.hyp.2.1 (dvd_mul_left _ _) hpw

theorem exists_bO (D : D7) : ∃ β : 𝓞 D.host.E,
    algebraMap (𝓞 D.host.E) D.host.E β = D.host.sqd ∧
    β ^ 2 = -(D.host.d : 𝓞 D.host.E) ∧ sgO D β = -β := by
  have hint : IsIntegral ℤ (D.host.sqd) :=
    ⟨Polynomial.X ^ 2 + Polynomial.C (D.host.d : ℤ), by monicity!, by simp [b_sq D]⟩
  have hβ : algebraMap (𝓞 D.host.E) D.host.E (IsIntegralClosure.mk' (𝓞 D.host.E) _ hint) =
      D.host.sqd := IsIntegralClosure.algebraMap_mk' _ _ _
  refine ⟨IsIntegralClosure.mk' (𝓞 D.host.E) _ hint, hβ, ?_, ?_⟩
  · apply RingOfIntegers.coe_injective
    rw [map_pow, map_neg, map_natCast, hβ, b_sq]
  · apply RingOfIntegers.coe_injective
    rw [map_neg, hβ, ← conj_b]
    exact (sgO_coe D _).trans (congrArg D.host.conj hβ)

theorem not_fixed_splitK (D : D7) (w : FinE D) (p : ℕ) (hpp : p.Prime) (hp2 : p ≠ 2)
    (hj : jacobiSym (-(D.host.d : ℤ)) p = 1) (hpw : (p : 𝓞 D.host.E) ∈ w.asIdeal) :
    w.asIdeal.comap (sgO D) ≠ w.asIdeal := by
  intro hfix
  have hone : (1 : 𝓞 D.host.E) ∉ w.asIdeal := fun h => w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h)
  have : Fact p.Prime := ⟨hpp⟩
  rw [← jacobiSym.legendreSym.to_jacobiSym] at hj
  have h0 : ((-(D.host.d : ℤ) : ℤ) : ZMod p) ≠ 0 := by
    intro h; rw [(legendreSym.eq_zero_iff p _).2 h] at hj; exact zero_ne_one hj
  obtain ⟨r, hr⟩ := (legendreSym.eq_one_iff p h0).1 hj
  obtain ⟨x, rfl⟩ := ZMod.intCast_surjective r
  have hdvd : (p : ℤ) ∣ x * x + D.host.d := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast at hr ⊢
    linear_combination -hr
  obtain ⟨m, hm⟩ := hdvd
  obtain ⟨β, hβ, hβ2, hσβ⟩ := exists_bO D
  have hprod : ((x : 𝓞 D.host.E) + β) * ((x : 𝓞 D.host.E) - β) ∈ w.asIdeal := by
    have : ((x : 𝓞 D.host.E) + β) * ((x : 𝓞 D.host.E) - β) = (p : 𝓞 D.host.E) * (m : 𝓞 D.host.E) := by
      have h1 : ((x * x + D.host.d : ℤ) : 𝓞 D.host.E) = ((p * m : ℤ) : 𝓞 D.host.E) := congrArg _ hm
      push_cast at h1
      linear_combination h1 - hβ2
    rw [this]; exact w.asIdeal.mul_mem_right _ hpw
  have hswap : ∀ y, y ∈ w.asIdeal → sgO D y ∈ w.asIdeal := by
    intro y hy; rw [← hfix] at hy; exact hy
  have hσ1 : sgO D ((x : 𝓞 D.host.E) + β) = (x : 𝓞 D.host.E) - β := by
    rw [map_add, map_intCast, hσβ]; ring
  have hσ2 : sgO D ((x : 𝓞 D.host.E) - β) = (x : 𝓞 D.host.E) + β := by
    rw [map_sub, map_intCast, hσβ]; ring
  have hboth : (x : 𝓞 D.host.E) + β ∈ w.asIdeal ∧ (x : 𝓞 D.host.E) - β ∈ w.asIdeal := by
    rcases w.isPrime.mem_or_mem hprod with h | h
    · exact ⟨h, hσ1 ▸ hswap _ h⟩
    · exact ⟨hσ2 ▸ hswap _ h, h⟩
  have h2β : ((2 : ℕ) : 𝓞 D.host.E) * β ∈ w.asIdeal := by
    have : ((2 : ℕ) : 𝓞 D.host.E) * β = ((x : 𝓞 D.host.E) + β) - ((x : 𝓞 D.host.E) - β) := by
      push_cast; ring
    rw [this]; exact w.asIdeal.sub_mem hboth.1 hboth.2
  rcases w.isPrime.mem_or_mem h2β with h | h
  · exact hone (one_mem_of_coprime _ ((Nat.coprime_primes hpp Nat.prime_two).2 hp2) hpw h)
  · have hd : (D.host.d : 𝓞 D.host.E) ∈ w.asIdeal := by
      have : (D.host.d : 𝓞 D.host.E) = -(β * β) := by linear_combination hβ2
      rw [this]; exact w.asIdeal.neg_mem (w.asIdeal.mul_mem_left _ h)
    refine hone (one_mem_of_coprime _ ((Nat.coprime_primes hpp D.host.hyp.2.1).2 ?_) hpw hd)
    intro hpd
    apply h0
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd, hpd]
    exact dvd_neg.2 dvd_rfl

theorem mem_of_over (D : D7) {w : FinE D} {v : FinF D} (hw : Over D w v) (n : ℕ) :
    (n : 𝓞 (FF D)) ∈ v.asIdeal → (n : 𝓞 D.host.E) ∈ w.asIdeal := by
  intro h
  rw [← hw, Ideal.mem_comap, map_natCast] at h
  exact h

theorem val_eq_one (D : D7) (w : FinE D) (x : 𝓞 D.host.E) (hx : x ∉ w.asIdeal) :
    w.valuation D.host.E (algebraMap (𝓞 D.host.E) D.host.E x) = 1 := by
  refine le_antisymm (w.valuation_le_one x) (not_lt.1 ?_)
  rw [HeightOneSpectrum.valuation_lt_one_iff_mem]; exact hx

end InertConditionsOfHost

open InertConditionsOfHost Formalism.FrobeniusOrbits in

theorem inert_conditions_hold (D : D7) : InertPlaceConditions D := by
  intro v hv
  obtain ⟨w0, hw0⟩ := exists_over D v
  have hfix0 := fixed_of_not_split D v hv w0 hw0
  have h2 : (2 : 𝓞 (FF D)) ∉ v.asIdeal := by
    intro h
    exact not_fixed_ram D w0 2 (Or.inl rfl) (mem_of_over D hw0 2 (by exact_mod_cast h)) hfix0
  refine ⟨h2, three_lt_absNorm D v h2, ?_, ?_⟩
  · intro hle
    have hdv : Ideal.absNorm v.asIdeal ∣ (discr (FF D)).natAbs := by
      rw [← absNorm_differentIdeal (K := FF D) (𝒪 := 𝓞 (FF D))]
      exact Ideal.absNorm_dvd_absNorm_of_le hle
    have h0 : Ideal.absNorm v.asIdeal ≠ 0 := by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
    have := v.isPrime
    obtain ⟨p, hpp, hpd, hpv⟩ := exists_prime_mem v.asIdeal _ h0 (Ideal.absNorm_mem v.asIdeal)
    have hp3 : p ∣ D.host.condN := by
      refine D.host.der.discr_primes.1 p hpp ?_
      rw [D.host.der.discr_sq]
      exact (Int.natCast_dvd.2 (hpd.trans hdv)).trans (dvd_pow_self _ two_ne_zero)
    exact not_fixed_condN D w0 p hpp hp3 (mem_of_over D hw0 p hpv) hfix0
  · intro w hw
    have hfix := fixed_of_not_split D v hv w hw
    obtain ⟨β, hβ, hβ2, -⟩ := exists_bO D
    have hβw : β ∉ w.asIdeal := by
      intro h
      have hd : (D.host.d : 𝓞 D.host.E) ∈ w.asIdeal := by
        have : (D.host.d : 𝓞 D.host.E) = -(β * β) := by linear_combination hβ2
        rw [this]; exact w.asIdeal.neg_mem (w.asIdeal.mul_mem_left _ h)
      exact not_fixed_ram D w _ (Or.inr (Or.inr rfl)) hd hfix
    have hNw : ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal := by
      intro h
      have hN0 : Ideal.absNorm D.host.ccK ≠ 0 := by
        rw [Ne, Ideal.absNorm_eq_zero_iff]; exact D.host.ccK_ne_bot
      have := w.isPrime
      obtain ⟨p, hpp, hpd, hpw⟩ := exists_prime_mem w.asIdeal _ hN0 h
      have hp2 : p ≠ 2 := by
        intro h2'
        have hc := D.host.ccK_coprime 2 (by simp)
        rw [h2'] at hpd
        exact absurd (Nat.Coprime.eq_one_of_dvd hc.symm hpd) (by norm_num)
      obtain ⟨P, hP, hPle, hpP⟩ : ∃ P : Ideal (𝓞 D.host.K), P.IsPrime ∧ D.host.ccK ≤ P ∧ p ∣ Ideal.absNorm P := by
        have hfac := Ideal.prod_normalizedFactors_eq_self D.host.ccK_ne_bot
        rw [← hfac, map_multiset_prod] at hpd
        obtain ⟨n, hn, hpn⟩ := (Nat.prime_iff.1 hpp).exists_mem_multiset_dvd hpd
        obtain ⟨P, hPm, rfl⟩ := Multiset.mem_map.1 hn
        exact ⟨P, Ideal.isPrime_of_prime (UniqueFactorizationMonoid.prime_of_normalized_factor P hPm),
          Ideal.le_of_dvd (UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hPm), hpn⟩
      obtain ⟨hNp, hj⟩ := D.host.ccK_split P hP hPle
      have hpe : p = Ideal.absNorm P := (Nat.prime_dvd_prime_iff_eq hpp hNp).1 hpP
      rw [← hpe] at hj
      exact not_fixed_splitK D w p hpp hp2 hj hpw hfix
    have e1 := val_eq_one D w β hβw
    have e2 := val_eq_one D w _ hNw
    rw [hβ] at e1
    rw [map_natCast] at e2
    rw [Formalism.BasicNotions.Host.xi0, Formalism.BasicNotions.Host.sqrtMinusD, map_div₀, Valuation.map_neg, map_one, map_mul, e2, e1]
    simp

def IsotDim {D : D7} (V : HS D) (k : ℕ) : Prop :=
  ∃ U : Submodule D.host.E V.V, Module.finrank D.host.E U = k ∧ ∀ x ∈ U, ∀ y ∈ U, V.hT x y = 0

def WittIdx {D : D7} (V : HS D) (r : ℕ) : Prop := IsotDim V r ∧ ¬ IsotDim V (r + 1)

def WittMinus {D : D7} (V U : HS D) (i : ℕ) : Prop :=
  ∃ ι : U.V →ₗ[D.host.E] V.V, Formalism.BasicNotions.HSpace.IsIsomEmb U V ι ∧
    ∃ e f : Fin i → V.V, (∀ k l, V.hT (e k) (e l) = 0) ∧ (∀ k l, V.hT (f k) (f l) = 0) ∧
      (∀ k l, V.hT (e k) (f l) = if k = l then 1 else 0) ∧
      (∀ x k, V.hT (ι x) (e k) = 0 ∧ V.hT (ι x) (f k) = 0) ∧ V.rank = U.rank + 2 * i

def Restr {ι : Type} {M : ι → Type} (s : ∀ i, M i) (φ : ∀ i, M i) : Prop := {i | φ i ≠ s i}.Finite

def IsIrr {Gp M : Type} [Monoid Gp] [AddCommGroup M] [Module ℂ M] (σ : Representation ℂ Gp M) : Prop :=
  Nontrivial M ∧ ∀ N : Submodule ℂ M, (∀ g, ∀ x ∈ N, σ g x ∈ N) → N = ⊥ ∨ N = ⊤

def RepIso {Gp M N : Type} [Monoid Gp] [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N]
    (σ : Representation ℂ Gp M) (π : Representation ℂ Gp N) : Prop :=
  ∃ e : M ≃ₗ[ℂ] N, ∀ g x, e (σ g x) = π g (e x)

open Classical in

structure LocW (D : D7) (T : ThetaX D) where

  sR : Bool

  ChrF : Type
  [chrFG : CommGroup ChrF]

  res : T.Chr →* ChrF

  eta : ChrF
  eta_sq : eta ^ 2 = 1
  eta_ne : eta ≠ 1

  cc : T.Chr →* T.Chr
  cc_cc : ∀ χ, cc (cc χ) = χ
  res_cc : ∀ χ, res (cc χ) = res χ
  cc_inf : ∀ χ τ, T.infTy (cc χ) τ = -T.infTy χ τ

  unr : T.Chr → FinE D → Prop

  val : T.Chr → FinE D → ℂ
  unr_one : ∀ w, unr 1 w ∧ val 1 w = 1
  unr_mul : ∀ χ χ' w, unr χ w → unr χ' w → unr (χ * χ') w ∧ val (χ * χ') w = val χ w * val χ' w
  unr_inv : ∀ χ w, unr χ w → unr χ⁻¹ w
  val_ram : ∀ χ w, ¬ unr χ w → val χ w = 0
  val_abs : ∀ χ w, unr χ w → ‖val χ w‖ = 1
  unr_ae : ∀ χ, Set.Finite {w | ¬ unr χ w}

  valI : T.Chr → FI D → ℂ
  valI_one : ∀ χ, valI χ 1 = 1
  valI_mul : ∀ χ (I J : FI D), I ≠ 0 → J ≠ 0 →
    (∀ w, ¬ unr χ w → FractionalIdeal.count D.host.E w I = 0 ∧ FractionalIdeal.count D.host.E w J = 0) →
    valI χ (I * J) = valI χ I * valI χ J
  valI_prime : ∀ χ (w : FinE D), unr χ w →
    valI χ ((w.asIdeal : Ideal (𝓞 D.host.E)) : FI D) = val χ w

  locChr : T.Chr → (w : FinE D) → (w.adicCompletion D.host.E)ˣ →* ℂˣ
  locChr_mul : ∀ χ χ' w, locChr (χ * χ') w = locChr χ w * locChr χ' w

  G : HS D → Type
  [gG : ∀ V, Group (G V)]
  [gM : ∀ V, MeasurableSpace (G V)]
  μG : ∀ V, Measure (G V)

  GF : ∀ V, Subgroup (G V)

  Fd : ∀ V, Set (G V)
  Fd_fund : ∀ V, IsFundamentalDomain (GF V) (Fd V) (μG V)

  ht : ∀ V, G V → ℝ
  ht_ge : ∀ V g, 1 ≤ ht V g
  ht_mul : ∀ V g g', ht V (g * g') ≤ ht V g * ht V g'

  Gk : ∀ V, Subgroup (G V)

  om : ∀ V W, T.Chr → T.Chr → Representation ℂ (G V × G W) (T.Sch V W)

  thF : ∀ V W, T.Sch V W →ₗ[ℂ] ℂ
  thF_aut : ∀ (V W : HS D) χ₁ χ₂, res χ₁ = eta ^ V.rank → res χ₂ = eta ^ W.rank →
    ∀ (γ : GF V) (γ' : GF W) (Φ : T.Sch V W),
      thF V W (om V W χ₁ χ₂ ((γ : G V), (γ' : G W)) Φ) = thF V W Φ

  Hloc : HS D → Pl D → Type
  [hL : ∀ V v, Monoid (Hloc V v)]

  aug : ∀ V v, Hloc V v →* ℂ
  aug_fin : ∀ V (v : FinF D) g, aug V (Sum.inl v) g = 1

  loc : ∀ V v, Gk V →* Hloc V v
  aug_loc : ∀ V v k, aug V v (loc V v k) = 1

  SchL : HS D → HS D → Pl D → Type
  [schLA : ∀ V W v, AddCommGroup (SchL V W v)]
  [schLM : ∀ V W v, Module ℂ (SchL V W v)]

  omL : ∀ V W, T.Chr → T.Chr → ∀ v, Representation ℂ (Hloc V v × Hloc W v) (SchL V W v)

  vac : ∀ V W v, SchL V W v

  pure : ∀ V W, (∀ v, SchL V W v) → T.Sch V W

  pure_span : ∀ V W, Submodule.span ℂ {Φ | ∃ φ, Restr (vac V W) φ ∧ Φ = pure V W φ} = T.kfin V W
  pure_om : ∀ (V W : HS D) χ₁ χ₂, res χ₁ = eta ^ V.rank → res χ₂ = eta ^ W.rank →
    ∀ (g : Gk V) (h : Gk W) φ, Restr (vac V W) φ →
      om V W χ₁ χ₂ ((g : G V), (h : G W)) (pure V W φ) =
        pure V W (fun v => omL V W χ₁ χ₂ v (loc V v g, loc W v h) (φ v))
  pure_mlin : ∀ V W φ v (c : ℂ) (x y : SchL V W v), Restr (vac V W) φ →
    pure V W (Function.update φ v (c • x + y)) =
      c • pure V W (Function.update φ v x) + pure V W (Function.update φ v y)

  glL : ∀ (V : HS D) (v : FinF D) (w : FinE D), Over D w v →
    Hloc V (Sum.inl v) →* Matrix.GeneralLinearGroup (Fin V.rank) (v.adicCompletion (FF D))
  glL_bij : ∀ V v w (hw : Over D w v), Split D v → Function.Bijective (glL V v w hw)

  linM : ∀ (V W : HS D) (v : FinF D) (w : FinE D), Over D w v →
    SchL V W (Sum.inl v) →ₗ[ℂ] (Matrix (Fin V.rank) (Fin W.rank) (v.adicCompletion (FF D)) → ℂ)
  linM_inj : ∀ V W v w (hw : Over D w v), Split D v → Function.Injective (linM V W v w hw)
  linM_eq : ∀ (V W : HS D) χ₁ χ₂ v w (hw : Over D w v), res χ₁ = eta ^ V.rank → res χ₂ = eta ^ W.rank →
    Split D v → ∀ g k, ∃ c : ℂ, c ≠ 0 ∧ ∀ φ,
    linM V W v w hw (omL V W χ₁ χ₂ (Sum.inl v) (g, k) φ) = c • fun Xm =>
      linM V W v w hw φ (Units.val (glL V v w hw g)⁻¹ * Xm * (Units.val (glL W v w hw k)⁻¹).transpose)

attribute [instance] LocW.chrFG LocW.gG LocW.gM LocW.hL LocW.schLA LocW.schLM

variable {D : D7} {T : ThetaX D}

def Lpart (X : LocW D T) (S0 : Finset (FinF D)) (ν : T.Chr) (s : ℤ) : ℂ :=
  ∏' w : {w : FinE D // ∀ v ∈ S0, ¬ Over D w v},
    (1 - X.val ν w.1 * ((Ideal.absNorm w.1.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹

def th (X : LocW D T) (V W : HS D) (χ₁ χ₂ : T.Chr) (Φ : T.Sch V W) (g : X.G V) (h : X.G W) : ℂ :=
  X.thF V W (X.om V W χ₁ χ₂ (g, h) Φ)

def Ith (X : LocW D T) (V W : HS D) (χ₁ χ₂ : T.Chr) (Φ : T.Sch V W) (h : X.G W) : ℂ :=
  ∫ g in X.Fd V, th X V W χ₁ χ₂ Φ g h ∂(X.μG V)

def htq (X : LocW D T) (V : HS D) (g : X.G V) : ℝ := ⨅ γ : X.GF V, X.ht V ((γ : X.G V) * g)

def IsThetaMap (X : LocW D T) (V W : HS D) (χ₁ χ₂ : T.Chr) (v : Pl D) {N : Type} [AddCommGroup N]
    [Module ℂ N] (σ : Representation ℂ (X.Hloc W v) N) (f : X.SchL V W v →ₗ[ℂ] N) : Prop :=
  ∀ g h φ, f (X.omL V W χ₁ χ₂ v (g, h) φ) = X.aug V v g • σ h (f φ)

def SmallTheta (X : LocW D T) (V W : HS D) (χ₁ χ₂ : T.Chr) (v : Pl D) {M : Type} [AddCommGroup M]
    [Module ℂ M] (π : Representation ℂ (X.Hloc W v) M) : Prop :=
  IsIrr π ∧ ∀ (N : Type) [AddCommGroup N] [Module ℂ N] (σ : Representation ℂ (X.Hloc W v) N), IsIrr σ →
    ((∃ f : X.SchL V W v →ₗ[ℂ] N, f ≠ 0 ∧ IsThetaMap X V W χ₁ χ₂ v σ f) ↔ RepIso σ π)

def HasSmallTheta (X : LocW D T) (V W : HS D) (χ₁ χ₂ : T.Chr) (v : Pl D) : Prop :=
  ∃ (M : Type) (_ : AddCommGroup M) (_ : Module ℂ M) (π : Representation ℂ (X.Hloc W v) M),
    SmallTheta X V W χ₁ χ₂ v π

def KudlaOK (X : LocW D T) (V W : HS D) (χ₁ χ₂ : T.Chr) : Prop :=
  X.res χ₁ = X.eta ^ V.rank ∧ X.res χ₂ = X.eta ^ W.rank

def ePlus (X : LocW D T) (τ : D.what₂.Tau) : Prop :=
  0 < ((tauE D τ) D.host.xi0).im ↔ X.sR = true

open Classical in

structure LocP {D : D7} {T : ThetaX D} (X : LocW D T) where
  PiT : HS D → HS D → HS D → T.Chr → T.Chr → Pl D → Type
  [piA : ∀ V V' W α β v, AddCommGroup (PiT V V' W α β v)]
  [piM : ∀ V V' W α β v, Module ℂ (PiT V V' W α β v)]
  piRep : ∀ V V' W α β v, Representation ℂ (X.Hloc W v) (PiT V V' W α β v)

  pi_def : ∀ V V' W α β v, HasSmallTheta X V W β (β / α) v →
    SmallTheta X V W β (β / α) v (piRep V V' W α β v)

  pL : ∀ V V' W α β v, X.SchL V W v →ₗ[ℂ] PiT V V' W α β v

  pL' : ∀ V V' W α β v, X.SchL V' W v →ₗ[ℂ] PiT V V' W α β v
  pL_th : ∀ V V' W α β v, IsThetaMap X V W β (β / α) v (piRep V V' W α β v) (pL V V' W α β v)
  pL'_th : ∀ V V' W α β v, IsThetaMap X V' W α (α / β) v (piRep V V' W α β v) (pL' V V' W α β v)
  pL_ne : ∀ V V' W α β v,
    (∃ f, f ≠ 0 ∧ IsThetaMap X V W β (β / α) v (piRep V V' W α β v) f) → pL V V' W α β v ≠ 0
  pL'_ne : ∀ V V' W α β v,
    (∃ f, f ≠ 0 ∧ IsThetaMap X V' W α (α / β) v (piRep V V' W α β v) f) → pL' V V' W α β v ≠ 0

  pL'_sph : ∀ V V' W α β (v : FinF D), (∀ w, Over D w v → X.unr α w ∧ X.unr β w) →
    (∃ f, f ≠ 0 ∧ IsThetaMap X V' W α (α / β) (Sum.inl v) (piRep V V' W α β (Sum.inl v)) f ∧
      f (X.vac V' W (Sum.inl v)) = pL V V' W α β (Sum.inl v) (X.vac V W (Sum.inl v))) →
    pL' V V' W α β (Sum.inl v) (X.vac V' W (Sum.inl v)) =
      pL V V' W α β (Sum.inl v) (X.vac V W (Sum.inl v))

  PiG : HS D → HS D → HS D → T.Chr → T.Chr → Type
  [piGA : ∀ V V' W α β, AddCommGroup (PiG V V' W α β)]
  [piGM : ∀ V V' W α β, Module ℂ (PiG V V' W α β)]
  purePi : ∀ V V' W α β, (∀ v, PiT V V' W α β v) → PiG V V' W α β
  purePi_mlin : ∀ V V' W α β ξ v (c : ℂ) (x y : PiT V V' W α β v),
    Restr (fun v => pL V V' W α β v (X.vac V W v)) ξ →
    purePi V V' W α β (Function.update ξ v (c • x + y)) =
      c • purePi V V' W α β (Function.update ξ v x) + purePi V V' W α β (Function.update ξ v y)
  purePi_span : ∀ V V' W α β, Submodule.span ℂ
    {z | ∃ ξ, Restr (fun v => pL V V' W α β v (X.vac V W v)) ξ ∧ z = purePi V V' W α β ξ} = ⊤

  purePi_sep : ∀ V V' W α β (l : ∀ v, PiT V V' W α β v →ₗ[ℂ] ℂ),
    {v | l v (pL V V' W α β v (X.vac V W v)) ≠ 1}.Finite →
    ∃ Λ : PiG V V' W α β →ₗ[ℂ] ℂ, ∀ ξ, Restr (fun v => pL V V' W α β v (X.vac V W v)) ξ →
      Λ (purePi V V' W α β ξ) = ∏ᶠ v, l v (ξ v)

  pG : ∀ V V' W α β, T.Sch V W →ₗ[ℂ] PiG V V' W α β
  pG' : ∀ V V' W α β, T.Sch V' W →ₗ[ℂ] PiG V V' W α β
  pG_pure : ∀ V V' W α β φ, Restr (X.vac V W) φ →
    pG V V' W α β (X.pure V W φ) = purePi V V' W α β (fun v => pL V V' W α β v (φ v))
  pG'_pure : ∀ V V' W α β φ, Restr (X.vac V' W) φ →
    pG' V V' W α β (X.pure V' W φ) = purePi V V' W α β (fun v => pL' V V' W α β v (φ v))

attribute [instance] LocP.piA LocP.piM LocP.piGA LocP.piGM

structure Loc (D : D7) (T : ThetaX D) where
  w : LocW D T
  p : LocP w

def IntV (v : FinF D) (c : ℕ) (x : v.adicCompletion (FF D)) : Prop :=
  Valued.v x ≤ WithZero.exp (-(c : ℤ))

def GLO {n : ℕ} (v : FinF D) (A : Matrix (Fin n) (Fin n) (v.adicCompletion (FF D))) : Prop :=
  (∀ i j, IntV v 0 (A i j)) ∧ Valued.v A.det = 1

def condExp (X : LocW D T) (χ : T.Chr) (w : FinE D) : ℕ :=
  sInf {n : ℕ | ∀ u : (w.adicCompletion D.host.E)ˣ,
    Valued.v ((u : w.adicCompletion D.host.E) - 1) ≤ WithZero.exp (-(n : ℤ)) → X.locChr χ w u = 1}

def IsStd (X : LocW D T) (V W : HS D) (χ₁ χ₂ : T.Chr) (v : FinF D) (w : FinE D) (hw : Over D w v)
    (blk : Fin V.rank → Fin W.rank) (c : ℕ) (φ : X.SchL V W (Sum.inl v)) : Prop :=
  (∀ Xm, X.linM V W v w hw φ Xm ≠ 0 →
    GLO v (Xm.submatrix id blk) ∧ ∀ i j, j ∉ Set.range blk → IntV v c (Xm i j)) ∧
  (∀ Xm, Xm.submatrix id blk = 1 → (∀ i j, j ∉ Set.range blk → IntV v c (Xm i j)) →
    X.linM V W v w hw φ Xm = X.linM V W v w hw (X.vac V W (Sum.inl v)) 0) ∧
  (∀ g : X.Hloc V (Sum.inl v), GLO v (Units.val (X.glL V v w hw g)) →
    X.omL V W χ₁ χ₂ (Sum.inl v) (g, 1) φ = φ)

def Pin (D : D7) (T : ThetaX D) (Lc : Loc D T) : Prop :=
  (∃ (wv : FinF D → FinE D) (hwv : ∀ v, Split D v → Over D (wv v) v),
    (∀ (V : HS D) (v : FinF D) (hv : Split D v) (w' : FinE D) (hw' : Over D w' v), w' ≠ wv v →
      ∀ g, Units.val (Lc.w.glL V v w' hw' g) =
        (Units.val (Lc.w.glL V v (wv v) (hwv v hv) g)⁻¹).transpose) ∧
    (∀ (V V' W : HS D) (α β : T.Chr) (v : FinF D) (hv : Split D v) (w' : FinE D) (hw' : Over D w' v)
      (hs : V.rank + V'.rank = W.rank), w' ≠ wv v → V'.rank < V.rank →
      Lc.w.cc α = α⁻¹ → Lc.w.cc β = β⁻¹ →
      Lc.w.res α = Lc.w.eta ^ V'.rank → Lc.w.res β = Lc.w.eta ^ V.rank →
      ¬ Lc.w.unr (α / β) (wv v) →
      (∃ φ, IsStd Lc.w V W β (β / α) v (wv v) (hwv v hv) (fun j => Fin.cast hs (Fin.castAdd V'.rank j))
        (condExp Lc.w (α / β) (wv v)) φ) ∧
      (∃ φ', IsStd Lc.w V' W α (α / β) v w' hw' (fun j => Fin.cast hs (Fin.natAdd V.rank j))
        (condExp Lc.w (α / β) (wv v)) φ') ∧
      ∀ φ φ',
        IsStd Lc.w V W β (β / α) v (wv v) (hwv v hv) (fun j => Fin.cast hs (Fin.castAdd V'.rank j))
          (condExp Lc.w (α / β) (wv v)) φ →
        IsStd Lc.w V' W α (α / β) v w' hw' (fun j => Fin.cast hs (Fin.natAdd V.rank j))
          (condExp Lc.w (α / β) (wv v)) φ' →
        (∃ f, IsThetaMap Lc.w V' W α (α / β) (Sum.inl v) (Lc.p.piRep V V' W α β (Sum.inl v)) f ∧
          f φ' = Lc.p.pL V V' W α β (Sum.inl v) φ) →
        Lc.p.pL' V V' W α β (Sum.inl v) φ' = Lc.p.pL V V' W α β (Sum.inl v) φ)) ∧
  (∀ (V V' W : HS D) (α β α₂ β₂ : T.Chr) (τ : D.what₂.Tau),
    V.rank + V'.rank = W.rank →
    Lc.w.cc α = α⁻¹ → Lc.w.cc β = β⁻¹ → Lc.w.cc α₂ = α₂⁻¹ → Lc.w.cc β₂ = β₂⁻¹ →
    Lc.w.res α = Lc.w.eta ^ V'.rank → Lc.w.res β = Lc.w.eta ^ V.rank →
    Lc.w.res α₂ = Lc.w.eta ^ V'.rank → Lc.w.res β₂ = Lc.w.eta ^ V.rank →
    T.infTy α τ = T.infTy α₂ τ → T.infTy β τ = T.infTy β₂ τ →
    ∃ e : Lc.p.PiT V V' W α β (Sum.inr τ) ≃ₗ[ℂ] Lc.p.PiT V V' W α₂ β₂ (Sum.inr τ),
      (∀ φ, e (Lc.p.pL V V' W α β (Sum.inr τ) φ) = Lc.p.pL V V' W α₂ β₂ (Sum.inr τ) φ) ∧
      (∀ φ, e (Lc.p.pL' V V' W α β (Sum.inr τ) φ) = Lc.p.pL' V V' W α₂ β₂ (Sum.inr τ) φ))

structure Sett (D : D7) (T : ThetaX D) (Lc : Loc D T) where

  Vt : ℕ → HS D
  V't : ℕ → HS D
  Wt : ℕ → HS D
  a : ℕ
  a' : ℕ
  d : ℕ
  e : ℕ
  p : ℕ
  q : ℕ
  rV : (Vt 0).rank = a
  rV' : (V't 0).rank = a'
  rW : (Wt 0).rank = d
  lt : a' < a
  sum : a + a' = d
  two_e : a = a' + 2 * e
  e_big : 2 * (p + q) + 1 < e
  a'_big : 2 * (p + q) + 1 < a'
  Vt_spec : ∀ i ≤ p, WittMinus (Vt 0) (Vt i) i
  V't_spec : ∀ j ≤ q, WittMinus (V't 0) (V't j) j
  Wt_spec : ∀ k ≤ p + q, WittMinus (Wt 0) (Wt k) k
  wittV : WittIdx (Vt 0) p
  wittV' : WittIdx (V't 0) q
  α : T.Chr
  β : T.Chr
  α_sd : Lc.w.cc α = α⁻¹
  β_sd : Lc.w.cc β = β⁻¹
  α_res : Lc.w.res α = Lc.w.eta ^ a'
  β_res : Lc.w.res β = Lc.w.eta ^ a

  kap : ∀ τ, (d : ℚ) < |2 * T.infTy (α / β) τ|
  okV : ∀ i ≤ p, (Vt i).SigOK
  okV' : ∀ j ≤ q, (V't j).SigOK
  okW : ∀ k ≤ p + q, (Wt k).SigOK

  sigV : ∀ i ≤ p, ∀ τ, (Vt i).sig (tauE D τ) = (a - p - i, p - i)
  sigV' : ∀ j ≤ q, ∀ τ, (V't j).sig (tauE D τ) = (q - j, a' - q - j)

  sigW : ∀ k ≤ p + q, ∀ τ, (Wt k).sig (tauE D τ) =
    if (ePlus Lc.w τ ↔ 0 < T.infTy (α / β) τ) then (d - (p + q) - k, p + q - k)
    else (p + q - k, d - (p + q) - k)
  S0 : Finset (FinF D)
  Q : Finset (FinF D)
  disj : Disjoint S0 Q
  spl : ∀ v ∈ S0 ∪ Q, Split D v
  ram : ∀ v ∈ S0 ∪ Q, ∀ w, Over D w v → ¬ Lc.w.unr (α / β) w
  unram : ∀ w : FinE D, (∀ v ∈ S0 ∪ Q, ¬ Over D w v) → Lc.w.unr α w ∧ Lc.w.unr β w

  psiSQ : ∀ v ∈ S0 ∪ Q, ¬ differentIdeal ℤ (𝓞 (FF D)) ≤ v.asIdeal
  v1 : FinF D
  w1 : FinE D
  hw1 : Over D w1 v1
  auxiliary_place_outside : v1 ∉ S0 ∪ Q
  auxiliary_place_split_prime : ∃ ℓ : ℕ, ℓ.Prime ∧ ((ℓ : ℤ) : 𝓞 (FF D)) ∈ v1.asIdeal ∧ SplitsCompletely D ℓ

  f13 : InertPlaceConditions D := inert_conditions_hold D

namespace Sett

variable {Lc : Loc D T} (S : Sett D T Lc)

def ν : T.Chr := S.α / S.β

def Sz (i j : ℕ) : Submodule ℂ (T.Sch (S.V't j) (S.Wt (i + j))) :=
  Submodule.span ℂ {Φ | ∃ φ, Restr (Lc.w.vac (S.V't j) (S.Wt (i + j))) φ ∧
    Φ = Lc.w.pure (S.V't j) (S.Wt (i + j)) φ ∧
    ∀ Xm, Lc.w.linM (S.V't j) (S.Wt (i + j)) S.v1 S.w1 S.hw1 (φ (Sum.inl S.v1)) Xm ≠ 0 →
      Xm.rank = (S.V't j).rank}

def IA (i j : ℕ) (Φ : T.Sch (S.Vt i) (S.Wt (i + j))) : Lc.w.G (S.Wt (i + j)) → ℂ :=
  Ith Lc.w (S.Vt i) (S.Wt (i + j)) S.β (S.β / S.α) Φ

def IB (i j : ℕ) (Φ : T.Sch (S.V't j) (S.Wt (i + j))) : Lc.w.G (S.Wt (i + j)) → ℂ :=
  Ith Lc.w (S.V't j) (S.Wt (i + j)) S.α (S.α / S.β) Φ

def LM (i j : ℕ) : Prop := ∀ v : Pl D,
  SmallTheta Lc.w (S.Vt i) (S.Wt (i + j)) S.β (S.β / S.α) v
      (Lc.p.piRep (S.Vt i) (S.V't j) (S.Wt (i + j)) S.α S.β v) ∧
    SmallTheta Lc.w (S.V't j) (S.Wt (i + j)) S.α (S.α / S.β) v
      (Lc.p.piRep (S.Vt i) (S.V't j) (S.Wt (i + j)) S.α S.β v) ∧
    Function.Surjective (Lc.p.pL (S.Vt i) (S.V't j) (S.Wt (i + j)) S.α S.β v) ∧
    Function.Surjective (Lc.p.pL' (S.Vt i) (S.V't j) (S.Wt (i + j)) S.α S.β v)

def RD (i j : ℕ) : Prop := ∀ Φ' ∈ S.Sz i j,
  (∀ h, IntegrableOn (fun g => th Lc.w (S.V't j) (S.Wt (i + j)) S.α (S.α / S.β) Φ' g h)
      (Lc.w.Fd (S.V't j)) (Lc.w.μG (S.V't j))) ∧
  ∀ N : ℕ, ∃ C M : ℝ, ∀ g h, ‖th Lc.w (S.V't j) (S.Wt (i + j)) S.α (S.α / S.β) Φ' g h‖ ≤
    C * htq Lc.w (S.V't j) g ^ (-(N : ℝ)) * Lc.w.ht (S.Wt (i + j)) h ^ M

def NZ (i j : ℕ) : Prop := ∃ Φ' ∈ S.Sz i j, S.IB i j Φ' ≠ 0

def Prop2 (i j : ℕ) (c : ℂ) : Prop := ∀ Φ ∈ T.kfin (S.Vt i) (S.Wt (i + j)), ∀ Φ' ∈ S.Sz i j,
  Lc.p.pG (S.Vt i) (S.V't j) (S.Wt (i + j)) S.α S.β Φ =
    Lc.p.pG' (S.Vt i) (S.V't j) (S.Wt (i + j)) S.α S.β Φ' →
  S.IA i j Φ = c • S.IB i j Φ'

end Sett

def LWW {D : D7} (W : HS D) : Submodule (𝓞 D.host.E) W.V :=
  Submodule.span (𝓞 D.host.E) {x | ∃ a ∈ D.host.AA, ∃ l ∈ W.L0, x = a • l}

structure Key (D : D7) where
  tag : Bool
  rk : Fin 7 → ℕ
  V : HS D
  V' : HS D
  W : HS D
  V1 : HS D
  V1' : HS D
  W1 : HS D
  Vc : HS D
  x0 : Vc.V
  w0 : W.V
  S0 : Finset (FinF D)
  inf : D.what₂.Tau → ℚ × ℚ
  localCharactersAtS0 : (w : FinE D) → Option (((w.adicCompletion D.host.E)ˣ →* ℂˣ) × ((w.adicCompletion D.host.E)ˣ →* ℂˣ))

namespace Sett

variable {Lc : Loc D T} (S : Sett D T Lc)

def cone (i j : ℕ) (tag : Bool) : HS D := bif tag then S.V't j else S.Vt i

def rk (i j : ℕ) : Fin 7 → ℕ := ![S.a, S.a', S.d, S.p, S.q, i, j]

open Classical in

def key (i j : ℕ) (tag : Bool) (x0 : (S.cone i j tag).V) (w0 : (S.Wt (i + j)).V) : Key D where
  tag := tag
  rk := S.rk i j
  V := S.Vt i
  V' := S.V't j
  W := S.Wt (i + j)
  V1 := bif tag then S.Vt i else S.Vt (i + 1)
  V1' := bif tag then S.V't (j + 1) else S.V't j
  W1 := S.Wt (i + j + 1)
  Vc := S.cone i j tag
  x0 := x0
  w0 := w0
  S0 := S.S0
  inf := fun τ => (T.infTy S.α τ, T.infTy S.β τ)
  localCharactersAtS0 := fun w => if ∃ v ∈ S.S0, Over D w v then some (Lc.w.locChr S.α w, Lc.w.locChr S.β w) else none

def SUnitQ (x : ℂ) : Prop :=
  x ≠ 0 ∧ ∃ M n : ℕ, 0 < M ∧ (∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ M → ∃ v ∈ S.Q, ((ℓ : ℤ) : 𝓞 (FF D)) ∈ v.asIdeal) ∧
    IsIntegral ℤ ((M : ℂ) ^ n * x) ∧ IsIntegral ℤ ((M : ℂ) ^ n * x⁻¹)

def IsoVec (i j : ℕ) (tag : Bool) (x0 : (S.cone i j tag).V) (w0 : (S.Wt (i + j)).V) (bb cc : FI D) : Prop :=
  x0 ≠ 0 ∧ (S.cone i j tag).hT x0 x0 = 0 ∧ w0 ≠ 0 ∧ (S.Wt (i + j)).hT w0 w0 = 0 ∧
    (∀ t : D.host.E, t ∈ bb ↔ t • x0 ∈ (S.cone i j tag).L0) ∧
    (∀ t : D.host.E, t ∈ cc ↔ t • w0 ∈ LWW (S.Wt (i + j))) ∧
    (∀ w : FinE D, (∃ v ∈ S.S0 ∪ S.Q, Over D w v) →
      FractionalIdeal.count D.host.E w bb = 0 ∧ FractionalIdeal.count D.host.E w cc = 0)

def IsU (uLoc : Key D → ℂ) (kExp : Bool → (Fin 7 → ℕ) → ℚ × ℚ × ℚ) (sb sc : Bool → ℤ)
    (i j : ℕ) (tag : Bool) (u : ℂ) : Prop :=
  ∀ (x0 : (S.cone i j tag).V) (w0 : (S.Wt (i + j)).V) (bb cc : FI D), S.IsoVec i j tag x0 w0 bb cc →
    ∃ x : ℂ, S.SUnitQ x ∧
      u = uLoc (S.key i j tag x0 w0) *
        (((((NumberField.discr D.host.E).natAbs : ℝ) ^ ((kExp tag (S.rk i j)).1 : ℝ)) *
          ((FractionalIdeal.absNorm bb : ℚ) : ℝ) ^ ((kExp tag (S.rk i j)).2.1 : ℝ) *
          ((FractionalIdeal.absNorm cc : ℚ) : ℝ) ^ ((kExp tag (S.rk i j)).2.2 : ℝ) : ℝ) : ℂ) *
        Lc.w.valI S.ν (bb ^ sb tag * cc ^ sc tag) * x

def key0 (i j : ℕ) (tag : Bool) (x0 : (S.cone i j tag).V) (w0 : (S.Wt (i + j)).V) : Key D :=
  { S.key i j tag x0 w0 with localCharactersAtS0 := fun _ => none }

def SUnitSQ (x : ℂ) : Prop :=
  x ≠ 0 ∧ ∃ M n : ℕ, 0 < M ∧
    (∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ M → ∃ v ∈ S.S0 ∪ S.Q, ((ℓ : ℤ) : 𝓞 (FF D)) ∈ v.asIdeal) ∧
    IsIntegral ℤ ((M : ℂ) ^ n * x) ∧ IsIntegral ℤ ((M : ℂ) ^ n * x⁻¹)

def IsUStd (uInf : Key D → ℂ) (kExp : Bool → (Fin 7 → ℕ) → ℚ × ℚ × ℚ) (sb sc : Bool → ℤ)
    (i j : ℕ) (tag : Bool) (u : ℂ) : Prop :=
  ∀ (x0 : (S.cone i j tag).V) (w0 : (S.Wt (i + j)).V) (bb cc : FI D), S.IsoVec i j tag x0 w0 bb cc →
    ∃ x : ℂ, S.SUnitSQ x ∧
      u = uInf (S.key0 i j tag x0 w0) *
        (((((NumberField.discr D.host.E).natAbs : ℝ) ^ ((kExp tag (S.rk i j)).1 : ℝ)) *
          ((FractionalIdeal.absNorm bb : ℚ) : ℝ) ^ ((kExp tag (S.rk i j)).2.1 : ℝ) *
          ((FractionalIdeal.absNorm cc : ℚ) : ℝ) ^ ((kExp tag (S.rk i j)).2.2 : ℝ) : ℝ) : ℂ) *
        Lc.w.valI S.ν (bb ^ sb tag * cc ^ sc tag) * x

end Sett

def aux₃ (D : D7) (T : ThetaX D) (Lc : Loc D T) : Prop :=
  ∃ (uLoc : Key D → ℂ) (kExp : Bool → (Fin 7 → ℕ) → ℚ × ℚ × ℚ) (sb sc : Bool → ℤ),
    (∀ k, uLoc k ≠ 0) ∧ (∀ t, (sb t = 1 ∨ sb t = -1) ∧ (sc t = 1 ∨ sc t = -1)) ∧
    ∀ S : Sett D T Lc,
      (∀ i ≤ S.p, ∀ j ≤ S.q, S.LM i j ∧ S.RD i j ∧ S.NZ i j) ∧
      ∃ c : ℕ → ℕ → ℂ, (∀ i ≤ S.p, ∀ j ≤ S.q, S.Prop2 i j (c i j)) ∧
        (∀ i ≤ S.p, ∀ j < S.q, ∃ u, S.IsU uLoc kExp sb sc i j true u ∧
          c i j * Lpart Lc.w S.S0 S.ν ((S.e : ℤ) - i + j + 1) = u * c i (j + 1)) ∧
        (∀ i < S.p, ∃ u, S.IsU uLoc kExp sb sc i S.q false u ∧
          c i S.q = u * Lpart Lc.w S.S0 S.ν ((S.e : ℤ) - i + S.q) * c (i + 1) S.q)

def KudlaConstantNonzero (D : D7) (T : ThetaX D) (Lc : Loc D T) : Prop :=
  ∀ S : Sett D T Lc, ∀ i ≤ S.p, ∀ j ≤ S.q, ∀ c : ℂ, S.Prop2 i j c → c ≠ 0

def KudlaStandardNormalisation (D : D7) (T : ThetaX D) (Lc : Loc D T) : Prop :=
  ∃ (uInf : Key D → ℂ) (kExp : Bool → (Fin 7 → ℕ) → ℚ × ℚ × ℚ) (sb sc : Bool → ℤ),
    (∀ k, uInf k ≠ 0) ∧ (∀ t, (sb t = 1 ∨ sb t = -1) ∧ (sc t = 1 ∨ sc t = -1)) ∧
    ∀ S : Sett D T Lc, ∀ c : ℕ → ℕ → ℂ, (∀ i ≤ S.p, ∀ j ≤ S.q, S.Prop2 i j (c i j)) →
      (∀ i ≤ S.p, ∀ j < S.q, ∃ u, S.IsUStd uInf kExp sb sc i j true u ∧
        c i j * Lpart Lc.w S.S0 S.ν ((S.e : ℤ) - i + j + 1) = u * c i (j + 1)) ∧
      (∀ i < S.p, ∃ u, S.IsUStd uInf kExp sb sc i S.q false u ∧
        c i S.q = u * Lpart Lc.w S.S0 S.ν ((S.e : ℤ) - i + S.q) * c (i + 1) S.q)

def adm1 (D : D7) (T : ThetaX D) (Lc : Loc D T) : Prop :=
  ∀ (V W : HS D) (χ₁ χ₂ : T.Chr) (r : ℕ), KudlaOK Lc.w V W χ₁ χ₂ → WittIdx V r →
    (r = 0 ∨ W.rank < 2 * (V.rank - r)) → ∀ Φ h,
      IntegrableOn (fun g => th Lc.w V W χ₁ χ₂ Φ g h) (Lc.w.Fd V) (Lc.w.μG V)

def adm2 (D : D7) (T : ThetaX D) (Lc : Loc D T) : Prop :=
  ∀ (V W : HS D) (χ₁ χ₂ : T.Chr) (v : Pl D), KudlaOK Lc.w V W χ₁ χ₂ →
    (∀ (N N' : Type) [AddCommGroup N] [Module ℂ N] [AddCommGroup N'] [Module ℂ N']
        (σ : Representation ℂ (Lc.w.Hloc W v) N) (σ' : Representation ℂ (Lc.w.Hloc W v) N'),
        IsIrr σ → IsIrr σ' →
        (∃ f : Lc.w.SchL V W v →ₗ[ℂ] N, f ≠ 0 ∧ IsThetaMap Lc.w V W χ₁ χ₂ v σ f) →
        (∃ f : Lc.w.SchL V W v →ₗ[ℂ] N', f ≠ 0 ∧ IsThetaMap Lc.w V W χ₁ χ₂ v σ' f) → RepIso σ σ') ∧
    (∀ (N : Type) [AddCommGroup N] [Module ℂ N] (σ : Representation ℂ (Lc.w.Hloc W v) N), IsIrr σ →
        ∀ f f' : Lc.w.SchL V W v →ₗ[ℂ] N, IsThetaMap Lc.w V W χ₁ χ₂ v σ f →
          IsThetaMap Lc.w V W χ₁ χ₂ v σ f' → f ≠ 0 → ∃ c : ℂ, f' = c • f)

def adm3 (D : D7) (T : ThetaX D) (Lc : Loc D T) : Prop :=
  ∀ (V V' W : HS D) (α β : T.Chr) (v : FinF D), ¬ Split D v →
    (∀ w, Over D w v → Lc.w.unr α w ∧ Lc.w.unr β w) → Lc.w.cc α = α⁻¹ → Lc.w.cc β = β⁻¹ →
    Lc.w.res α = Lc.w.eta ^ V'.rank → Lc.w.res β = Lc.w.eta ^ V.rank → V.rank + V'.rank = W.rank →
    V.rank % 2 = V'.rank % 2 →
    ∃ (M : Type) (_ : AddCommGroup M) (_ : Module ℂ M)
      (π : Representation ℂ (Lc.w.Hloc W (Sum.inl v)) M),
      SmallTheta Lc.w V W β (β / α) (Sum.inl v) π ∧ SmallTheta Lc.w V' W α (α / β) (Sum.inl v) π

def ArchimedeanSignatureMatching (D : D7) (T : ThetaX D) (Lc : Loc D T) : Prop :=
  ∀ (V W : HS D) (χ₁ χ₂ : T.Chr) (τ : D.what₂.Tau) (εV εW : Bool), KudlaOK Lc.w V W χ₁ χ₂ →
    V.SigOK → W.SigOK →
    V.sig (tauE D τ) = (if εV = true then (V.rank, 0) else (0, V.rank)) →
    W.sig (tauE D τ) = (if εW = true then (W.rank, 0) else (0, W.rank)) →
    (∀ (N : Type) [AddCommGroup N] [Module ℂ N] (σ : Representation ℂ (Lc.w.Hloc W (Sum.inr τ)) N)
        (f : Lc.w.SchL V W (Sum.inr τ) →ₗ[ℂ] N), IsThetaMap Lc.w V W χ₁ χ₂ (Sum.inr τ) σ f →
        Function.Surjective f → Nontrivial N → IsIrr σ) ∧
    (V.rank ≤ W.rank →
      (((εV = εW) ↔ ePlus Lc.w τ) → 2 * T.infTy χ₂ τ + (W.rank : ℚ) ≤ 0) →
      (¬ ((εV = εW) ↔ ePlus Lc.w τ) → (W.rank : ℚ) ≤ 2 * T.infTy χ₂ τ) →
      ∃ (N : Type) (_ : AddCommGroup N) (_ : Module ℂ N)
        (σ : Representation ℂ (Lc.w.Hloc W (Sum.inr τ)) N) (f : Lc.w.SchL V W (Sum.inr τ) →ₗ[ℂ] N),
        f ≠ 0 ∧ IsThetaMap Lc.w V W χ₁ χ₂ (Sum.inr τ) σ f)

def admitted (D : D7) (T : ThetaX D) (Lc : Loc D T) : Prop :=
  adm1 D T Lc ∧ adm2 D T Lc ∧ adm3 D T Lc ∧ ArchimedeanSignatureMatching D T Lc

def Stmt (D : D7) (T : ThetaX D) (Lc : Loc D T) : Prop :=
  Pin D T Lc → admitted D T Lc → aux₃ D T Lc ∧ KudlaConstantNonzero D T Lc ∧ KudlaStandardNormalisation D T Lc

def PinF {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps)
    (LF : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), Loc (Fm.D x i) (Fm.ex x hx i).th) : Prop :=
  ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), Pin (Fm.D x i) (Fm.ex x hx i).th (LF x hx i)

def AdmF {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps)
    (LF : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), Loc (Fm.D x i) (Fm.ex x hx i).th) : Prop :=
  ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), admitted (Fm.D x i) (Fm.ex x hx i).th (LF x hx i)

def OrbitValuationBound {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps)
    (LF : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), Loc (Fm.D x i) (Fm.ex x hx i).th) : Prop :=
  ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x),
    aux₃ (Fm.D x i) (Fm.ex x hx i).th (LF x hx i) ∧ KudlaConstantNonzero (Fm.D x i) (Fm.ex x hx i).th (LF x hx i) ∧
      KudlaStandardNormalisation (Fm.D x i) (Fm.ex x hx i).th (LF x hx i)

def KudlaFamilyStatement {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps)
    (LF : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), Loc (Fm.D x i) (Fm.ex x hx i).th) : Prop :=
  PinF Fm LF → AdmF Fm LF → OrbitValuationBound Fm LF

end Formalism.MainNotions.KudlaSiegelWeil
