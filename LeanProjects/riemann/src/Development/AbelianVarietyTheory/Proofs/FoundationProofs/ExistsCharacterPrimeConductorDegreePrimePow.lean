import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ClsFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.DecActRoots
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.UnitsMapSurjOfZmod
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicCharInertiaSurjective

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.Ord2.PrimeChar

theorem normV_prime (v : Pl) : (normV v).Prime := by
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

theorem normV_mem (v : Pl) : ((normV v : ℕ) : 𝓞 ℚ) ∈ v.asIdeal := Ideal.absNorm_mem v.asIdeal

theorem val_normV_lt_one {Ω : Type} [Field Ω] [Algebra ℚ Ω] {B : ValuationSubring Ω} {v : Pl}
    (h : IsPlaceOver B v) : B.valuation ((normV v : ℕ) : Ω) < 1 := by
  have := (h _).2 (normV_mem v)
  simpa using this

theorem eq_of_normV_eq {v w : Pl} (h : normV v = normV w) : v = w := by
  have hp := normV_prime w
  have hpr : Prime ((normV w : ℕ) : 𝓞 ℚ) := by
    have h1 : Prime ((normV w : ℕ) : ℤ) := Nat.prime_iff_prime_int.mp hp
    have e : ((normV w : ℕ) : 𝓞 ℚ) = Rat.ringOfIntegersEquiv.symm ((normV w : ℕ) : ℤ) := by simp
    rw [e]
    exact (MulEquiv.prime_iff Rat.ringOfIntegersEquiv.symm.toMulEquiv).mpr h1
  have hI : (Ideal.span {((normV w : ℕ) : 𝓞 ℚ)}).IsMaximal :=
    Ideal.IsPrime.isMaximal ((Ideal.span_singleton_prime hpr.ne_zero).mpr hpr)
      (by rw [Ne, Ideal.span_singleton_eq_bot]; exact hpr.ne_zero)
  have hv : Ideal.span {((normV w : ℕ) : 𝓞 ℚ)} = v.asIdeal :=
    hI.eq_of_le v.isPrime.ne_top (by rw [Ideal.span_singleton_le_iff_mem, ← h]; exact normV_mem v)
  have hw : Ideal.span {((normV w : ℕ) : 𝓞 ℚ)} = w.asIdeal :=
    hI.eq_of_le w.isPrime.ne_top (by rw [Ideal.span_singleton_le_iff_mem]; exact normV_mem w)
  exact HeightOneSpectrum.ext (hv.symm.trans hw)

theorem exists_surj (p N : ℕ) [Fact p.Prime] (h : N ∣ p - 1) :
    ∃ f : (ZMod p)ˣ →* Multiplicative (ZMod N), Function.Surjective f := by
  have hc : IsCyclic (ZMod p)ˣ := inferInstance
  have hcard : N ∣ Nat.card (ZMod p)ˣ := by rw [Nat.card_eq_fintype_card, ZMod.card_units]; exact h
  let c : ZMod (Nat.card (ZMod p)ˣ) →+ ZMod N := (ZMod.castHom hcard (ZMod N)).toAddMonoidHom
  refine ⟨(AddMonoidHom.toMultiplicative c).comp (zmodCyclicMulEquiv hc).symm.toMonoidHom, ?_⟩
  intro y
  obtain ⟨x, hx⟩ := ZMod.castHom_surjective hcard (Multiplicative.toAdd y)
  refine ⟨zmodCyclicMulEquiv hc (Multiplicative.ofAdd x), ?_⟩
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
  show Multiplicative.ofAdd (c x) = y
  exact hx

theorem pow_self_eq_one (N : ℕ) (a : Multiplicative (ZMod N)) : a ^ N = 1 := by
  apply Multiplicative.toAdd.injective
  rw [toAdd_pow, toAdd_one, nsmul_eq_mul, ZMod.natCast_self, zero_mul]

end GlobalTheory.Ord2.PrimeChar

namespace GlobalTheory.Ord2.PrimeChar

theorem exists_prime_char : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (n : ℕ) (w : Pl),
    1 ≤ n → l ^ n ∣ normV w - 1 → ∃ ψ : G ℚ Ω →* Multiplicative (ZMod (l ^ n)), KillsMu (normV w) ψ ∧
      Function.Surjective ψ ∧ (∀ B : ValuationSubring Ω, IsPlaceOver B w → ∃ τ ∈ Ine (F := ℚ) B, (ψ τ).toAdd = 1) ∧
      ∀ v : Pl, v ≠ w → (∃ x : ZMod (normV w), x ^ (l ^ n) = (normV v : ZMod (normV w))) →
        ∀ B : ValuationSubring Ω, IsPlaceOver B v → Dec (F := ℚ) B ≤ ψ.ker := by
  intro l _ Ω _ _ _ n w _ hdiv
  have hp := normV_prime w
  haveI : Fact (normV w).Prime := ⟨hp⟩
  haveI : NeZero (normV w) := ⟨hp.ne_zero⟩
  haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  obtain ⟨f, hf⟩ := exists_surj (normV w) (l ^ n) hdiv

  have hine : ∀ B : ValuationSubring Ω, IsPlaceOver B w →
      ∃ τ ∈ Ine (F := ℚ) B, (f.comp (Chr.cls ℚ Ω (normV w)) τ).toAdd = 1 := by
    intro B hB
    have hBp := val_normV_lt_one hB
    obtain ⟨g0, hg0⟩ := hf (Multiplicative.ofAdd 1)
    have hd : normV w ^ 1 ∣ normV w := by rw [pow_one]
    obtain ⟨w0, hw0⟩ := KStar.TotallyRealRoots.redPow_surjective (l := normV w) 1 (ZMod.unitsMap hd g0)
    obtain ⟨σ, hσ, hσw⟩ := GlobalTheory.CycInertia.cycZ_Ine_surjective Ω (normV w) B hBp w0
    refine ⟨σ, hσ, ?_⟩
    haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
    haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
    haveI : NeZero ((normV w : ℕ) : Ω) := ⟨Nat.cast_ne_zero.mpr hp.ne_zero⟩
    have hX : PadicInt.toZModPow 1 (w0 : ℤ_[normV w]) = (((g0 : ZMod (normV w)).val : ℕ) : ZMod (normV w ^ 1)) := by
      have h2 := congrArg (fun u : (ZMod (normV w ^ 1))ˣ => (u : ZMod (normV w ^ 1))) hw0
      simp only [ZMod.unitsMap_val] at h2
      rw [← ZMod.cast_natCast (R := ZMod (normV w ^ 1)) hd ((g0 : ZMod (normV w)).val), ZMod.natCast_zmod_val]
      exact h2
    have hcls : Chr.cls ℚ Ω (normV w) σ = g0 := by
      refine (Chr.clsFacts ℚ Ω (normV w)).2.2.1 σ g0 fun ζ hζ => ?_
      have hζ' : ζ ^ (normV w ^ 1) = 1 := by rw [pow_one]; exact hζ
      have hspec : σ ζ = ζ ^ (PadicInt.toZModPow 1 ((cycZ ℚ Ω (normV w) σ : ℤ_[normV w]ˣ) : ℤ_[normV w])).val :=
        cyclotomicCharacter.spec (L := Ω) (normV w) (MulSemiringAction.toRingAut (G ℚ Ω) Ω σ) ζ hζ'
      rw [hspec, hσw, hX, ZMod.val_natCast, ← pow_eq_pow_mod _ hζ']
    rw [MonoidHom.comp_apply, hcls, hg0, toAdd_ofAdd]
  refine ⟨f.comp (Chr.cls ℚ Ω (normV w)), fun s hs => ?_, fun y => ?_, hine, fun v hvw hx B hB => ?_⟩
  ·
    have h1 : Chr.cls ℚ Ω (normV w) s = 1 := (Chr.clsFacts ℚ Ω (normV w)).2.2.1 s 1 fun ζ hζ => by
      rw [Units.val_one, ZMod.val_one_eq_one_mod, ← pow_eq_pow_mod 1 hζ, pow_one]
      exact hs ζ hζ
    rw [MonoidHom.comp_apply, h1, map_one]
  ·
    obtain ⟨B, hB⟩ := exists_isPlaceOver Ω w
    obtain ⟨τ, -, hτ⟩ := hine B hB
    refine ⟨τ ^ (Multiplicative.toAdd y).val, ?_⟩
    apply Multiplicative.toAdd.injective
    rw [map_pow, toAdd_pow, hτ, nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val]
  ·
    have hq := normV_prime v
    haveI : Fact (normV v).Prime := ⟨hq⟩
    have hne : normV v ≠ normV w := fun h => hvw (eq_of_normV_eq h)
    have hcop : (normV w).Coprime (normV v) := (Nat.coprime_primes hp hq).2 (Ne.symm hne)
    have hBq := val_normV_lt_one hB
    obtain ⟨x, hx⟩ := hx
    have hq0 : ((normV v : ℕ) : ZMod (normV w)) ≠ 0 := by
      rw [Ne, CharP.cast_eq_zero_iff (ZMod (normV w)) (normV w)]
      exact fun h => hne ((Nat.prime_dvd_prime_iff_eq hp hq).1 h).symm
    have hx0 : x ≠ 0 := by
      rintro rfl
      rw [zero_pow (pow_ne_zero _ (Fact.out : l.Prime).ne_zero)] at hx
      exact hq0 hx.symm
    let uq : (ZMod (normV w))ˣ := ZMod.unitOfCoprime (normV v) hcop.symm
    have huq : uq = Units.mk0 x hx0 ^ (l ^ n) := by
      ext
      simp [uq, hx]
    have hfq : f uq = 1 := by rw [huq, map_pow, pow_self_eq_one]
    intro g hg
    obtain ⟨k, hk⟩ := UpperTheory.V.LDataCardLeFinrank.decActRoots ℚ Ω (normV v) B hBq (normV w) hcop g hg
    have hcls : Chr.cls ℚ Ω (normV w) g = uq ^ k := by
      refine (Chr.clsFacts ℚ Ω (normV w)).2.2.1 g (uq ^ k) fun ζ hζ => ?_
      rw [hk ζ hζ, Units.val_pow_eq_pow_val, ZMod.coe_unitOfCoprime, ← Nat.cast_pow, ZMod.val_natCast,
        ← pow_eq_pow_mod _ hζ]
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, hcls, map_pow, hfq, one_pow]

end GlobalTheory.Ord2.PrimeChar
