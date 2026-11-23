import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ResidualConstruction
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes
import Formalism.FrobeniusOrbits.RealSubfieldLeCompositum
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicCharInertiaSurjectiveStatement
import Development.AutomorphicArithmetic.PrimeDiscriminants.CycImage
import Development.AutomorphicArithmetic.CyclotomicBounds.FactorizationConductorLeLocalLevel
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices

namespace GlobalTheory.TameFixedLift

open Pointwise

theorem transfer {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [Algebra ℚ Ω]
    (A : ValuationSubring Ω) (l : ℕ) [Fact l.Prime] (σ : G ℚ Ω) (hσ : σ ∈ Ine (F := ℚ) A)
    (hfix : ∀ x : E, σ (algebraMap E Ω x) = algebraMap E Ω x) :
    ∃ g ∈ Ine (F := E) A, cycZ (F := E) (Ω := Ω) l g = cycZ (F := ℚ) (Ω := Ω) l σ := by
  refine ⟨AlgEquiv.ofRingEquiv (f := (σ : Ω ≃+* Ω)) hfix, ⟨?_, hσ.2⟩, rfl⟩
  have h : σ • A = A := hσ.1
  exact h

theorem root_fix {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω] (l : ℕ) [Fact l.Prime] (n : ℕ)
    (σ : G ℚ Ω) (u : ℤ_[l])
    (h : ((cycZ (F := ℚ) (Ω := Ω) l σ : ℤ_[l]ˣ) : ℤ_[l]) = 1 + (l : ℤ_[l]) ^ n * u)
    (t : Ω) (ht : t ^ l ^ n = 1) : σ t = t := by
  have : CharZero Ω := algebraRat.charZero Ω
  have : ∀ i : ℕ, NeZero ((l ^ i : ℕ) : Ω) := fun i =>
    ⟨by exact_mod_cast pow_ne_zero i (Fact.out : l.Prime).ne_zero⟩
  have h1 := cyclotomicCharacter.spec l (n := n) (σ : Ω ≃+* Ω) t ht
  have h2 : ((cyclotomicCharacter Ω l (σ : Ω ≃+* Ω) : ℤ_[l]ˣ) : ℤ_[l]) = 1 + (l : ℤ_[l]) ^ n * u := h
  have h3 : PadicInt.toZModPow n ((l : ℤ_[l]) ^ n) = 0 := by
    rw [← RingHom.mem_ker, PadicInt.ker_toZModPow]; exact Ideal.mem_span_singleton_self _
  rw [h2, map_add, map_mul, h3, zero_mul, add_zero, map_one] at h1
  have h4 : t ^ (1 : ZMod (l ^ n)).val = t := by
    rw [ZMod.val_one_eq_one_mod, ← pow_eq_pow_mod 1 ht, pow_one]
  rw [h4] at h1
  exact h1

theorem exists_place (E : Type) [Field E] [NumberField E] (l : ℕ) [Fact l.Prime] :
    ∃ w, w ∈ placesOver E l := by
  have hl : l.Prime := Fact.out
  have hnu : Ideal.span {(l : 𝓞 E)} ≠ ⊤ := by
    intro h
    have h1 := congrArg Ideal.absNorm h
    rw [Ideal.absNorm_span_natCast, Ideal.absNorm_top] at h1
    rcases Nat.pow_eq_one.mp h1 with h2 | h2
    · exact hl.one_lt.ne' h2
    · exact Module.finrank_pos.ne' h2
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hnu
  have hmem : (l : 𝓞 E) ∈ M := hle (Ideal.mem_span_singleton_self _)
  refine ⟨⟨M, hM.isPrime, ?_⟩, hmem⟩
  rintro rfl
  rw [Ideal.mem_bot] at hmem
  exact hl.ne_zero (by exact_mod_cast hmem)

private theorem eq_one_of_cong {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {l m : ℕ}
    (hA : A.valuation (l : Ω) < 1) (hc : Nat.Coprime m l) {z : Ω} (hz : z ^ m = 1)
    (h1 : A.valuation (z - 1) < 1) : z = 1 := by
  by_contra hne
  have hint : ∀ n : ℤ, A.valuation (n : Ω) ≤ 1 := fun n =>
    (A.valuation_le_one_iff _).mpr (intCast_mem A n)
  have hz1 : A.valuation z ≤ 1 := by
    have := Valuation.map_add_le A.valuation h1.le (le_of_eq (map_one A.valuation))
    simpa using this
  have hp : ∀ i : ℕ, A.valuation (z ^ i - 1) < 1 := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      rw [show z ^ (i + 1) - 1 = (z ^ i - 1) * z + (z - 1) by ring]
      refine Valuation.map_add_lt _ ?_ h1
      rw [map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_right' hz1) ih
  have hs : ∑ i ∈ Finset.range m, z ^ i = 0 := by
    have := mul_geom_sum z m
    rw [hz, sub_self] at this
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hne)
  have hm : A.valuation (m : Ω) < 1 := by
    have h2 : A.valuation (∑ i ∈ Finset.range m, (z ^ i - 1)) < 1 :=
      Valuation.map_sum_lt _ one_ne_zero fun i _ => hp i
    rw [Finset.sum_sub_distrib, hs] at h2
    simpa using h2
  have hb : (1 : Ω) = (m : Ω) * ((Nat.gcdA m l : ℤ) : Ω) + (l : Ω) * ((Nat.gcdB m l : ℤ) : Ω) := by
    have h3 := Nat.gcd_eq_gcd_ab m l
    rw [hc.gcd_eq_one] at h3
    exact_mod_cast congrArg (Int.cast : ℤ → Ω) h3
  have h4 : A.valuation ((m : Ω) * ((Nat.gcdA m l : ℤ) : Ω) + (l : Ω) * ((Nat.gcdB m l : ℤ) : Ω)) < 1 := by
    refine Valuation.map_add_lt _ ?_ ?_ <;> rw [map_mul]
    · exact lt_of_le_of_lt (mul_le_of_le_one_right' (hint _)) hm
    · exact lt_of_le_of_lt (mul_le_of_le_one_right' (hint _)) hA
  rw [← hb, map_one] at h4
  exact lt_irrefl _ h4

private theorem tame_fix {Ω : Type} [Field Ω] [Algebra ℚ Ω] (A : ValuationSubring Ω) {l m : ℕ}
    (hA : A.valuation (l : Ω) < 1) (hm : m ≠ 0) (hc : Nat.Coprime m l) (σ : G ℚ Ω) (hσ : σ ∈ Ine (F := ℚ) A)
    (z : Ω) (hz : z ^ m = 1) : σ z = z := by
  have hv : A.valuation z = 1 := by
    have := congrArg A.valuation hz
    rw [map_pow, map_one] at this
    exact (pow_eq_one_iff_of_nonneg zero_le hm).mp this
  have hz0 : z ≠ 0 := by rintro rfl; simp at hv
  have h3 : A.valuation (σ z - z) < 1 := hσ.2 z hv.le
  have h4 : σ z / z = 1 := eq_one_of_cong A hA hc
    (by rw [div_pow, ← map_pow, hz, map_one, div_one]) (by
      rw [show σ z / z - 1 = (σ z - z) / z by field_simp, map_div₀, hv, div_one]
      exact h3)
  exact (div_eq_one_iff_eq hz0).mp h4

private theorem loc_fix {R : Ranks} (H : Host R) {Ω : Type} [Field Ω] [Algebra H.E Ω] [Algebra ℚ Ω]
    [IsAlgClosed Ω] (A : ValuationSubring Ω) {l : ℕ} (hl : l.Prime) (hA : A.valuation (l : Ω) < 1)
    (σ : G ℚ Ω) (hσ : σ ∈ Ine (F := ℚ) A)
    (hroot : ∀ t : Ω, t ^ l ^ H.condN.factorization l = 1 → σ t = t) (x : H.E) :
    σ (algebraMap H.E Ω x) = algebraMap H.E Ω x := by
  have hN : H.condN ≠ 0 := H.condN_ne_zero
  refine H.image_mem_of_roots (algebraMap H.E Ω) (RingHom.eqLocusField (σ : Ω →+* Ω) (RingHom.id Ω))
    (fun y hy => ?_) x
  show σ y = y
  have hy0 : y ≠ 0 := by rintro rfl; simp [hN] at hy
  have hmul := Nat.ordProj_mul_ordCompl_eq_self H.condN l
  have hco : Nat.Coprime l (ordCompl[l] H.condN) := Nat.coprime_ordCompl hl hN
  have h1 := hroot (y ^ ordCompl[l] H.condN) (by rw [← pow_mul, mul_comm, hmul, hy])
  have h2 := tame_fix A hA (Nat.ordCompl_pos l hN).ne' hco.symm σ hσ (y ^ ordProj[l] H.condN)
    (by rw [← pow_mul, hmul, hy])
  rw [map_pow] at h1 h2
  have h3 : (σ y / y) ^ Nat.gcd (ordProj[l] H.condN) (ordCompl[l] H.condN) = 1 :=
    pow_gcd_eq_one.2 ⟨by rw [div_pow, h2, div_self (pow_ne_zero _ hy0)],
      by rw [div_pow, h1, div_self (pow_ne_zero _ hy0)]⟩
  rw [(Nat.Coprime.pow_left _ hco).gcd_eq_one, pow_one] at h3
  exact (div_eq_one_iff_eq hy0).mp h3

theorem main : ∀ {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (i : N.Loc) , ∃ w ∈ placesOver H.E (N.l i), ∀ u : ℤ_[N.l i], ∃ g ∈ Ine (F := H.E) (N.plOm.1 w), ((cycZ (F := H.E) (Ω := N.Om) (N.l i) g : ℤ_[N.l i]ˣ) : ℤ_[N.l i]) = 1 + (N.l i : ℤ_[N.l i]) ^ N.s0 i * u := by
  intro R H what₂ N i
  obtain ⟨w, hw⟩ := exists_place H.E (N.l i)
  refine ⟨w, hw, fun u => ?_⟩
  have : CharZero N.Om := charZero_of_injective_algebraMap (algebraMap H.E N.Om).injective
  have : IsAlgClosed N.Om := IsAlgClosure.isAlgClosed H.E
  have : IsScalarTower ℚ H.E N.Om := IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
  have : IsAlgClosure ℚ N.Om := IsAlgClosure.ofAlgebraic ℚ H.E N.Om
  have hA : (N.plOm.1 w).valuation (N.l i : N.Om) < 1 := by
    have := (N.plOm.2 w (N.l i : 𝓞 H.E)).2 hw
    simpa using this
  have hs : 1 ≤ N.s0 i := UpperTheory.KStar.S0.one_le_localLevel N i
  have hunit : IsUnit (1 + (N.l i : ℤ_[N.l i]) ^ N.s0 i * u) := by
    have hm : -((N.l i : ℤ_[N.l i]) ^ N.s0 i * u) ∈ IsLocalRing.maximalIdeal ℤ_[N.l i] := by
      rw [PadicInt.maximalIdeal_eq_span_p, neg_mem_iff, Ideal.mem_span_singleton]
      exact Dvd.dvd.mul_right (dvd_pow_self _ (by omega)) _
    have := IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _ hm
    simpa using this
  obtain ⟨σ, hσ, hv⟩ := GlobalTheory.T.cyclotomicChar_inertia_surjective N.Om (N.l i) (N.plOm.1 w) hA hunit.unit
  have hv' : ((cycZ (F := ℚ) (Ω := N.Om) (N.l i) σ : ℤ_[N.l i]ˣ) : ℤ_[N.l i]) =
      1 + (N.l i : ℤ_[N.l i]) ^ N.s0 i * u := by rw [hv]; rfl
  obtain ⟨k, hk⟩ := pow_dvd_pow (N.l i) (UpperTheory.KStar.S0.factorization_conductor_le_localLevel N i)
  obtain ⟨g, hg, hc⟩ := transfer (E := H.E) (N.plOm.1 w) (N.l i) σ hσ
    (loc_fix H _ (N.lPrime i).out hA σ hσ fun t ht =>
      root_fix (N.l i) (N.s0 i) σ u hv' t (by rw [hk, pow_mul, ht, one_pow]))
  exact ⟨g, hg, by rw [hc, hv']⟩

end GlobalTheory.TameFixedLift
