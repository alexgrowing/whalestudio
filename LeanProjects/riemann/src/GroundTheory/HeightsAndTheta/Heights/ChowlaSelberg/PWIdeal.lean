import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.Statements
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.PWIdealField
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.PWIdealPrimes
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.PWIdealPrincipal
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ChowlaSelberg

open NumberField GroundTheory.Global GroundTheory.Global.Elliptic
open scoped nonZeroDivisors

noncomputable section

variable {K : Type} [Field K] [NumberField K]

def WIdealAt (σ : K →+* ℂ) (L : PeriodPair) (𝔞 : (Ideal (𝓞 K))⁰) : Prop :=
  IsAlgebraic ℚ (discrRatio σ L.lattice (FractionalIdeal.mk0 K 𝔞)) ∧
    ∀ (F : Type) [Field F] [NumberField F] (ι : K →+* F) (τ : F →+* ℂ), τ.comp ι = σ →
      discrRatio σ L.lattice (FractionalIdeal.mk0 K 𝔞) ∈ Set.range τ →
        ∃ w : 𝓞 F, τ (w : F) = discrRatio σ L.lattice (FractionalIdeal.mk0 K 𝔞) ∧
          Ideal.span {w} = Ideal.map (RingOfIntegers.mapRingHom ι) (𝔞 : Ideal (𝓞 K)) ^ 12

theorem mapRingHom_injective {F F' : Type*} [Field F] [Field F'] (ι : F →+* F') :
    Function.Injective (RingOfIntegers.mapRingHom ι) := fun x y h ↦
  RingOfIntegers.ext (ι.injective (by simpa using congrArg (fun t : 𝓞 F' ↦ (t : F')) h))

omit [NumberField K] in
theorem map_ne_bot {F : Type} [Field F] [NumberField F] (ι : K →+* F) (𝔞 : (Ideal (𝓞 K))⁰) (n : ℕ) :
    Ideal.map (RingOfIntegers.mapRingHom ι) (𝔞 : Ideal (𝓞 K)) ^ n ≠ ⊥ := by
  have h0 : Ideal.map (RingOfIntegers.mapRingHom ι) (𝔞 : Ideal (𝓞 K)) ≠ ⊥ := by
    rw [ne_eq, Ideal.map_eq_bot_iff_of_injective (mapRingHom_injective ι)]
    exact nonZeroDivisors.coe_ne_zero 𝔞
  rw [← Ideal.zero_eq_bot] at h0 ⊢
  exact pow_ne_zero n h0

theorem wIdealAt_span (σ : K →+* ℂ) (L : PeriodPair) (hL : latticeEnd L = cmRing σ) (a : 𝓞 K)
    (ha : a ≠ 0) : WIdealAt σ L (spanNZ a ha) := by
  rw [WIdealAt, discrRatio_span_singleton σ L hL a ha]
  refine ⟨?_, fun F _ _ ι τ hτ _ ↦ ?_⟩
  · have hi : IsIntegral ℤ (σ (algebraMap (𝓞 K) K a)) :=
      (RingOfIntegers.isIntegral_coe a).map σ.toIntAlgHom
    exact (hi.pow 12).tower_top.isAlgebraic
  · refine ⟨RingOfIntegers.mapRingHom ι a ^ 12, ?_, ?_⟩
    · rw [← hτ]
      simp
    · rw [← Ideal.span_singleton_pow]
      congr 1
      show Ideal.span {RingOfIntegers.mapRingHom ι a} =
        Ideal.map (RingOfIntegers.mapRingHom ι) (Ideal.span {a})
      rw [Ideal.map_span, Set.image_singleton]

theorem wIdealAt_mul [Algebra.IsQuadraticExtension ℚ K] {S : PrimeDiscriminant K}
    (hC : WCocycle.Statement S) (σ : K →+* ℂ) (L : PeriodPair) (hL : latticeEnd L = cmRing σ)
    (𝔞 𝔭 : (Ideal (𝓞 K))⁰) (L' : PeriodPair)
    (hL' : L'.lattice = idealLattice σ ↑(FractionalIdeal.mk0 K 𝔞)⁻¹ * L.lattice)
    (h₁ : WIdealAt σ L 𝔞) (h₂ : WIdealAt σ L' 𝔭) : WIdealAt σ L (𝔞 * 𝔭) := by
  have hw : discrRatio σ L.lattice (FractionalIdeal.mk0 K (𝔞 * 𝔭)) =
      discrRatio σ L.lattice (FractionalIdeal.mk0 K 𝔞) *
        discrRatio σ L'.lattice (FractionalIdeal.mk0 K 𝔭) := by
    rw [map_mul, hC σ L hL, hL']
  obtain ⟨a₁, i₁⟩ := h₁
  obtain ⟨a₂, i₂⟩ := h₂
  refine ⟨hw ▸ a₁.mul a₂, fun F _ _ ι τ hτ hmem ↦ ?_⟩
  obtain ⟨F', _, _, j, τ', hτ', ⟨v₁, hv₁⟩, ⟨v₂, hv₂⟩⟩ := exists_extension_mem_range τ a₁ a₂
  have hτ'σ : τ'.comp (j.comp ι) = σ := by rw [← RingHom.comp_assoc, hτ', hτ]
  obtain ⟨u₁, hu₁, s₁⟩ := i₁ F' (j.comp ι) τ' hτ'σ ⟨v₁, hv₁⟩
  obtain ⟨u₂, hu₂, s₂⟩ := i₂ F' (j.comp ι) τ' hτ'σ ⟨v₂, hv₂⟩
  obtain ⟨v, hv⟩ := hmem
  have hjv : j v = ((u₁ * u₂ : 𝓞 F') : F') := by
    apply τ'.injective
    rw [← RingHom.comp_apply, hτ', hv, hw, ← hu₁, ← hu₂]
    simp
  have hvint : IsIntegral ℤ v :=
    isIntegral_of_map j (by rw [hjv]; exact RingOfIntegers.isIntegral_coe _)
  obtain ⟨v', hv'⟩ : ∃ v' : 𝓞 F, (v' : F) = v := ⟨⟨v, (mem_integralClosure_iff ℤ F).2 hvint⟩, rfl⟩
  refine ⟨v', by rw [hv']; exact hv, ?_⟩
  apply eq_of_map_eq j (map_ne_bot ι (𝔞 * 𝔭) 12)
  have hcomp : RingOfIntegers.mapRingHom (j.comp ι) =
      (RingOfIntegers.mapRingHom j).comp (RingOfIntegers.mapRingHom ι) := by
    ext x
    rfl
  have hj : RingOfIntegers.mapRingHom j v' = u₁ * u₂ :=
    RingOfIntegers.ext (by rw [RingOfIntegers.mapRingHom_apply, hv', hjv])
  rw [Ideal.map_span, Set.image_singleton, Ideal.map_pow, Ideal.map_map, ← hcomp, hj,
    ← Ideal.span_singleton_mul_span_singleton, s₁, s₂, ← mul_pow, ← Ideal.map_mul]
  rfl

theorem wIdealAt_split [Algebra.IsQuadraticExtension ℚ K] {S : PrimeDiscriminant K}
    [IsTotallyComplex K] (hC : WCocycle.Statement S) (hU : WUnitOffPrime.Statement S)
    (σ : K →+* ℂ) (L : PeriodPair) (hL : latticeEnd L = cmRing σ) (p : ℕ) (hp : p.Prime)
    (𝔭 𝔮 : (Ideal (𝓞 K))⁰) (h𝔭 : (𝔭 : Ideal (𝓞 K)).IsPrime) (h𝔮 : (𝔮 : Ideal (𝓞 K)).IsPrime)
    (hN𝔭 : Ideal.absNorm (𝔭 : Ideal (𝓞 K)) = p) (hN𝔮 : Ideal.absNorm (𝔮 : Ideal (𝓞 K)) = p)
    (hpq : (𝔭 : Ideal (𝓞 K)) * 𝔮 = Ideal.span {(p : 𝓞 K)})
    (hne : (𝔮 : Ideal (𝓞 K)) ≠ 𝔭) : WIdealAt σ L 𝔭 := by
  obtain ⟨L', hL'lat, hL'⟩ :=
    exists_lattice_mul σ (Algebra.IsQuadraticExtension.finrank_eq_two ℚ K) L hL (FractionalIdeal.mk0 K 𝔭)
  have hp0 : (p : 𝓞 K) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  have hprod : discrRatio σ L.lattice (FractionalIdeal.mk0 K 𝔭) *
      discrRatio σ L'.lattice (FractionalIdeal.mk0 K 𝔮) = (p : ℂ) ^ 12 := by
    have e : 𝔭 * 𝔮 = spanNZ (p : 𝓞 K) hp0 := Subtype.ext hpq
    have h := hC σ L hL (FractionalIdeal.mk0 K 𝔭) (FractionalIdeal.mk0 K 𝔮)
    rw [← map_mul, e, discrRatio_span_singleton σ L hL, ← hL'lat] at h
    rw [← h]
    simp
  have U₁ := hU σ L hL 𝔭 h𝔭 (hN𝔭 ▸ hp)
  have U₂ := hU σ L' hL' 𝔮 h𝔮 (hN𝔮 ▸ hp)
  have hw₁ : discrRatio σ L.lattice (FractionalIdeal.mk0 K 𝔭) ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hprod
    exact pow_ne_zero 12 (Nat.cast_ne_zero.2 hp.ne_zero) hprod.symm
  refine ⟨U₁.1, fun F _ _ ι τ hτ hmem ↦ ?_⟩
  have hmem₂ : discrRatio σ L'.lattice (FractionalIdeal.mk0 K 𝔮) ∈ Set.range τ := by
    obtain ⟨v, hv⟩ := hmem
    refine ⟨(p : F) ^ 12 / v, ?_⟩
    rw [map_div₀, map_pow, map_natCast, hv, ← hprod]
    field_simp
  obtain ⟨u₁, hu₁, hQ₁⟩ := U₁.2 F ι τ hτ hmem
  obtain ⟨u₂, hu₂, hQ₂⟩ := U₂.2 F ι τ hτ hmem₂
  refine ⟨u₁, hu₁, ?_⟩
  set f := RingOfIntegers.mapRingHom ι
  set P := Ideal.map f (𝔭 : Ideal (𝓞 K))
  set Q := Ideal.map f (𝔮 : Ideal (𝓞 K))
  have hu : u₁ * u₂ = (p : 𝓞 F) ^ 12 := by
    apply RingOfIntegers.ext
    apply τ.injective
    simp [hu₁, hu₂, hprod]
  have hAB : Ideal.span {u₁} * Ideal.span {u₂} = P ^ 12 * Q ^ 12 := by
    rw [Ideal.span_singleton_mul_span_singleton, hu, ← Ideal.span_singleton_pow, ← mul_pow,
      ← Ideal.map_mul, hpq, Ideal.map_span, Set.image_singleton, map_natCast]
  have h𝔭0 : (𝔭 : Ideal (𝓞 K)) ≠ ⊥ := by rw [← Ideal.zero_eq_bot]; exact nonZeroDivisors.coe_ne_zero 𝔭
  have h𝔮0 : (𝔮 : Ideal (𝓞 K)) ≠ ⊥ := by rw [← Ideal.zero_eq_bot]; exact nonZeroDivisors.coe_ne_zero 𝔮
  have hPQ : P ⊔ Q = ⊤ := by
    rw [← Ideal.map_sup, Ideal.IsMaximal.coprime_of_ne (h𝔭.isMaximal h𝔭0) (h𝔮.isMaximal h𝔮0)
      (Ne.symm hne), Ideal.map_top]
  have hcop : ∀ (u : 𝓞 F) (R T : Ideal (𝓞 F)), R ⊔ T = ⊤ →
      (∀ M : Ideal (𝓞 F), M.IsMaximal → ¬ R ≤ M → u ∉ M) → Ideal.span {u} ⊔ T = ⊤ := by
    intro u R T hRT hu
    by_contra h
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ h
    have huM : u ∈ M := hle (Ideal.mem_sup_left (Ideal.mem_span_singleton_self u))
    have hRM : R ≤ M := by
      by_contra hR
      exact hu M hM hR huM
    have hTM : T ≤ M := le_trans le_sup_right hle
    exact hM.ne_top (top_le_iff.1 (hRT ▸ sup_le hRM hTM))
  have hAQ : IsCoprime (Ideal.span {u₁}) (Q ^ 12) :=
    (Ideal.isCoprime_iff_sup_eq.2 (hcop u₁ P Q hPQ hQ₁)).pow_right
  have hBP : IsCoprime (Ideal.span {u₂}) (P ^ 12) :=
    (Ideal.isCoprime_iff_sup_eq.2 (hcop u₂ Q P (by rw [sup_comm]; exact hPQ) hQ₂)).pow_right
  obtain ⟨X, hX⟩ : Ideal.span {u₁} ∣ P ^ 12 :=
    hAQ.dvd_of_dvd_mul_right (hAB ▸ dvd_mul_right _ _)
  obtain ⟨Y, hY⟩ : Ideal.span {u₂} ∣ Q ^ 12 :=
    hBP.dvd_of_dvd_mul_left (hAB ▸ dvd_mul_left _ _)
  have hne0 : Ideal.span {u₁} * Ideal.span {u₂} ≠ 0 := by
    rw [hAB, Ideal.zero_eq_bot]
    have := map_ne_bot ι (𝔭 * 𝔮) 12
    rwa [Submonoid.coe_mul, Ideal.map_mul, mul_pow] at this
  have hXY : X * Y = 1 := by
    have e : Ideal.span {u₁} * Ideal.span {u₂} * (X * Y) = Ideal.span {u₁} * Ideal.span {u₂} * 1 := by
      rw [mul_one]
      conv_rhs => rw [hAB, hX, hY]
      ring
    exact mul_left_cancel₀ hne0 e
  have hX1 : X = ⊤ := by
    apply top_le_iff.1
    rw [← Ideal.one_eq_top, ← hXY, mul_comm]
    exact Ideal.mul_le_right
  rw [hX, hX1, Ideal.mul_top]

theorem wIdealAt_prime [Algebra.IsQuadraticExtension ℚ K] {S : PrimeDiscriminant K}
    [IsTotallyComplex K] (hC : WCocycle.Statement S) (hU : WUnitOffPrime.Statement S)
    (σ : K →+* ℂ) (L : PeriodPair) (hL : latticeEnd L = cmRing σ) (𝔭 : (Ideal (𝓞 K))⁰)
    (h𝔭 : (𝔭 : Ideal (𝓞 K)).IsPrime) : WIdealAt σ L 𝔭 := by
  have h𝔭0 : (𝔭 : Ideal (𝓞 K)) ≠ ⊥ := by rw [← Ideal.zero_eq_bot]; exact nonZeroDivisors.coe_ne_zero 𝔭
  rcases prime_cases S.prime S.discr_eq (𝔭 : Ideal (𝓞 K)) h𝔭0 with ⟨a, ha⟩ | ⟨p, hp, hN𝔭, 𝔮, h𝔮, hN𝔮, hpq, hne⟩
  · have ha0 : a ≠ 0 := by
      rintro rfl
      rw [Ideal.span_singleton_eq_bot.2 rfl] at ha
      exact h𝔭0 ha
    have e : 𝔭 = spanNZ a ha0 := Subtype.ext ha
    rw [e]
    exact wIdealAt_span σ L hL a ha0
  · have h𝔮0 : 𝔮 ≠ 0 := by
      rintro rfl
      rw [Ideal.zero_eq_bot, Ideal.absNorm_bot] at hN𝔮
      exact hp.ne_zero hN𝔮.symm
    exact wIdealAt_split hC hU σ L hL p hp 𝔭 ⟨𝔮, mem_nonZeroDivisors_of_ne_zero h𝔮0⟩ h𝔭 h𝔮 hN𝔭
      hN𝔮 hpq hne

theorem WIdeal.proof [Algebra.IsQuadraticExtension ℚ K] (S : PrimeDiscriminant K)
    (hC : WCocycle.Statement S) (hU : WUnitOffPrime.Statement S) : WIdeal.Statement S := by
  have : IsTotallyComplex K := by
    have hd : discr K < 0 := by
      rw [S.discr_eq]
      exact neg_neg_of_pos (by exact_mod_cast S.prime.pos)
    exact nrRealPlaces_eq_zero_iff.1 (Quadratic.places_of_discr_neg K hd).1
  intro σ L hL 𝔞
  suffices H : ∀ I : Ideal (𝓞 K), ∀ hI : I ≠ 0, ∀ L : PeriodPair, latticeEnd L = cmRing σ →
      WIdealAt σ L ⟨I, mem_nonZeroDivisors_of_ne_zero hI⟩ from
    H 𝔞 (nonZeroDivisors.coe_ne_zero 𝔞) L hL
  intro I
  refine UniqueFactorizationMonoid.induction_on_prime I ?_ ?_ ?_
  · intro h
    exact absurd rfl h
  · intro x hx hI L hL
    have e : (⟨x, mem_nonZeroDivisors_of_ne_zero hI⟩ : (Ideal (𝓞 K))⁰) = spanNZ 1 one_ne_zero :=
      Subtype.ext (by show x = Ideal.span {1}; rw [Ideal.isUnit_iff.1 hx, Ideal.span_singleton_one])
    rw [e]
    exact wIdealAt_span σ L hL 1 one_ne_zero
  · intro a 𝔭 ha h𝔭 ih hI L hL
    have h𝔭0 : 𝔭 ≠ 0 := h𝔭.ne_zero
    let A : (Ideal (𝓞 K))⁰ := ⟨a, mem_nonZeroDivisors_of_ne_zero ha⟩
    let P : (Ideal (𝓞 K))⁰ := ⟨𝔭, mem_nonZeroDivisors_of_ne_zero h𝔭0⟩
    have e : (⟨𝔭 * a, mem_nonZeroDivisors_of_ne_zero hI⟩ : (Ideal (𝓞 K))⁰) = A * P :=
      Subtype.ext (mul_comm 𝔭 a)
    obtain ⟨L', hL'lat, hL'⟩ :=
      exists_lattice_mul σ (Algebra.IsQuadraticExtension.finrank_eq_two ℚ K) L hL (FractionalIdeal.mk0 K A)
    rw [e]
    exact wIdealAt_mul hC σ L hL A P L' hL'lat (ih ha L hL)
      (wIdealAt_prime hC hU σ L' hL' P (Ideal.isPrime_of_prime h𝔭))

end

end GroundTheory.Heights₂.Heights.ChowlaSelberg
