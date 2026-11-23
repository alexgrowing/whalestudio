import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ExistsAvoidOne
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.PartialSum
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeightedSumDecompositionDenominatorsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RayClassParametrizationExistsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PrimeNotDividingCoprimeIdealNormStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsLargePrimeInRayClassStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AbsNormModEqOfRayRelPowModStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RayRelAntitoneModulusAndPowModStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConeSeriesSpecialValueRationalStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConeZetaSpecialValueDenominatorBoundStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RayClassPartialZetaIntegralityStatement
import Development.WeilBound.CoreStatements.AutomorphicKernels.DeligneRibet.WeightedSummability.WeightedSummable

set_option autoImplicit false

noncomputable section

open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

namespace PositivityTheory.PfDRL

theorem classValueZ : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔣 𝔞 𝔟 𝔠 : Ideal (𝓞 F)) (J : Type) [Fintype J]
    (r : J → ℕ) (y : J → 𝓞 F) (v : ∀ j, Fin (r j) → 𝓞 F), ClassParam 𝔣 𝔞 𝔟 r y v → 𝔠.IsPrime → (Ideal.absNorm 𝔠).Prime →
    (∀ j i, v j i ∉ 𝔠 * 𝔟) → ∀ T : ℂ → ℂ, DifferentiableOn ℂ T {1}ᶜ →
      (∀ s : ℂ, 1 < s.re → HasSum (fun I : {I : Ideal (𝓞 F) // CoprimeTo F 𝔣 I ∧ RayRel F 𝔣 I 𝔞} =>
        (classWeight (Ideal.absNorm 𝔠) 𝔠 I.1 : ℂ) * ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s)) (T s)) →
      ∀ k : ℕ, 1 ≤ k → ∃ q : ℚ, T (1 - (k : ℂ)) = (q : ℂ) ∧
        ∀ l : ℕ, l.Prime → l ≠ Ideal.absNorm 𝔠 → ¬ l ∣ Ideal.absNorm 𝔟 → 0 ≤ padicValRat l q := GlobalTheory.T.ray_class_partial_zeta_integrality

theorem classParamCop : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔣 : Ideal (𝓞 F)), 𝔣 ≠ ⊥ →
    ∀ 𝔞 : Ideal (𝓞 F), CoprimeTo F 𝔣 𝔞 →
      ∃ (𝔟 : Ideal (𝓞 F)) (J : Type) (_ : Fintype J) (r' : J → ℕ) (y : J → 𝓞 F) (v' : ∀ j, Fin (r' j) → 𝓞 F),
        ClassParam 𝔣 𝔞 𝔟 r' y v' ∧ 𝔟 ⊔ 𝔣 = ⊤ := GlobalTheory.T.ray_class_parametrization_exists

theorem not_dvd_absNorm {F : Type} [Field F] [NumberField F] {l : ℕ} (hl : l.Prime) {𝔟 : Ideal (𝓞 F)}
    (h : 𝔟 ⊔ Ideal.span {(l : 𝓞 F)} = ⊤) : ¬ l ∣ Ideal.absNorm 𝔟 := GlobalTheory.T.prime_not_dividing_coprime_ideal_norm F l hl 𝔟 h

theorem deg1Ray : ∀ (F : Type) [Field F] [NumberField F] (𝔣 𝔞 : Ideal (𝓞 F)), 𝔣 ≠ ⊥ → CoprimeTo F 𝔣 𝔞 →
    ∀ (W : Finset (𝓞 F)) (B : ℕ), (∀ x ∈ W, x ≠ 0) →
      ∃ 𝔠 : Ideal (𝓞 F), 𝔠.IsPrime ∧ (Ideal.absNorm 𝔠).Prime ∧ B < Ideal.absNorm 𝔠 ∧ CoprimeTo F 𝔣 𝔠 ∧
        RayRel F 𝔣 𝔠 𝔞 ∧ ∀ x ∈ W, x ∉ 𝔠 := GlobalTheory.T.exists_large_prime_in_ray_class

theorem absNorm_modEq (F : Type) [Field F] [NumberField F] (l m : ℕ) {I J : Ideal (𝓞 F)}
    (h : RayRel F (powMod F l m) I J) : Ideal.absNorm I ≡ Ideal.absNorm J [MOD l ^ m] := GlobalTheory.T.absNorm_modEq_pow_of_rayRel_powMod F l m I J h

theorem rayRel_mono {F : Type} [Field F] [NumberField F] {𝔣 𝔣' I J : Ideal (𝓞 F)} (h : 𝔣' ≤ 𝔣) (hr : RayRel F 𝔣' I J) :
    RayRel F 𝔣 I J := (GlobalTheory.T.rayRel_antitone_modulus_and_powMod F).1 𝔣 𝔣' I J h hr

theorem powMod_le {F : Type} [Field F] [NumberField F] (l : ℕ) {n m : ℕ} (h : n ≤ m) : powMod F l m ≤ powMod F l n := (GlobalTheory.T.rayRel_antitone_modulus_and_powMod F).2 l n m h

theorem smoothed : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔣 : Ideal (𝓞 F)), 𝔣 ≠ ⊥ →
    ∀ (S : Finset (Ideal (𝓞 F))), (∀ a ∈ S, CoprimeTo F 𝔣 a) → (∀ a ∈ S, ∀ b ∈ S, RayRel F 𝔣 a b → a = b) →
      (∀ I, CoprimeTo F 𝔣 I → ∃ a ∈ S, RayRel F 𝔣 I a) → ∀ Z : S → ℂ → ℂ, (∀ c, IsRayZeta 𝔣 c.1 (Z c)) →
      ∃ W : Finset (𝓞 F), (∀ x ∈ W, x ≠ 0) ∧ ∀ 𝔠 : Ideal (𝓞 F), 𝔠.IsPrime → (Ideal.absNorm 𝔠).Prime → 𝔠 ⊔ 𝔣 = ⊤ →
        (∀ x ∈ W, x ∉ 𝔠) → ∃ τ : Equiv.Perm S, (∀ c, RayRel F 𝔣 (𝔠 * (τ c).1) c.1) ∧
          ∀ k : ℕ, 1 ≤ k → ∀ c, ∃ q : ℚ,
            ((Ideal.absNorm 𝔠 : ℕ) : ℂ) ^ k * Z (τ c) (1 - (k : ℂ)) - Z c (1 - (k : ℂ)) = (q : ℂ) ∧
            ∀ l : ℕ, l.Prime → l ≠ Ideal.absNorm 𝔠 → 𝔣 ≤ Ideal.span {(l : 𝓞 F)} → 0 ≤ padicValRat l q := PositivityTheory.PfDR.h_smooth.smoothed_of classValueZ classParamCop not_dvd_absNorm

theorem val_add_nonneg {l : ℕ} [Fact l.Prime] {x y : ℚ} (hx : 0 ≤ padicValRat l x)
    (hy : 0 ≤ padicValRat l y) : 0 ≤ padicValRat l (x + y) := by
  by_cases h : x + y = 0
  · simp [h]
  · exact le_trans (le_min hx hy) (padicValRat.min_le_padicValRat_add h)

theorem val_mul_nonneg {l : ℕ} [Fact l.Prime] {x y : ℚ} (hx : 0 ≤ padicValRat l x)
    (hy : 0 ≤ padicValRat l y) : 0 ≤ padicValRat l (x * y) := by
  by_cases h0 : x = 0
  · simp [h0]
  by_cases h1 : y = 0
  · simp [h1]
  rw [padicValRat.mul h0 h1]
  exact add_nonneg hx hy

theorem val_sum_nonneg {l : ℕ} [Fact l.Prime] {ι : Type*} (s : Finset ι) (f : ι → ℚ)
    (h : ∀ i ∈ s, 0 ≤ padicValRat l (f i)) : 0 ≤ padicValRat l (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact val_add_nonneg (h i (Finset.mem_insert_self i s))
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem isRayL_sum {F : Type} [Field F] [NumberField F] {𝔣 : Ideal (𝓞 F)} {S : Finset (Ideal (𝓞 F))}
    (hS : ∀ a ∈ S, CoprimeTo F 𝔣 a) (hd : ∀ a ∈ S, ∀ b ∈ S, RayRel F 𝔣 a b → a = b)
    (hc : ∀ I, CoprimeTo F 𝔣 I → ∃ a ∈ S, RayRel F 𝔣 I a) {Z : S → ℂ → ℂ} (hZ : ∀ c, IsRayZeta 𝔣 c.1 (Z c))
    {ε : Ideal (𝓞 F) → ℚ} (hε : IsRayFun 𝔣 ε) :
    IsRayL 𝔣 ε (fun s => ∑ c : S, (ε c.1 : ℂ) * Z c s) := by
  classical
  have hZ' : ∀ c : S, IsRayL 𝔣 (rayIndicator 𝔣 c.1) (Z c) := fun c => isRayZeta_iff.1 (hZ c)
  have hind : ∀ I : {I : Ideal (𝓞 F) // CoprimeTo F 𝔣 I},
      ∑ c : S, (ε c.1 : ℂ) * ((rayIndicator 𝔣 c.1 I.1 : ℚ) : ℂ) = (ε I.1 : ℂ) := by
    intro I
    obtain ⟨a, ha, hIa⟩ := hc I.1 I.2
    rw [Finset.sum_eq_single (⟨a, ha⟩ : S)]
    · have : ε a = ε I.1 := hε _ _ (hS a ha) I.2 (rayRel_symm hIa)
      simp [rayIndicator, hIa, this]
    · intro b _ hb
      have : ¬ RayRel F 𝔣 I.1 b.1 := fun h =>
        hb (Subtype.ext (hd _ b.2 _ ha (rayRel_trans (rayRel_symm h) hIa)))
      simp [rayIndicator, this]
    · simp
  refine ⟨?_, fun s hs => ?_⟩
  · intro s hs
    refine DifferentiableWithinAt.fun_sum fun c _ => ?_
    exact (differentiableWithinAt_const _).mul ((hZ' c).1 s hs)
  · have h1 := hasSum_sum (s := Finset.univ) fun c (_ : c ∈ (Finset.univ : Finset S)) =>
      ((hZ' c).2 s hs).mul_left (ε c.1 : ℂ)
    have he : (fun I : {I : Ideal (𝓞 F) // CoprimeTo F 𝔣 I} => (ε I.1 : ℂ) * ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s)) =
        fun I => ∑ c : S, (ε c.1 : ℂ) * (((rayIndicator 𝔣 c.1 I.1 : ℚ) : ℂ) * ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s)) := by
      funext I
      rw [← hind I, Finset.sum_mul]
      exact Finset.sum_congr rfl fun c _ => by ring
    rw [he]
    exact h1

theorem value_eq {F : Type} [Field F] [NumberField F] {𝔣 : Ideal (𝓞 F)} {S : Finset (Ideal (𝓞 F))}
    (hS : ∀ a ∈ S, CoprimeTo F 𝔣 a) (hd : ∀ a ∈ S, ∀ b ∈ S, RayRel F 𝔣 a b → a = b)
    (hc : ∀ I, CoprimeTo F 𝔣 I → ∃ a ∈ S, RayRel F 𝔣 I a) {Z : S → ℂ → ℂ} (hZ : ∀ c, IsRayZeta 𝔣 c.1 (Z c))
    {ε : Ideal (𝓞 F) → ℚ} (hε : IsRayFun 𝔣 ε) {k : ℕ} (hk : 1 ≤ k) {z : S → ℚ}
    (hz : ∀ c, Z c (1 - (k : ℂ)) = (z c : ℂ)) {r : ℚ} (hr : IsRayValue 𝔣 ε k r) :
    r = ∑ c : S, ε c.1 * z c := by
  have h := hr.eq hk (isRayL_sum hS hd hc hZ hε)
  simp only [hz] at h
  have h' : ((∑ c : S, ε c.1 * z c : ℚ) : ℂ) = (r : ℂ) := by push_cast; exact h
  exact_mod_cast h'.symm

theorem deligneRibet : GlobalTheory.Published.DeligneRibet := by
  classical
  intro F _ _ _ l _ n hn ε hε hint 𝔠 h𝔠 k hk r r' hr hr'
  have hl : l.Prime := Fact.out
  have h𝔣 : powMod F l n ≠ ⊥ := powMod_ne_bot hl.ne_zero n
  obtain ⟨S, hS, hd, hc⟩ := GlobalTheory.T.ray_class_group_finite_representatives F (powMod F l n) h𝔣
  obtain ⟨Z, hZ⟩ := exists_classZeta F (powMod F l n) h𝔣 S hS hd hc
  choose z hz using fun c : S => (hZ c).2 k hk
  have hZ1 : ∀ c : S, IsRayZeta (powMod F l n) c.1 (Z c) := fun c => (hZ c).1
  have hrv : r = ∑ c : S, ε c.1 * z c := value_eq hS hd hc hZ1 hε hk hz hr
  have hrv' : r' = ∑ c : S, ε (𝔠 * c.1) * z c := value_eq hS hd hc hZ1 (hε.translate h𝔠) hk hz hr'
  set m : ℕ := n + (padicValRat l r').natAbs with hm
  have hnm : n ≤ m := Nat.le_add_right _ _
  have hm1 : 1 ≤ m := le_trans hn hnm
  have h𝔣' : powMod F l m ≠ ⊥ := powMod_ne_bot hl.ne_zero m
  obtain ⟨W, hW0, hW⟩ := smoothed F (powMod F l n) h𝔣 S hS hd hc Z hZ1
  have h𝔠m : CoprimeTo F (powMod F l m) 𝔠 := (coprimeTo_powMod_iff hm1).2 ((coprimeTo_powMod_iff hn).1 h𝔠)
  obtain ⟨𝔠', hpr, hNp, hB, h𝔠'm, hrel, hav⟩ := deg1Ray F (powMod F l m) 𝔠 h𝔣' h𝔠m W l hW0
  have h𝔠'n : CoprimeTo F (powMod F l n) 𝔠' := (coprimeTo_powMod_iff hn).2 ((coprimeTo_powMod_iff hm1).1 h𝔠'm)
  obtain ⟨τ, hτ, hq⟩ := hW 𝔠' hpr hNp h𝔠'n.2 hav
  have hlN : l ≠ Ideal.absNorm 𝔠' := hB.ne
  have hfl : powMod F l n ≤ Ideal.span {(l : 𝓞 F)} := by
    unfold powMod
    rw [Ideal.span_singleton_le_span_singleton]
    exact dvd_pow_self _ (by omega)
  choose q hqv hqval using fun c => hq k hk c
  have hqeq : ∀ c, (Ideal.absNorm 𝔠' : ℚ) ^ k * z (τ c) - z c = q c := by
    intro c
    have h := hqv c
    rw [hz (τ c), hz c] at h
    exact_mod_cast h
  have heq : ∀ c : S, ε (𝔠 * (τ c).1) = ε c.1 := by
    intro c
    have h1 : RayRel F (powMod F l n) 𝔠 𝔠' := rayRel_symm (rayRel_mono (powMod_le l hnm) hrel)
    have h2 : RayRel F (powMod F l n) ((τ c).1 * 𝔠) ((τ c).1 * 𝔠') := rayRel_mul_left _ h1
    rw [mul_comm (τ c).1 𝔠, mul_comm (τ c).1 𝔠'] at h2
    exact hε _ _ (coprimeTo_mul h𝔠 (hS _ (τ c).2)) (hS _ c.2) (rayRel_trans h2 (hτ c))
  have hr'τ : r' = ∑ c : S, ε c.1 * z (τ c) := by
    rw [hrv']
    refine (Fintype.sum_equiv τ _ _ fun c => ?_).symm
    show ε c.1 * z (τ c) = ε (𝔠 * (τ c).1) * z (τ c)
    rw [heq c]
  have hA : r - (Ideal.absNorm 𝔠' : ℚ) ^ k * r' = -∑ c : S, ε c.1 * q c := by
    rw [hrv, hr'τ, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← hqeq c]
    ring
  have hAval : 0 ≤ padicValRat l (r - (Ideal.absNorm 𝔠' : ℚ) ^ k * r') := by
    rw [hA, padicValRat.neg]
    refine val_sum_nonneg _ _ fun c _ => val_mul_nonneg ?_ ?_
    · exact inZl_iff.1 (hint _ (hS _ c.2))
    · exact hqval c l hl hlN hfl
  have hmod : Ideal.absNorm 𝔠' ^ k ≡ Ideal.absNorm 𝔠 ^ k [MOD l ^ m] := (absNorm_modEq F l m hrel).pow k
  obtain ⟨t, ht⟩ := (Nat.modEq_iff_dvd.1 hmod.symm)
  have hB' : 0 ≤ padicValRat l (((Ideal.absNorm 𝔠' : ℚ) ^ k - (Ideal.absNorm 𝔠 : ℚ) ^ k) * r') := by
    have hcast : (Ideal.absNorm 𝔠' : ℚ) ^ k - (Ideal.absNorm 𝔠 : ℚ) ^ k = (l : ℚ) ^ m * (t : ℚ) := by
      have h := congrArg (fun x : ℤ => (x : ℚ)) ht
      push_cast at h
      exact h
    rw [hcast]
    by_cases ht0 : t = 0
    · simp [ht0]
    by_cases hr0 : r' = 0
    · simp [hr0]
    have hl0 : (l : ℚ) ≠ 0 := by exact_mod_cast hl.ne_zero
    have ht0' : (t : ℚ) ≠ 0 := by exact_mod_cast ht0
    have hlm : padicValRat l ((l : ℚ) ^ m) = m := by
      rw [show ((l : ℚ) ^ m) = ((l ^ m : ℕ) : ℚ) by push_cast; rfl, padicValRat.of_nat, padicValNat.prime_pow]
    rw [mul_assoc, padicValRat.mul (pow_ne_zero _ hl0) (mul_ne_zero ht0' hr0), padicValRat.mul ht0' hr0, hlm]
    have hv : 0 ≤ padicValRat l (t : ℚ) := by
      rw [padicValRat.of_int]
      exact Nat.cast_nonneg _
    have key : -(padicValRat l r') ≤ ((padicValRat l r').natAbs : ℤ) := by
      rw [← Int.natAbs_neg]
      exact Int.le_natAbs
    have hmz : (m : ℤ) = (n : ℤ) + ((padicValRat l r').natAbs : ℤ) := by
      rw [hm]
      push_cast
      ring
    rw [hmz]
    have hn0 : (0 : ℤ) ≤ n := Nat.cast_nonneg _
    linarith
  rw [inZl_iff]
  have hsplit : r - (Ideal.absNorm 𝔠 : ℚ) ^ k * r' = (r - (Ideal.absNorm 𝔠' : ℚ) ^ k * r') +
      ((Ideal.absNorm 𝔠' : ℚ) ^ k - (Ideal.absNorm 𝔠 : ℚ) ^ k) * r' := by ring
  rw [hsplit]
  exact val_add_nonneg hAval hB'

end PositivityTheory.PfDRL
