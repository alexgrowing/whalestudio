import Mathlib
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Statements
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.ChartGlueLoc
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.ChartGlueSat
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open ReciprocityTheory.ChartRestriction.G.Geo

section Generic

variable {Ω : Type} [Field Ω] {τ : Type} {x : τ → Ω} {r : ℕ} {E : Type} [AddCommGroup E] [Module Ω E]

end Generic

section Glue

variable {Ω : Type} [Field Ω] {τ : Type} {x : τ → Ω} {r : ℕ}
  {E : Type} [AddCommGroup E] [Module Ω E] {S : Finset Nat.Primes}
  {o₀ : Type} [CommRing o₀] [Algebra ℤ o₀] [IsLocalization.Away (primeProd S) o₀] [Algebra o₀ Ω]
  {o : S → Type} [∀ p, CommRing (o p)] [∀ p, Algebra ℤ (o p)]
  [∀ p : S, IsLocalization.AtPrime (o p) (Ideal.span {(((p : Nat.Primes) : ℕ) : ℤ)})]
  [∀ p, Algebra (o p) Ω]

abbrev primeTo (p : Nat.Primes) : Submonoid ℤ := (Ideal.span {((p : ℕ) : ℤ)}).primeCompl

theorem mem_primeTo {p : Nat.Primes} {s : ℤ} : s ∈ primeTo p ↔ ¬ ((p : ℕ) : ℤ) ∣ s := by
  show s ∉ Ideal.span _ ↔ _
  rw [Ideal.mem_span_singleton]

instance (p : S) : IsLocalization (primeTo (p : Nat.Primes)) (o p) := inferInstance

variable (x) in

theorem inv_mem_chartRing_at (p : S) (i : τ) {s : ℤ} (hs : ¬ (((p : Nat.Primes) : ℕ) : ℤ) ∣ s) :
    (s : Ω) ≠ 0 ∧ (s : Ω)⁻¹ ∈ chartRing (o p) x i :=
  inv_mem_chartRing_loc x i (o p) (primeTo (p : Nat.Primes)) (mem_primeTo.2 hs)

variable (x o₀) in

theorem inv_prod_mem_chartRing (i : τ) :
    ((primeProd S : ℤ) : Ω) ≠ 0 ∧ ((primeProd S : ℤ) : Ω)⁻¹ ∈ chartRing o₀ x i :=
  inv_mem_chartRing_loc x i o₀ (Submonoid.powers (primeProd S)) (Submonoid.mem_powers _)

def primeProdErase (S : Finset Nat.Primes) (p : Nat.Primes) : ℤ := ∏ q ∈ S.erase p, ((q : ℕ) : ℤ)

theorem primeProd_eq_mul {p : Nat.Primes} (hp : p ∈ S) :
    primeProd S = ((p : ℕ) : ℤ) * primeProdErase S p :=
  (Finset.mul_prod_erase S (fun q : Nat.Primes => ((q : ℕ) : ℤ)) hp).symm

theorem dvd_primeProd {p : Nat.Primes} (hp : p ∈ S) : ((p : ℕ) : ℤ) ∣ primeProd S :=
  ⟨_, primeProd_eq_mul hp⟩

theorem dvd_primeProdErase {p q : Nat.Primes} (hq : q ∈ S) (hqp : q ≠ p) :
    ((q : ℕ) : ℤ) ∣ primeProdErase S p :=
  Finset.dvd_prod_of_mem _ (Finset.mem_erase.2 ⟨hqp, hq⟩)

theorem not_dvd_primeProdErase (p : Nat.Primes) : ¬ ((p : ℕ) : ℤ) ∣ primeProdErase S p := by
  intro h
  obtain ⟨q, hq, hpq⟩ := (Prime.dvd_finsetProd_iff (Nat.prime_iff_prime_int.mp p.2) _).1 h
  have : (p : ℕ) = q := (Nat.prime_dvd_prime_iff_eq p.2 q.2).1 (Int.natCast_dvd_natCast.1 hpq)
  exact (Finset.mem_erase.1 hq).1 (Subtype.ext this).symm

theorem not_dvd_prime_of_ne {p q : Nat.Primes} (h : q ≠ p) : ¬ ((p : ℕ) : ℤ) ∣ ((q : ℕ) : ℤ) := by
  intro hd
  have : (p : ℕ) = q := (Nat.prime_dvd_prime_iff_eq p.2 q.2).1 (Int.natCast_dvd_natCast.1 hd)
  exact h (Subtype.ext this).symm

variable (x o₀) in

theorem inv_prime_mem_chartRing {p : Nat.Primes} (hp : p ∈ S) (i : τ) :
    (((p : ℕ) : ℤ) : Ω)⁻¹ ∈ chartRing o₀ x i := by
  obtain ⟨hm0, hm⟩ := inv_prod_mem_chartRing x o₀ (S := S) i
  have h : (((p : ℕ) : ℤ) : Ω)⁻¹ = (primeProdErase S p : Ω) * ((primeProd S : ℤ) : Ω)⁻¹ := by
    rw [primeProd_eq_mul hp] at hm0 ⊢
    push_cast at hm0 ⊢
    have h1 : ((p : ℕ) : Ω) ≠ 0 := fun h => hm0 (by rw [h, zero_mul])
    have h2 : (primeProdErase S p : Ω) ≠ 0 := fun h => hm0 (by rw [h, mul_zero])
    field_simp
  rw [h]
  exact mul_mem (intCast_mem_chartRing x i o₀ _) hm

theorem smul_mem_of_chart {R : Type*} [CommRing R] [Algebra R Ω] (B : ChartBundle R x r E) {i : τ}
    {a : Ω} (ha : a ∈ chartRing R x i) {e : E} (he : e ∈ B.lat i) : a • e ∈ B.lat i :=
  B.stable i a ha e he

theorem intCast_smul_mem {R : Type*} [CommRing R] [Algebra R Ω] (B : ChartBundle R x r E) {i : τ}
    (z : ℤ) {e : E} (he : e ∈ B.lat i) : (z : Ω) • e ∈ B.lat i :=
  B.stable i _ (intCast_mem_chartRing x i R z) e he

variable (B₀ : ChartBundle o₀ x r E) (Bp : ∀ p, ChartBundle (o p) x r E)

def glueLat (i : τ) : AddSubgroup E := B₀.lat i ⊓ ⨅ p, (Bp p).lat i

theorem mem_glueLat {i : τ} {e : E} :
    e ∈ glueLat B₀ Bp i ↔ e ∈ B₀.lat i ∧ ∀ p, e ∈ (Bp p).lat i := by
  simp [glueLat, AddSubgroup.mem_inf, AddSubgroup.mem_iInf]

variable {B₀ Bp}

theorem exists_prime_pow_smul_mem {i : τ} (p : S)
    (hSR : SameRationalSpan (B₀.lat i) ((Bp p).lat i)) {w : E} (hw : w ∈ B₀.lat i) :
    ∃ k : ℕ, ((((p : Nat.Primes) : ℕ) : ℤ) : Ω) ^ k • w ∈ (Bp p).lat i := by
  obtain ⟨N, hN0, hN⟩ := hSR.1 w hw
  obtain ⟨k, n', hn', hN'⟩ := Nat.exists_eq_pow_mul_and_not_dvd hN0.ne' ((p : Nat.Primes) : ℕ)
    (p : Nat.Primes).2.one_lt.ne'
  refine ⟨k, ?_⟩
  have hs : ¬ (((p : Nat.Primes) : ℕ) : ℤ) ∣ (n' : ℤ) := fun h => hn' (Int.natCast_dvd_natCast.1 h)
  obtain ⟨hs0, hsinv⟩ := inv_mem_chartRing_at (o := o) x p i hs
  have : ((((p : Nat.Primes) : ℕ) : ℤ) : Ω) ^ k • w = ((n' : ℤ) : Ω)⁻¹ • ((N : Ω) • w) := by
    rw [smul_smul, hN']
    congr 1
    push_cast at hs0 ⊢
    field_simp
  rw [this, Nat.cast_smul_eq_nsmul]
  exact smul_mem_of_chart (Bp p) hsinv hN

theorem exists_pow_smul_mem_all {i : τ} (hSR : ∀ p, SameRationalSpan (B₀.lat i) ((Bp p).lat i))
    {w : E} (hw : w ∈ B₀.lat i) (z : ℤ) (P : S → Prop)
    (hz : ∀ p, P p → (((p : Nat.Primes) : ℕ) : ℤ) ∣ z) :
    ∃ K : ℕ, ∀ K' ≥ K, ∀ p, P p → ((z : Ω) ^ K') • w ∈ (Bp p).lat i := by
  classical
  choose k hk using fun p => exists_prime_pow_smul_mem p (hSR p) hw
  refine ⟨Finset.univ.sup k, fun K' hK' p hp => ?_⟩
  obtain ⟨c, hc⟩ := hz p hp
  have hle : k p ≤ K' := le_trans (Finset.le_sup (Finset.mem_univ p)) hK'
  have : ((z : Ω) ^ K') • w =
      ((z : Ω) ^ (K' - k p) * (c : Ω) ^ k p) • ((((p : Nat.Primes) : ℕ) : ℤ) : Ω) ^ k p • w := by
    rw [smul_smul]
    congr 1
    rw [hc, Int.cast_mul, mul_assoc, ← mul_pow, mul_comm (c : Ω), ← Int.cast_mul, ← hc,
      pow_sub_mul_pow _ hle]
  rw [this]
  exact smul_mem_of_chart (Bp p) (mul_mem (pow_mem (intCast_mem_chartRing x i _ _) _)
    (pow_mem (intCast_mem_chartRing x i _ _) _)) (hk p)

theorem mem_B₀_iff {i : τ} (hSR : ∀ p, SameRationalSpan (B₀.lat i) ((Bp p).lat i)) (v : E) :
    v ∈ B₀.lat i ↔ ∃ n : ℕ, primeProd S ^ n • v ∈ glueLat B₀ Bp i := by
  constructor
  · intro hv
    obtain ⟨K, hK⟩ := exists_pow_smul_mem_all hSR hv (primeProd S) (fun _ => True)
      (fun p _ => dvd_primeProd p.2)
    refine ⟨K, (mem_glueLat B₀ Bp).2 ⟨?_, fun p => ?_⟩⟩
    · rw [← Int.cast_smul_eq_zsmul Ω, Int.cast_pow]
      exact smul_mem_of_chart B₀ (pow_mem (intCast_mem_chartRing x i _ _) _) hv
    · rw [← Int.cast_smul_eq_zsmul Ω, Int.cast_pow]
      exact hK K le_rfl p trivial
  · rintro ⟨n, hn⟩
    have h0 := ((mem_glueLat B₀ Bp).1 hn).1
    rw [← Int.cast_smul_eq_zsmul Ω, Int.cast_pow] at h0
    obtain ⟨hm0, hm⟩ := inv_prod_mem_chartRing x o₀ (S := S) i
    have : v = (((primeProd S : ℤ) : Ω)⁻¹) ^ n • (((primeProd S : ℤ) : Ω) ^ n • v) := by
      rw [smul_smul, ← mul_pow, inv_mul_cancel₀ hm0, one_pow, one_smul]
    rw [this]
    exact smul_mem_of_chart B₀ (pow_mem hm _) h0

theorem mem_Bp_iff [CharZero Ω] {i : τ} (hSR : ∀ p, SameRationalSpan (B₀.lat i) ((Bp p).lat i)) (p : S) (v : E) :
    v ∈ (Bp p).lat i ↔ ∃ s : ℤ, ¬ (((p : Nat.Primes) : ℕ) : ℤ) ∣ s ∧ s • v ∈ glueLat B₀ Bp i := by
  constructor
  · intro hv
    obtain ⟨N, hN0, hN⟩ := (hSR p).2 v hv
    obtain ⟨k, n', hn', hN'⟩ := Nat.exists_eq_pow_mul_and_not_dvd hN0.ne' ((p : Nat.Primes) : ℕ)
      (p : Nat.Primes).2.one_lt.ne'
    have hw : ((n' : ℤ) : Ω) • v ∈ B₀.lat i := by
      have : ((n' : ℤ) : Ω) • v =
          ((((p : Nat.Primes) : ℕ) : ℤ) : Ω)⁻¹ ^ k • ((N : Ω) • v) := by
        rw [smul_smul, hN']
        congr 1
        have : (((p : Nat.Primes) : ℕ) : Ω) ≠ 0 := Nat.cast_ne_zero.2 (p : Nat.Primes).2.ne_zero
        push_cast
        rw [inv_pow, mul_comm ((((p : Nat.Primes) : ℕ) : Ω) ^ k), ← mul_assoc, mul_comm _ (n' : Ω),
          mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ this), mul_one]
      rw [this, Nat.cast_smul_eq_nsmul]
      exact smul_mem_of_chart B₀ (pow_mem (inv_prime_mem_chartRing x o₀ p.2 i) _) hN
    obtain ⟨K, hK⟩ := exists_pow_smul_mem_all hSR hw (primeProdErase S p) (fun q => q ≠ p)
      (fun q hq => dvd_primeProdErase q.2 (fun h => hq (Subtype.ext h)))
    have hs : ¬ (((p : Nat.Primes) : ℕ) : ℤ) ∣ (n' * primeProdErase S p ^ K) := by
      rw [(Nat.prime_iff_prime_int.mp (p : Nat.Primes).2).dvd_mul]
      rintro (h | h)
      · exact hn' (Int.natCast_dvd_natCast.1 h)
      · exact not_dvd_primeProdErase _ ((Nat.prime_iff_prime_int.mp (p : Nat.Primes).2).dvd_of_dvd_pow h)
    refine ⟨n' * primeProdErase S p ^ K, hs, ?_⟩
    rw [← Int.cast_smul_eq_zsmul Ω]
    have heq : (((n' * primeProdErase S p ^ K : ℤ)) : Ω) • v =
        ((primeProdErase S p : Ω) ^ K) • (((n' : ℤ) : Ω) • v) := by
      rw [smul_smul]; congr 1; push_cast; ring
    refine (mem_glueLat B₀ Bp).2 ⟨?_, fun q => ?_⟩
    · rw [heq]
      exact smul_mem_of_chart B₀ (pow_mem (intCast_mem_chartRing x i _ _) _) hw
    · by_cases hq : q = p
      · subst hq
        exact intCast_smul_mem (Bp q) _ hv
      · rw [heq]
        exact hK K le_rfl q hq
  · rintro ⟨s, hs, hsv⟩
    have h0 := ((mem_glueLat B₀ Bp).1 hsv).2 p
    rw [← Int.cast_smul_eq_zsmul Ω] at h0
    obtain ⟨hs0, hsinv⟩ := inv_mem_chartRing_at (o := o) x p i hs
    have : v = ((s : Ω)⁻¹) • ((s : Ω) • v) := by
      rw [smul_smul, inv_mul_cancel₀ hs0, one_smul]
    rw [this]
    exact smul_mem_of_chart (Bp p) hsinv h0

theorem glueLat_stable (i : τ) (a : Ω) (ha : a ∈ chartRing ℤ x i) (e : E)
    (he : e ∈ glueLat B₀ Bp i) : a • e ∈ glueLat B₀ Bp i := by
  obtain ⟨h0, hp⟩ := (mem_glueLat B₀ Bp).1 he
  exact (mem_glueLat B₀ Bp).2 ⟨B₀.stable i a (mem_chartRing_of_int x i o₀ ha) e h0,
    fun p => (Bp p).stable i a (mem_chartRing_of_int x i (o p) ha) e (hp p)⟩

theorem glueLat_overlap (i j : τ) (hi : x i ≠ 0) (hj : x j ≠ 0) (e : E)
    (he : e ∈ glueLat B₀ Bp i) : ∃ m : ℕ, (x i / x j) ^ m • e ∈ glueLat B₀ Bp j := by
  classical
  obtain ⟨h0, hp⟩ := (mem_glueLat B₀ Bp).1 he
  obtain ⟨m₀, hm₀⟩ := B₀.overlap i j hi hj e h0
  choose mp hmp using fun p => (Bp p).overlap i j hi hj e (hp p)
  refine ⟨max m₀ (Finset.univ.sup mp), (mem_glueLat B₀ Bp).2 ⟨?_, fun p => ?_⟩⟩
  · rw [← pow_sub_mul_pow _ (le_max_left m₀ (Finset.univ.sup mp)), mul_smul]
    exact smul_mem_of_chart B₀ (pow_mem (div_mem_chartRing x j i) _) hm₀
  · have hle : mp p ≤ max m₀ (Finset.univ.sup mp) :=
      le_trans (Finset.le_sup (Finset.mem_univ p)) (le_max_right _ _)
    rw [← pow_sub_mul_pow _ hle, mul_smul]
    exact smul_mem_of_chart (Bp p) (pow_mem (div_mem_chartRing x j i) _) (hmp p)

end Glue

end GroundTheory.Heights₂.Heights.Model
