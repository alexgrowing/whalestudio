import Mathlib
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.ChartGlueLat
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open ReciprocityTheory.ChartRestriction.G.Geo

section FrameGeneric

variable {Ω : Type} [Field Ω] {E : Type} [AddCommGroup E] [Module Ω E]

def IsFrameAt (A : Subalgebra ℤ Ω) (r : ℕ) (M : AddSubgroup E) (h : Ω) : Prop :=
  ∃ b : Fin r → E, LinearIndependent Ω b ∧ Submodule.span Ω (Set.range b) = ⊤ ∧
    ∀ e, (∃ n : ℕ, h ^ n • e ∈ M) ↔
      ∃ a : Fin r → Ω, (∀ q, ∃ n : ℕ, h ^ n * a q ∈ A) ∧ e = ∑ q, a q • b q

theorem exists_frame_cover (A : Subalgebra ℤ Ω) (r : ℕ) (M : AddSubgroup E)
    (hloc : ∀ Q : Ideal A, Q.IsMaximal →
      ∃ h : Ω, ∃ hh : h ∈ A, (⟨h, hh⟩ : A) ∉ Q ∧ IsFrameAt A r M h) :
    ∃ (k : ℕ) (f c : Fin k → Ω), (∀ l, f l ∈ A) ∧ (∀ l, c l ∈ A) ∧ ∑ l, c l * f l = 1 ∧
      ∀ l, IsFrameAt A r M (f l) := by
  let H : Set A := {h | IsFrameAt A r M h}
  have htop : Ideal.span H = ⊤ := by
    by_contra hne
    obtain ⟨Q, hQ, hle⟩ := Ideal.exists_le_maximal _ hne
    obtain ⟨h, hh, hQh, hfr⟩ := hloc Q hQ
    exact hQh (hle (Ideal.subset_span (show (⟨h, hh⟩ : A) ∈ H from hfr)))
  have h1 : (1 : A) ∈ Ideal.span H := by rw [htop]; exact Submodule.mem_top
  obtain ⟨k, c, g, hcg⟩ := Submodule.mem_span_set'.1 h1
  refine ⟨k, fun l => ((g l : A) : Ω), fun l => (c l : Ω), fun l => (g l : A).2, fun l => (c l).2,
    ?_, fun l => (g l).2⟩
  have := congrArg Subtype.val hcg
  simpa using this

theorem mem_ideal_of_sum {A : Subalgebra ℤ Ω} (Q : Ideal A) {k : ℕ} (a y : Fin k → Ω)
    (ha : ∀ l, a l ∈ A) (hy : ∀ l, y l ∈ A) (hyQ : ∀ l, (⟨y l, hy l⟩ : A) ∈ Q) {z : Ω}
    (hz : z ∈ A) (hsum : ∑ l, a l * y l = z) : (⟨z, hz⟩ : A) ∈ Q := by
  have : (⟨z, hz⟩ : A) = ∑ l, (⟨a l, ha l⟩ : A) * ⟨y l, hy l⟩ := Subtype.ext (by simp [← hsum])
  rw [this]
  exact Q.sum_mem fun l _ => Q.mul_mem_left _ (hyQ l)

theorem intCast_subtype (A : Subalgebra ℤ Ω) (z : ℤ) :
    (⟨(z : Ω), intCast_mem A z⟩ : A) = (z : A) :=
  Subtype.ext (by simp)

theorem mem_of_prime_pow_mul_mem {A : Subalgebra ℤ Ω} {p : ℕ} (hp : p.Prime) {s : ℤ}
    (hs : ¬ (p : ℤ) ∣ s) (N : ℕ) {y : Ω} (h1 : (((p : ℤ) : Ω)) ^ N * y ∈ A)
    (h2 : (s : Ω) * y ∈ A) : y ∈ A := by
  have hcop : IsCoprime ((p : ℤ) ^ N) s := by
    have : IsCoprime (p : ℤ) s := by
      rw [Int.isCoprime_iff_gcd_eq_one]
      have : ¬ p ∣ s.natAbs := fun h => hs (Int.natCast_dvd.mpr h)
      simpa [Int.gcd] using (Nat.Prime.coprime_iff_not_dvd hp).mpr this
    exact this.pow_left
  obtain ⟨u, v, huv⟩ := hcop
  have : y = (u : Ω) * ((((p : ℤ) : Ω)) ^ N * y) + (v : Ω) * ((s : Ω) * y) := by
    have h := congrArg (Int.cast : ℤ → Ω) huv
    push_cast at h ⊢
    linear_combination (-y) * h
  rw [this]
  exact add_mem (mul_mem (intCast_mem A u) h1) (mul_mem (intCast_mem A v) h2)

end FrameGeneric

section FrameGlue

variable {Ω : Type} [Field Ω] {τ : Type} {x : τ → Ω} {r : ℕ}
  {E : Type} [AddCommGroup E] [Module Ω E] {S : Finset Nat.Primes}
  {o₀ : Type} [CommRing o₀] [Algebra ℤ o₀] [IsLocalization.Away (primeProd S) o₀] [Algebra o₀ Ω]
  {o : S → Type} [∀ p, CommRing (o p)] [∀ p, Algebra ℤ (o p)]
  [∀ p : S, IsLocalization.AtPrime (o p) (Ideal.span {(((p : Nat.Primes) : ℕ) : ℤ)})]
  [∀ p, Algebra (o p) Ω]
  {B₀ : ChartBundle o₀ x r E} {Bp : ∀ p, ChartBundle (o p) x r E}

theorem frame_away {i : τ} (hi : x i ≠ 0)
    (hSR : ∀ p, SameRationalSpan (B₀.lat i) ((Bp p).lat i)) (Q : Ideal (chartRing ℤ x i))
    (hQ : Q.IsPrime) (hmQ : ((primeProd S : ℤ) : chartRing ℤ x i) ∉ Q) :
    ∃ h : Ω, ∃ hh : h ∈ chartRing ℤ x i, (⟨h, hh⟩ : chartRing ℤ x i) ∉ Q ∧
      IsFrameAt (chartRing ℤ x i) r (glueLat B₀ Bp i) h := by
  classical
  set m : ℤ := primeProd S with hm
  obtain ⟨hm0, hminv⟩ := inv_prod_mem_chartRing x o₀ (S := S) i
  obtain ⟨k, f, c, hf, hc, hsum, hb⟩ := B₀.frame i hi
  obtain ⟨t, ht, htf⟩ := exists_mul_mem_chartRing_int_fin x i o₀ (Submonoid.powers m) f hf
  obtain ⟨t', ht', htc⟩ := exists_mul_mem_chartRing_int_fin x i o₀ (Submonoid.powers m) c hc
  obtain ⟨J, rfl⟩ := (Submonoid.mem_powers_iff _ _).1 ht
  obtain ⟨J', rfl⟩ := (Submonoid.mem_powers_iff _ _).1 ht'
  have hmA : (m : Ω) ∈ chartRing ℤ x i := intCast_mem (chartRing ℤ x i) m
  have hJ : ∀ l, (m : Ω) ^ J * f l ∈ chartRing ℤ x i := fun l => by simpa using htf l
  have hφ : ∀ l, (m : Ω) ^ (J + 1) * f l ∈ chartRing ℤ x i := fun l => by
    have : (m : Ω) ^ (J + 1) * f l = (m : Ω) * ((m : Ω) ^ J * f l) := by ring
    rw [this]; exact mul_mem hmA (hJ l)
  have hex : ∃ l, (⟨(m : Ω) ^ (J + 1) * f l, hφ l⟩ : chartRing ℤ x i) ∉ Q := by
    by_contra hall
    push Not at hall
    have hmem := mem_ideal_of_sum Q (fun l => ((m ^ J' : ℤ) : Ω) * c l)
      (fun l => (m : Ω) ^ (J + 1) * f l) htc hφ hall (z := ((m ^ (J + 1 + J') : ℤ) : Ω))
      (intCast_mem (chartRing ℤ x i) _) (by
        have : ∑ l, ((m ^ J' : ℤ) : Ω) * c l * ((m : Ω) ^ (J + 1) * f l) =
            ((m : Ω) ^ J' * (m : Ω) ^ (J + 1)) * ∑ l, c l * f l := by
          rw [Finset.mul_sum]; push_cast; exact Finset.sum_congr rfl fun l _ => by ring
        rw [this, hsum]; push_cast; ring)
    rw [intCast_subtype] at hmem
    push_cast at hmem
    exact hmQ (hQ.mem_of_pow_mem _ hmem)
  obtain ⟨l, hl⟩ := hex
  obtain ⟨b, hli, hsp, hiff⟩ := hb l
  refine ⟨_, hφ l, hl, b, hli, hsp, fun e => ?_⟩
  have hYX : ∀ v ∈ B₀.lat i, ∃ k : ℕ, (m : Ω) ^ k • v ∈ glueLat B₀ Bp i := fun v hv => by
    obtain ⟨n, hn⟩ := (mem_B₀_iff hSR v).1 hv
    rw [← Int.cast_smul_eq_zsmul Ω, Int.cast_pow] at hn
    exact ⟨n, hn⟩
  rw [exists_pow_smul_mem_iff_of_loc (chartRing ℤ x i) (glueLat B₀ Bp i) (B₀.lat i) J hm0 hmA (hJ l)
    (glueLat_stable i) (fun e he => ((mem_glueLat B₀ Bp).1 he).1)
    (fun e he => smul_mem_of_chart B₀ hminv he) hYX e, hiff e]
  refine exists_congr fun a => and_congr (forall_congr' fun q => ?_) Iff.rfl
  have key := exists_pow_smul_mem_iff_of_loc (E := Ω) (chartRing ℤ x i) (chartRing ℤ x i).toSubring.toAddSubgroup
    (chartRing o₀ x i).toSubring.toAddSubgroup J hm0 hmA (hJ l)
    (fun a ha e he => show a * e ∈ chartRing ℤ x i from mul_mem ha he) (fun y hy => mem_chartRing_of_int x i o₀ hy)
    (fun y hy => show _ * y ∈ chartRing o₀ x i from mul_mem hminv hy)
    (fun y hy => by
      obtain ⟨t, ht, hty⟩ := exists_mul_mem_chartRing_int x i o₀ (Submonoid.powers m) hy
      obtain ⟨K, rfl⟩ := (Submonoid.mem_powers_iff _ _).1 ht
      exact ⟨K, by simpa using hty⟩) (a q)
  simpa [smul_eq_mul] using key.symm

end FrameGlue

end GroundTheory.Heights₂.Heights.Model
