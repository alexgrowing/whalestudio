import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsSncPatchRat
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegAtIsLocalRingIsFractionRingStalk

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.SncBase.Mdl

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase

section Alg

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω]

abbrev chartQ {κ : Type} (x : κ → Ω) (c : κ) : Subalgebra ℚ Ω :=
  Algebra.adjoin ℚ (Set.range fun j => x j / x c)

abbrev invAdj (A : Subalgebra ℚ Ω) (h : Ω) : Subalgebra ℚ Ω :=
  Algebra.adjoin ℚ (insert h⁻¹ (A : Set Ω))

theorem le_invAdj (A : Subalgebra ℚ Ω) (h : Ω) : A ≤ invAdj A h := fun _ ha =>
  Algebra.subset_adjoin (Set.mem_insert_of_mem _ ha)

theorem inv_mem_invAdj (A : Subalgebra ℚ Ω) (h : Ω) : h⁻¹ ∈ invAdj A h :=
  Algebra.subset_adjoin (Set.mem_insert _ _)

theorem exists_mul_pow_mem {A : Subalgebra ℚ Ω} {g : Ω} (hg : g ∈ A) (h0 : g ≠ 0) {s : Ω}
    (hs : s ∈ invAdj A g) : ∃ k : ℕ, s * g ^ k ∈ A := by
  induction hs using Algebra.adjoin_induction with
  | mem a ha =>
    rcases ha with rfl | ha
    · exact ⟨1, by rw [pow_one, inv_mul_cancel₀ h0]; exact A.one_mem⟩
    · exact ⟨0, by simpa using ha⟩
  | algebraMap r => exact ⟨0, by simpa using A.algebraMap_mem r⟩
  | add a b _ _ ha hb =>
    obtain ⟨k, hk⟩ := ha
    obtain ⟨l, hl⟩ := hb
    refine ⟨k + l, ?_⟩
    have : (a + b) * g ^ (k + l) = a * g ^ k * g ^ l + b * g ^ l * g ^ k := by ring
    rw [this]
    exact A.add_mem (A.mul_mem hk (A.pow_mem hg _)) (A.mul_mem hl (A.pow_mem hg _))
  | mul a b _ _ ha hb =>
    obtain ⟨k, hk⟩ := ha
    obtain ⟨l, hl⟩ := hb
    refine ⟨k + l, ?_⟩
    have : a * b * g ^ (k + l) = a * g ^ k * (b * g ^ l) := by ring
    rw [this]
    exact A.mul_mem hk hl

abbrev primeUnder (A : Subalgebra ℚ Ω) (g : Ω) (q : Ideal (invAdj A g)) : Ideal A :=
  q.comap (Subalgebra.inclusion (le_invAdj A g)).toRingHom

theorem mem_primeUnder {A : Subalgebra ℚ Ω} {g : Ω} {q : Ideal (invAdj A g)} {a : A} :
    a ∈ primeUnder A g q ↔ (⟨a, le_invAdj A g a.2⟩ : invAdj A g) ∈ q := Iff.rfl

theorem not_mem_of_isPrime {A : Subalgebra ℚ Ω} {g : Ω} (hg : g ∈ A) (h0 : g ≠ 0) {q : Ideal (invAdj A g)}
    (hq : q.IsPrime) : (⟨g, le_invAdj A g hg⟩ : invAdj A g) ∉ q := by
  intro h
  apply hq.ne_top
  rw [Ideal.eq_top_iff_one]
  have : (⟨g⁻¹, inv_mem_invAdj A g⟩ : invAdj A g) * ⟨g, le_invAdj A g hg⟩ = 1 :=
    Subtype.ext (by simp [h0])
  rw [← this]
  exact q.mul_mem_left _ h

theorem mem_iff_mul_pow {A : Subalgebra ℚ Ω} {g : Ω} (hg : g ∈ A) (h0 : g ≠ 0) {q : Ideal (invAdj A g)}
    (hq : q.IsPrime) (s : invAdj A g) (k : ℕ) (t : A) (ht : (s : Ω) * g ^ k = t) :
    s ∈ q ↔ t ∈ primeUnder A g q := by
  have e : (⟨t, le_invAdj A g t.2⟩ : invAdj A g) = s * (⟨g, le_invAdj A g hg⟩ : invAdj A g) ^ k :=
    Subtype.ext (by simp [ht])
  rw [mem_primeUnder, e]
  constructor
  · exact fun h => q.mul_mem_right _ h
  · intro h
    rcases hq.mem_or_mem h with h | h
    · exact h
    · exact absurd (hq.mem_of_pow_mem _ h) (not_mem_of_isPrime hg h0 hq)

theorem isLocAt_invAdj {A : Subalgebra ℚ Ω} {g : Ω} (hg : g ∈ A) (h0 : g ≠ 0) {q : Ideal (invAdj A g)}
    (hq : q.IsPrime) {R : Subring Ω} (hR : IsLocAt A (primeUnder A g q) R) : IsLocAt (invAdj A g) q R := by
  intro a
  rw [hR a]
  constructor
  · rintro ⟨s, hs, hsa⟩
    exact ⟨⟨s, le_invAdj A g s.2⟩, hs, le_invAdj A g hsa⟩
  · rintro ⟨s, hs, hsa⟩
    obtain ⟨k, hk⟩ := exists_mul_pow_mem hg h0 s.2
    obtain ⟨l, hl⟩ := exists_mul_pow_mem hg h0 hsa
    have hsk : (⟨(s : Ω) * g ^ k, hk⟩ : A) ∉ primeUnder A g q := fun h =>
      hs ((mem_iff_mul_pow hg h0 hq s k ⟨_, hk⟩ rfl).2 h)
    have hgl : (⟨g, hg⟩ : A) ∉ primeUnder A g q := not_mem_of_isPrime hg h0 hq
    have hprime : (primeUnder A g q).IsPrime := Ideal.comap_isPrime _ _
    refine ⟨⟨(s : Ω) * g ^ k, hk⟩ * ⟨g, hg⟩ ^ l, ?_, ?_⟩
    · intro h
      rcases hprime.mem_or_mem h with h | h
      · exact hsk h
      · exact hgl (hprime.mem_of_pow_mem _ h)
    · have e : (((⟨(s : Ω) * g ^ k, hk⟩ * ⟨g, hg⟩ ^ l : A) : Ω)) * a =
          ((s : Ω) * a * g ^ l) * g ^ k := by
        simp only [Subalgebra.coe_mul, Subalgebra.coe_pow]
        ring
      rw [e]
      exact A.mul_mem hl (A.pow_mem hg _)

end Alg

section Pts

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)

theorem unitAt_one (p : Cpt ξ) : unitAt ξ p 1 :=
  ⟨one_ne_zero, (regAt ξ p).one_mem, by simpa using (regAt ξ p).one_mem⟩

variable {ξ}

theorem unitAt_mul {p : Cpt ξ} {a b : Ω} (ha : unitAt ξ p a) (hb : unitAt ξ p b) : unitAt ξ p (a * b) :=
  ⟨mul_ne_zero ha.1 hb.1, (regAt ξ p).mul_mem ha.2.1 hb.2.1, by
    rw [mul_inv]; exact (regAt ξ p).mul_mem ha.2.2 hb.2.2⟩

theorem unitAt_inv {p : Cpt ξ} {a : Ω} (ha : unitAt ξ p a) : unitAt ξ p a⁻¹ :=
  ⟨inv_ne_zero ha.1, ha.2.2, by simpa using ha.2.1⟩

theorem unitAt_pow {p : Cpt ξ} {a : Ω} (ha : unitAt ξ p a) (k : ℕ) : unitAt ξ p (a ^ k) := by
  induction k with
  | zero => simpa using unitAt_one ξ p
  | succ k ih => rw [pow_succ]; exact unitAt_mul ih ha

theorem unitAt_of_mul_left {p : Cpt ξ} {a b : Ω} (h : unitAt ξ p (a * b)) (ha : a ∈ regAt ξ p)
    (hb : b ∈ regAt ξ p) : unitAt ξ p a := by
  have ha0 : a ≠ 0 := left_ne_zero_of_mul h.1
  have hb0 : b ≠ 0 := right_ne_zero_of_mul h.1
  refine ⟨ha0, ha, ?_⟩
  have : a⁻¹ = b * (a * b)⁻¹ := by field_simp
  rw [this]
  exact (regAt ξ p).mul_mem hb h.2.2

theorem unitAt_of_mul_right {p : Cpt ξ} {a b : Ω} (h : unitAt ξ p (a * b)) (ha : a ∈ regAt ξ p)
    (hb : b ∈ regAt ξ p) : unitAt ξ p b :=
  unitAt_of_mul_left (by rwa [mul_comm]) hb ha

theorem not_unitAt_add (hξ : IsCptGen ξ) {p : Cpt ξ} {a b : Ω} (ha : a ∈ regAt ξ p) (hb : b ∈ regAt ξ p)
    (hna : ¬ unitAt ξ p a) (hnb : ¬ unitAt ξ p b) : ¬ unitAt ξ p (a + b) := by
  haveI : IsLocalRing (regAt ξ p) := (regAt_isLocalRing_isFractionRing_stalk X Ω ξ hξ p).1
  have key : ∀ {c : Ω} (hc : c ∈ regAt ξ p), IsUnit (⟨c, hc⟩ : regAt ξ p) ↔ unitAt ξ p c := by
    intro c hc
    constructor
    · rintro ⟨u, hu⟩
      have hu1 : ((u : regAt ξ p) : Ω) = c := congrArg Subtype.val hu
      have h1 : ((u : regAt ξ p) : Ω) * (((u⁻¹ : (regAt ξ p)ˣ) : regAt ξ p) : Ω) = 1 := by
        rw [← Subring.coe_mul, Units.mul_inv, Subring.coe_one]
      have hc0 : c ≠ 0 := by
        intro h0
        rw [hu1, h0, zero_mul] at h1
        exact zero_ne_one h1
      refine ⟨hc0, hc, ?_⟩
      have : c⁻¹ = (((u⁻¹ : (regAt ξ p)ˣ) : regAt ξ p) : Ω) := by
        rw [hu1] at h1
        exact (eq_inv_of_mul_eq_one_right h1).symm
      rw [this]
      exact Subtype.property _
    · rintro ⟨h0, -, hi⟩
      exact IsUnit.of_mul_eq_one ⟨c⁻¹, hi⟩ (Subtype.ext (by simp [h0]))
  intro hab
  have hsum : IsUnit ((⟨a, ha⟩ : regAt ξ p) + ⟨b, hb⟩) := (key ((regAt ξ p).add_mem ha hb)).2 hab
  rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add hsum with h | h
  · exact hna ((key ha).1 h)
  · exact hnb ((key hb).1 h)

variable [CharZero Ω]

theorem Char0.unitAt_natCast {p : Cpt ξ} (hp : Char0 ξ p) {m : ℕ} (hm : m ≠ 0) : unitAt ξ p (m : Ω) := by
  induction m using Nat.recOnMul with
  | zero => exact absurd rfl hm
  | one => simpa using unitAt_one ξ p
  | prime r hr =>
    have := hp r hr
    simpa [InFibre] using this
  | mul a b ha hb =>
    rw [Nat.cast_mul]
    exact unitAt_mul (ha (left_ne_zero_of_mul hm)) (hb (right_ne_zero_of_mul hm))

theorem Char0.algebraMap_mem {p : Cpt ξ} (hp : Char0 ξ p) (r : ℚ) : algebraMap ℚ Ω r ∈ regAt ξ p := by
  have e : algebraMap ℚ Ω r = (r.num : Ω) * ((r.den : Ω))⁻¹ := by
    rw [eq_ratCast, Rat.cast_def, div_eq_mul_inv]
  rw [e]
  exact (regAt ξ p).mul_mem (intCast_mem _ _) (Char0.unitAt_natCast hp r.den_nz).2.2

theorem chartQ_le {κ : Type} {x : κ → Ω} {c : κ} {p : Cpt ξ} (hp : Char0 ξ p) (hc : InChart ξ x c p)
    {s : Ω} (hs : s ∈ chartQ x c) : s ∈ regAt ξ p := by
  induction hs using Algebra.adjoin_induction with
  | mem a ha => obtain ⟨j, rfl⟩ := ha; exact hc.2 j
  | algebraMap r => exact Char0.algebraMap_mem hp r
  | add a b _ _ ha hb => exact (regAt ξ p).add_mem ha hb
  | mul a b _ _ ha hb => exact (regAt ξ p).mul_mem ha hb

theorem invAdj_le {p : Cpt ξ} (hp : Char0 ξ p) {A : Subalgebra ℚ Ω} {h : Ω} (hA : ∀ s ∈ A, s ∈ regAt ξ p)
    (hh : unitAt ξ p h) {s : Ω} (hs : s ∈ invAdj A h) : s ∈ regAt ξ p := by
  induction hs using Algebra.adjoin_induction with
  | mem a ha =>
    rcases ha with rfl | ha
    · exact hh.2.2
    · exact hA _ ha
  | algebraMap r => exact Char0.algebraMap_mem hp r
  | add a b _ _ ha hb => exact (regAt ξ p).add_mem ha hb
  | mul a b _ _ ha hb => exact (regAt ξ p).mul_mem ha hb

end Pts

section Gens

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {N : ℕ}

abbrev ratEval (x : Fin (N + 1) → Ω) (c : Fin (N + 1)) (G : MRing (fun _ : Unit => Fin (N + 1))) : Ω :=
  MvPolynomial.aeval (fun p : (Σ _ : Unit, Fin (N + 1)) => x p.2 / x c) G

def bdGens (ξ : Spec (CommRingCat.of Ω) ⟶ X) (x : Fin (N + 1) → Ω) (B : Set (Cpt ξ)) :
    Set (MRing (fun _ : Unit => Fin (N + 1))) :=
  {G | ∃ d : ℕ, G.IsHomogeneous d ∧ ∀ c', ∀ q ∈ B, InChart ξ x c' q → ¬ unitAt ξ q (ratEval x c' G)}

end Gens

end GlobalTheory.CompanionTheory.Ar.SncBase.Mdl
