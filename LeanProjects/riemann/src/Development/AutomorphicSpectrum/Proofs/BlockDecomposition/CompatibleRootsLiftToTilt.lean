import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ConstantCoeffSurjective
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.GaloisTwistIdentitySection
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SharpSurjectiveKerSpan
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UntiltAdicCompleteStatement
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.MemPow

set_option backward.isDefEq.respectTransparency false

open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

namespace GlobalTheory.CompanionTheory.Untilt

section Adic

variable {R : Type*} [CommRing R]

theorem smodEq_span_pow_iff (π x y : R) (n : ℕ) :
    x ≡ y [SMOD (Ideal.span {π} ^ n • (⊤ : Submodule R R))] ↔ π ^ n ∣ x - y := by
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]

theorem eq_zero_of_forall_pow_dvd {π x : R} (h : IsHausdorff (Ideal.span {π}) R)
    (hx : ∀ n : ℕ, π ^ n ∣ x) : x = 0 :=
  h.haus x fun n => (smodEq_span_pow_iff π x 0 n).2 (by simpa using hx n)

theorem exists_limit_of_pow_dvd {π : R} (h : IsPrecomplete (Ideal.span {π}) R) (f : ℕ → R)
    (hf : ∀ n : ℕ, π ^ n ∣ f (n + 1) - f n) : ∃ L, ∀ n : ℕ, π ^ n ∣ f n - L :=
  _root_.UpperTheory.Reformulated.B.Yra6.main h f hf

theorem pow_pow_of_compatible {M : Type*} [Monoid M] {l : ℕ} {v : ℕ → M}
    (hv : ∀ i, v (i + 1) ^ l = v i) (i j : ℕ) : v (i + j) ^ l ^ j = v i := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ', pow_mul, ← add_assoc, hv, ih]

end Adic

variable {l : ℕ} [Fact l.Prime] (A : PAlg l)

theorem sub_pow_pow (x y : A.A) (j : ℕ) : (x - y) ^ l ^ j = x ^ l ^ j - y ^ l ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ, pow_mul, ih, pow_mul, pow_mul]
    exact map_sub A.frob _ _

theorem exists_limit_pow (b : ℕ → A.A) (hb : ∀ j, A.pi ∣ b (j + 1) ^ l - b j) (i : ℕ) :
    ∃ L, ∀ n : ℕ, A.pi ^ n ∣ b (i + n) ^ l ^ n - L := by
  have hl : 1 < l := (Fact.out : l.Prime).one_lt
  refine exists_limit_of_pow_dvd (π := A.pi) A.compl.toIsPrecomplete
    (fun n => b (i + n) ^ l ^ n) fun n => ?_
  have e : b (i + (n + 1)) ^ l ^ (n + 1) - b (i + n) ^ l ^ n
      = (b (i + n + 1) ^ l - b (i + n)) ^ l ^ n := by
    rw [sub_pow_pow, ← pow_mul, ← pow_succ', add_assoc]
  change A.pi ^ n ∣ b (i + (n + 1)) ^ l ^ (n + 1) - b (i + n) ^ l ^ n
  rw [e]
  exact (pow_dvd_pow _ (Nat.lt_pow_self hl).le).trans (pow_dvd_pow_of_dvd (hb _) _)

theorem exists_compatible_roots_of_sharp : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l) (u : ℕ → A.U),
    (∀ i, u (i + 1) ^ l = u i) →
    ∃ a : ℕ → A.A, (∀ i, a (i + 1) ^ l = a i) ∧ ∀ i, A.sharp (a i) = u i := by
  intro l _ A u hu
  obtain ⟨hsurj, hker⟩ := sharp_map_surjective_ker A
  choose b hb using fun j => hsurj (Ideal.Quotient.mk _ (u j))
  have hbd : ∀ j, A.pi ∣ b (j + 1) ^ l - b j := fun j => by
    rw [← Ideal.mem_span_singleton]
    rw [← hker, RingHom.mem_ker, map_sub, map_pow, hb, hb, ← map_pow, hu, sub_self]
  choose a ha using exists_limit_pow A b hbd
  have hA : IsHausdorff (Ideal.span {A.pi}) A.A := A.compl.toIsHausdorff
  have hroot : ∀ i, a (i + 1) ^ l = a i := fun i => by
    refine sub_eq_zero.1 (eq_zero_of_forall_pow_dvd hA fun n => ?_)
    have h1 : A.pi ^ n ∣ b (i + 1 + n) ^ l ^ (n + 1) - a (i + 1) ^ l := by
      rw [pow_succ, pow_mul]
      exact (ha (i + 1) n).trans (sub_dvd_pow_sub_pow _ _ l)
    have h2 : A.pi ^ n ∣ b (i + 1 + n) ^ l ^ (n + 1) - a i := by
      have := ha i (n + 1)
      rw [show i + (n + 1) = i + 1 + n by ring] at this
      exact (pow_dvd_pow _ (Nat.le_succ n)).trans this
    have := dvd_sub h2 h1
    simpa using this
  have hmod : ∀ i, A.pi ∣ a i - b i := fun i => by
    have h1 := ha i 1
    rw [pow_one, pow_one] at h1
    have := dvd_sub (hbd i) h1
    simpa using this
  have hl1 : ∀ i, (l : A.U) ∣ A.sharp (a i) - u i := fun i => by
    have h0 : A.aToU1 (a i) = A.aToU1 (b i) := by
      rw [← sub_eq_zero, ← map_sub, ← RingHom.mem_ker, hker, Ideal.mem_span_singleton]
      exact hmod i
    rw [hb, sharpMap_eq] at h0
    have := Ideal.Quotient.eq.1 h0
    rwa [pow_one, Ideal.mem_span_singleton] at this
  refine ⟨a, hroot, fun i => sub_eq_zero.1 ?_⟩
  refine eq_zero_of_forall_pow_dvd (π := (l : A.U)) (GlobalTheory.T.untilt_adic_complete A).toIsHausdorff fun n => ?_
  have h1 := dvd_sub_pow_of_dvd_sub (hl1 (i + n)) n
  rw [← map_pow, pow_pow_of_compatible hroot, pow_pow_of_compatible hu] at h1
  exact (pow_dvd_pow _ (Nat.le_succ n)).trans h1

end GlobalTheory.CompanionTheory.Untilt
