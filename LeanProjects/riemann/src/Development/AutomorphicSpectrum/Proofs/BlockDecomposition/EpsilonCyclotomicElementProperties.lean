import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.MapUSharp
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ValuationOfValuationModSquare
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PerfectionIsUnitOfCoeffZero

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

noncomputable section

namespace GlobalTheory.CompanionTheory.EpsFacts

variable {l : ℕ} [Fact l.Prime]

theorem geom_sum_eq_zero {R : Type*} [CommRing R] [IsDomain R] {z : R} {m : ℕ} (h : z ^ m = 1) (h1 : z ≠ 1) :
    ∑ i ∈ Finset.range m, z ^ i = 0 := by
  have e := mul_geom_sum z m
  rw [h, sub_self] at e
  exact (mul_eq_zero.1 e).resolve_left (sub_ne_zero.2 h1)

theorem pow_chain {M : Type*} [Monoid M] {m : ℕ} (e : ℕ → M) (hs : ∀ k, e (k + 1) ^ m = e k) (k j : ℕ) :
    e (k + j) ^ m ^ j = e k := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ m j, mul_comm, pow_mul, ← add_assoc, hs, ih]

theorem prim_chain {M : Type*} [CommMonoid M] (e : ℕ → M) (hs : ∀ k, e (k + 1) ^ l = e k) (h0 : e 0 = 1)
    (h1 : e 1 ≠ 1) (m : ℕ) : IsPrimitiveRoot (e m) (l ^ m) := by
  cases m with
  | zero => simpa [h0] using IsPrimitiveRoot.one
  | succ k =>
    have a : e (k + 1) ^ l ^ k = e 1 := by
      have := pow_chain e hs 1 k
      rwa [add_comm 1 k] at this
    have b : e (k + 1) ^ l ^ (k + 1) = 1 := by
      have := pow_chain e hs 0 (k + 1)
      rwa [zero_add, h0] at this
    have o : orderOf (e (k + 1)) = l ^ (k + 1) :=
      orderOf_eq_prime_pow (by rw [a]; exact h1) b
    exact o ▸ IsPrimitiveRoot.orderOf _

theorem coeff_not_isUnit {R : Type*} [CommRing R] [IsLocalRing R] (a : R) (ha : ¬ IsUnit (a - 1)) (i : ℕ) :
    ¬ IsUnit ((WittVector.teichmuller l a - 1 : WittVector l R).coeff i) := by
  have h1 : IsLocalRing.residue R a = 1 := by
    have : IsLocalRing.residue R (a - 1) = 0 :=
      (IsLocalRing.residue_eq_zero_iff _).2 ((IsLocalRing.mem_maximalIdeal _).2 ha)
    rwa [map_sub, map_one, sub_eq_zero] at this
  have h2 : WittVector.map (IsLocalRing.residue R) (WittVector.teichmuller l a - 1 : WittVector l R) = 0 := by
    rw [map_sub, map_one, WittVector.map_teichmuller, h1, map_one, sub_self]
  have h3 : IsLocalRing.residue R ((WittVector.teichmuller l a - 1 : WittVector l R).coeff i) = 0 := by
    rw [← WittVector.map_coeff, h2, WittVector.zero_coeff]
  exact (IsLocalRing.mem_maximalIdeal _).1 ((IsLocalRing.residue_eq_zero_iff _).1 h3)

variable (l) in
theorem isLocalRing_oc : IsLocalRing (OC l) := ValuationRing.isLocalRing (OC l)

variable (l) in
theorem isLocalRing_ob : IsLocalRing (Ob l) :=
  haveI := isLocalRing_oc l
  GlobalTheory.preTilt_isLocalRing l (OC l)

variable (l) in
theorem pFlat_not_isUnit : ¬ IsUnit (pFlat l) := fun h => by
  have h1 : IsUnit (theta0 l (WittVector.teichmuller l (pFlat l))) := (h.map (WittVector.teichmuller l)).map (theta0 l)
  rw [WittVector.fontaineTheta_teichmuller, untilt_pFlat] at h1
  exact (inferInstance : Fact (¬ IsUnit (l : OC l))).out h1

theorem integral_prime_dvd_epsilon_zero_sub_one (ε : Eps l) : pFlat l ∣ ((ε.e 0 : Ob l) - 1) := by
  have h := ((RL.sharp_cong (base l)).2.1 (ε.e 0 : Ob l) 1).1 (by
    have h0 : (base l).sharp (ε.e 0 : Ob l) = 1 := ε.sharp_e (base l)
    rw [h0, map_one, sub_self]
    exact zero_mem _)
  exact Ideal.mem_span_singleton.1 h

theorem epsilon_one_sub_one_not_isUnit (ε : Eps l) : ¬ IsUnit ((ε.e 1 : Ob l) - 1) := fun h => by
  haveI : CharP (Ob l) l := inferInstance
  have h1 : IsUnit (((ε.e 1 : Ob l) - 1) ^ l) := h.pow l
  have e : (ε.e 1 : Ob l) ^ l = ε.e 0 := by
    have := congrArg Units.val (ε.succ 0)
    rwa [Units.val_pow_eq_pow_val] at this
  rw [sub_pow_char, e, one_pow] at h1
  exact pFlat_not_isUnit l (isUnit_of_dvd_unit (integral_prime_dvd_epsilon_zero_sub_one ε) h1)

theorem theta_e_succ (ε : Eps l) (k : ℕ) :
    theta0 l (WittVector.teichmuller l (ε.e (k + 1) : Ob l)) ^ l = theta0 l (WittVector.teichmuller l (ε.e k : Ob l)) := by
  rw [← map_pow, ← map_pow, ← Units.val_pow_eq_pow_val, ε.succ]

theorem qk_succ (ε : Eps l) (k : ℕ) : ε.qk (k + 1) ^ l = ε.qk k := by
  rw [Eps.qk, ← map_pow, ← map_pow, ← Units.val_pow_eq_pow_val, ε.succ, Eps.qk]

theorem sum_mem_ker (ε : Eps l) :
    ∑ i ∈ Finset.range l, (WittVector.teichmuller l (ε.e 1 : Ob l)) ^ i ∈ RingHom.ker (theta0 l) := by
  rw [RingHom.mem_ker, map_sum]
  simp only [map_pow]
  exact geom_sum_eq_zero ((theta_e_succ ε 0).trans ε.one) ε.prim

theorem cris_sum_mem (ε : Eps l) (A : PAlg l) (n : ℕ) :
    A.cris n (∑ i ∈ Finset.range l, ε.qk 1 ^ i) ∈ A.Fil n 1 := by
  have e : ∑ i ∈ Finset.range l, ε.qk 1 ^ i =
      algebraMap (Ainf l) (Acris l) (∑ i ∈ Finset.range l, (WittVector.teichmuller l (ε.e 1 : Ob l)) ^ i) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_pow, Eps.qk]
  have h := sum_mem_ker ε
  rw [ker_theta0] at h
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 h
  rw [e, cris_algebraMap, ← hc, map_mul, map_mul]
  change _ * A.toAcr n A.xi ∈ _
  rw [toAcr_xi]
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨1, le_rfl, rfl⟩)

theorem mu_eq (ε : Eps l) : ε.μ = (ε.qk 1 - 1) * ∑ i ∈ Finset.range l, ε.qk 1 ^ i := by
  rw [mul_geom_sum, qk_succ ε 0, Eps.μ]

theorem eps_facts : ∀ {l : ℕ} [Fact l.Prime] (ε : Eps l), D.InWm l ((WittVector.teichmuller l (ε.e 1 : Ob l)) - 1) ∧ (∀ k, ε.qk (k + 1) ^ l = ε.qk k) ∧ (∀ (A : PAlg l) (n : ℕ), A.cris n (∑ i ∈ Finset.range l, ε.qk 1 ^ i) ∈ A.Fil n 1) ∧ ε.μ = (ε.qk 1 - 1) * ∑ i ∈ Finset.range l, ε.qk 1 ^ i ∧ ∀ m, IsPrimitiveRoot (theta0 l (WittVector.teichmuller l (ε.e m : Ob l))) (l ^ m) := by
  intro l _ ε
  haveI := isLocalRing_ob l
  exact ⟨fun i => coeff_not_isUnit _ (epsilon_one_sub_one_not_isUnit ε) i, qk_succ ε, cris_sum_mem ε, mu_eq ε,
    prim_chain (fun m => theta0 l (WittVector.teichmuller l (ε.e m : Ob l))) (theta_e_succ ε) ε.one ε.prim⟩

end GlobalTheory.CompanionTheory.EpsFacts
