import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExpStar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulMemLatIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyThetaOnBdRPlusPeriodData
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFontaineThetaOnAinf
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TeichmullerEpsilonSubExpMemHodgeFiltrationStatement

noncomputable section

namespace GlobalTheory.ExpImage

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc
open scoped Formalism.Per

theorem eq_of_pow_eq_of_nilpotent {Q : Type*} [CommRing Q] {a b : Q} {N : ℕ} (hN : IsUnit (N : Q))
    (hb : IsUnit b) (hn : IsNilpotent (a - b)) (h : a ^ N = b ^ N) : a = b := by
  have h1 := (Commute.all a b).geom_sum₂_mul N
  rw [h, sub_self] at h1
  have h2 : IsNilpotent ((∑ i ∈ Finset.range N, a ^ i * b ^ (N - 1 - i)) - N * b ^ (N - 1)) := by
    have e : (N : Q) * b ^ (N - 1) = ∑ i ∈ Finset.range N, b ^ i * b ^ (N - 1 - i) := by
      rw [Finset.sum_congr rfl (g := fun _ => b ^ (N - 1))]
      · simp
      · intro i hi
        rw [← pow_add]
        congr 1
        have := Finset.mem_range.1 hi
        omega
    rw [e, ← Finset.sum_sub_distrib, ← mem_nilradical]
    refine Ideal.sum_mem _ fun i _ => ?_
    rw [← sub_mul]
    obtain ⟨c, hc⟩ := sub_dvd_pow_sub_pow a b i
    rw [hc, mul_assoc]
    exact Ideal.mul_mem_right _ _ (mem_nilradical.2 hn)
  have h3 := h2.isUnit_add_right_of_commute (hN.mul (hb.pow (N - 1))) (Commute.all _ _)
  rw [sub_add_cancel] at h3
  exact sub_eq_zero.1 ((h3.mul_right_eq_zero).1 h1)

theorem nilpotent_exp_nsmul {Q : Type*} [CommRing Q] [Module ℚ Q] {x : Q} (hx : IsNilpotent x) (n : ℕ) :
    IsNilpotent.exp ((n : Q) * x) = IsNilpotent.exp x ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_succ, add_mul, one_mul, IsNilpotent.exp_add_of_commute (Commute.all _ _)
      ((Commute.all _ _).isNilpotent_mul_left hx) hx, ih, pow_succ]

theorem pow_eq_mul_exp {K Q : Type*} [Field K] [CharZero K] [CommRing Q] [Algebra K Q] {a z t : Q}
    {M N : ℕ} (m : ℕ) (hN : N ≠ 0) (ht : t ^ M = 0) (hz : z ^ N = 1) (hn : IsNilpotent (a - z))
    (ha : a ^ N = ∑ j ∈ Finset.range M, algebraMap K Q ((j.factorial : K)⁻¹) * t ^ j) :
    a ^ m = z ^ m * ∑ j ∈ Finset.range M,
      algebraMap K Q (((m : K) / (N : K)) ^ j / (j.factorial : K)) * t ^ j := by
  letI : Algebra ℚ Q := ((algebraMap K Q).comp (algebraMap ℚ K)).toAlgebra
  have hE : ∀ c : K, IsNilpotent.exp (algebraMap K Q c * t) =
      ∑ j ∈ Finset.range M, algebraMap K Q (c ^ j / (j.factorial : K)) * t ^ j := by
    intro c
    rw [IsNilpotent.exp_eq_sum (k := M) (by rw [mul_pow, ht, mul_zero])]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Algebra.smul_def, mul_pow, ← mul_assoc, ← map_pow, div_eq_inv_mul, map_mul]
    congr 2
    change algebraMap K Q (algebraMap ℚ K _) = _
    simp
  have hN' : (N : K) ≠ 0 := Nat.cast_ne_zero.2 hN
  have hx : IsNilpotent (algebraMap K Q (N : K)⁻¹ * t) :=
    (Commute.all _ _).isNilpotent_mul_left ⟨M, ht⟩
  have hk : ∀ k : ℕ, IsNilpotent.exp (algebraMap K Q (N : K)⁻¹ * t) ^ k =
      ∑ j ∈ Finset.range M, algebraMap K Q (((k : K) / (N : K)) ^ j / (j.factorial : K)) * t ^ j := by
    intro k
    rw [← nilpotent_exp_nsmul hx, ← hE, div_eq_mul_inv, map_mul, map_natCast, mul_assoc]
  have hu : IsUnit z := IsUnit.of_pow_eq_one hz hN
  have e : a = z * IsNilpotent.exp (algebraMap K Q (N : K)⁻¹ * t) := by
    refine eq_of_pow_eq_of_nilpotent (N := N) ?_ (hu.mul hx.isUnit_exp) ?_ ?_
    · have := (IsUnit.mk0 _ hN').map (algebraMap K Q)
      rwa [map_natCast] at this
    · have h1 := (Commute.all z _).isNilpotent_mul_left hx.isNilpotent_exp_sub_one
      have h2 := (Commute.all _ _).isNilpotent_sub hn h1
      convert h2 using 1
      ring
    · rw [mul_pow, hz, one_mul, hk, ha]
      simp [div_self hN']
  rw [e, mul_pow, hk]

variable {l : ℕ} [Fact l.Prime]

def filZero (P : LocPrime l) : Subalgebra ℚ_[l] P.R.BdR where
  carrier := {x | x ∈ FilB P 0}
  mul_mem' hx hy := FilB_zero_mul hx hy
  add_mem' hx hy := (FilB P 0).add_mem hx hy
  algebraMap_mem' c := qB_mem c

def filIdeal (P : LocPrime l) (M : ℕ) : Ideal ↥(filZero P) where
  carrier := {x | (x : P.R.BdR) ∈ FilB P (M : ℤ)}
  zero_mem' := (FilB P (M : ℤ)).zero_mem
  add_mem' hx hy := (FilB P (M : ℤ)).add_mem hx hy
  smul_mem' c _ hx := FilB_zero_mul c.2 hx

theorem epsT_pow {P : LocPrime l} (AI : LocAinf l P) (s : ℕ) :
    epsT AI s ^ l ^ s = WittVector.teichmuller l AI.ε := by
  rw [epsT, ← map_pow]
  congr 1
  induction s with
  | zero => simp [LocAinf.εroot]
  | succ n ih =>
    rw [pow_succ', pow_mul, ← ih, LocAinf.εroot, Function.iterate_succ_apply',
      frobeniusEquiv_symm_pow_p]
    rfl

theorem ζQ_pow (P : LocPrime l) (s : ℕ) : P.ζQ s ^ l ^ s = 1 := by
  induction s with
  | zero => simp [P.ζQ_zero]
  | succ n ih => rw [pow_succ', pow_mul, P.ζQ_succ, ih]

theorem oB_mem_zero {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI) (x : Om l) :
    oB P x ∈ FilB P 0 := by
  obtain ⟨y, h1, -⟩ := T.om x
  exact (GlobalTheory.ThetaTie.fil_zero T _).2 ⟨y, h1.symm⟩

theorem epsT_sub_mem {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI) (s : ℕ) :
    io AI (epsT AI s) - oB P (P.ζQ s) ∈ FilB P 1 := by
  obtain ⟨y, h1, h2⟩ := T.om (P.ζQ s)
  refine (GlobalTheory.ThetaTie.fil_nat T 1 _).2 ⟨GlobalTheory.MemLoc.aDp l (epsT AI s) - y, ?_, ?_⟩
  · rw [← (GlobalTheory.T.thetaBdRPlus_surjective_ker_units_equivariant l).2.1, map_sub, h2, (GlobalTheory.T.thetaBdRPlus_surjective_ker_units_equivariant l).2.2.2.1, epsT,
      WittVector.fontaineTheta_teichmuller, untilt_εroot, AI.ζ_eq, sub_self]
  · rw [map_sub, map_sub, h1, io_apply, GlobalTheory.ThetaTie.eD_ιA]

theorem epsT_pow_taylor : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P),
    LocTied l P AI → ∀ s m M : ℕ, io AI (epsT AI s ^ m) - oB P (P.ζQ s ^ m) *
      ∑ j ∈ Finset.range M, qB P (((m : ℚ_[l]) / (l : ℚ_[l]) ^ s) ^ j / (j.factorial : ℚ_[l])) *
        tD P ^ j ∈ FilB P (M : ℤ) := by
  intro l _ P AI T s m M
  let π := Ideal.Quotient.mkₐ ℚ_[l] (filIdeal P M)
  have hπ : ∀ x y : ↥(filZero P), π x = π y ↔ (x : P.R.BdR) - y ∈ FilB P (M : ℤ) :=
    fun x y => Ideal.Quotient.eq
  have hnil : ∀ x : ↥(filZero P), (x : P.R.BdR) ∈ FilB P 1 → π x ^ M = 0 := by
    intro x hx
    rw [← map_pow, ← map_zero π, hπ]
    simpa using FilB_pow hx M
  let a : ↥(filZero P) := ⟨io AI (epsT AI s), io_mem AI _⟩
  let z : ↥(filZero P) := ⟨oB P (P.ζQ s), oB_mem_zero T _⟩
  let t : ↥(filZero P) := ⟨tD P, FilB_anti zero_le_one tD_mem⟩
  have hs : ∀ c : ℕ → ℚ_[l], ∑ j ∈ Finset.range M, algebraMap ℚ_[l] _ (c j) * π t ^ j =
      π (∑ j ∈ Finset.range M, algebraMap ℚ_[l] _ (c j) * t ^ j) := by
    intro c
    simp only [map_sum, map_mul, map_pow, AlgHom.commutes]
  have hc : ∀ c : ℕ → ℚ_[l],
      ((∑ j ∈ Finset.range M, algebraMap ℚ_[l] _ (c j) * t ^ j : ↥(filZero P)) : P.R.BdR) =
      ∑ j ∈ Finset.range M, qB P (c j) * tD P ^ j := by
    intro c
    rw [AddSubmonoidClass.coe_finset_sum]
    rfl
  have key := pow_eq_mul_exp (K := ℚ_[l]) (a := π a) (z := π z) (t := π t) (M := M) (N := l ^ s) m
    (pow_ne_zero _ (Fact.out : l.Prime).ne_zero) (hnil t tD_mem)
    (by
      rw [← map_pow, ← map_one π]
      congr 1
      apply Subtype.ext
      change oB P (P.ζQ s) ^ l ^ s = 1
      rw [← map_pow, ζQ_pow, map_one])
    ⟨M, by rw [← map_sub]; exact hnil _ (epsT_sub_mem T s)⟩
    (by
      rw [hs (fun j => (j.factorial : ℚ_[l])⁻¹), ← map_pow, hπ, hc]
      change io AI (epsT AI s) ^ l ^ s - _ ∈ _
      rw [← map_pow, epsT_pow]
      exact GlobalTheory.T.teichmullerEpsilon_sub_exp_mem_hodgeFiltration l P AI T M)
  rw [hs (fun j => ((m : ℚ_[l]) / ((l ^ s : ℕ) : ℚ_[l])) ^ j / (j.factorial : ℚ_[l])), ← map_pow,
    ← map_pow, ← map_mul, hπ, Subalgebra.coe_mul, hc, Nat.cast_pow] at key
  rw [map_pow, map_pow]
  exact key

end GlobalTheory.ExpImage
