import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GlobSpecOfExists
import Formalism.GradedWeylDivisibility.FinalD
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Formalism.LocalToGlobal.Divisibility.CoefModLemmas
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PosOkId
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GenMDetNeZeroOfNontrivial

open MvPolynomial NumberField IsDedekindDomain Formalism.GradedWeylDivisibility Formalism.MainNotions.G Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.GO GlobalTheory.ValCmp

namespace GlobalTheory.ValCmp

theorem sum_mul_sub_succ : ∀ (m : ℕ) (ν : Fin (m + 1) → ℕ), Antitone ν →
    ∑ s : Fin m, s.val * (ν s.castSucc - ν s.succ) + m * ν (Fin.last m) + ν 0 = ∑ i, ν i := by
  intro m
  induction m with
  | zero => intro ν _; simp
  | succ m ih =>
    intro ν hν
    have h := ih (fun i => ν i.castSucc) (fun a b hab => hν (by simpa using hab))
    rw [Fin.sum_univ_castSucc (f := ν), ← h, Fin.sum_univ_castSucc]
    have hle : ν (Fin.last (m + 1)) ≤ ν (Fin.last m).castSucc := hν (Fin.le_last _)
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hle
    simp only [Fin.val_castSucc, Fin.val_last, Fin.succ_last, Fin.castSucc_zero, Fin.succ_castSucc, hd,
      Nat.add_sub_cancel_left]
    ring

noncomputable def revInitMinor (R : Type) [CommRing R] (n k : ℕ) : MP R n :=
  if h : k ≤ n then initMinor R (fun a : Fin k => Fin.rev (Fin.castLE h a)) h else 1

def antiDiagGL (R : Type) [CommRing R] (n : ℕ) : GL (Fin n) R where
  val := Matrix.of fun a b => if b = a.rev then 1 else 0
  inv := Matrix.of fun a b => if b = a.rev then 1 else 0
  val_inv := by
    ext a b
    rw [Matrix.mul_apply, Finset.sum_eq_single a.rev (fun j _ hj => by simp [hj]) (by simp)]
    simp [Matrix.one_apply, eq_comm]
  inv_val := by
    ext a b
    rw [Matrix.mul_apply, Finset.sum_eq_single a.rev (fun j _ hj => by simp [hj]) (by simp)]
    simp [Matrix.one_apply, eq_comm]

theorem dwAct_antiDiag_X (R : Type) [CommRing R] (n : ℕ) (a s : Fin n) :
    Formalism.UG.dwAct R n n (antiDiagGL R n) (X (a, s)) = X (a.rev, s) := by
  have : (((antiDiagGL R n)⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) =
      Matrix.of fun a b => if b = a.rev then 1 else 0 := rfl
  rw [Formalism.UG.dwAct, this, rowAct, aeval_X, Finset.sum_eq_single a.rev (fun j _ hj => by simp [hj]) (by simp)]
  simp

theorem dwAct_antiDiag_lpMinor (R : Type) [CommRing R] (n k : ℕ) (h h' : k ≤ n) :
    Formalism.UG.dwAct R n n (antiDiagGL R n) (lpMinor R k h h') = revInitMinor R n k := by
  rw [revInitMinor, dif_pos h, lpMinor, initMinor, AlgHom.map_det]
  congr 1
  ext a b : 2
  simp [dwAct_antiDiag_X]

theorem cofAct_lpMinor (R : Type) [CommRing R] [IsDomain R] (n k : ℕ) (h h' : k + 1 ≤ n) : ∃ ε : ℤˣ,
    cofAct R n (lpMinor R (k + 1) h h') = (ε : ℤ) • ((genM R n).det ^ k * revInitMinor R n (n - (k + 1))) := by
  obtain ⟨ε, hε⟩ := cofAct_initMinor R n (k + 1) h (by omega) 1
  refine ⟨ε, ?_⟩
  rw [revInitMinor, dif_pos (Nat.sub_le _ _)]
  exact hε

theorem exists_cofRel_hw : ∀ (R : Type) [CommRing R] [IsDomain R] (m : ℕ) (ν : Fin (m + 1) → ℕ), Antitone ν → ν (Fin.last m) = 0 → ∃ g ∈ weyl R (m + 1) (m + 1) le_rfl (nuDual ν), CofRel R m ν (hw R le_rfl ν) g := by
  intro R _ _ m ν hν h0
  have hmem : hw R le_rfl (nuDual ν) ∈ weyl R (m + 1) (m + 1) le_rfl (nuDual ν) :=
    Submodule.subset_span ⟨[], rfl⟩
  have hJ := Formalism.UG.Final.WeylGLStable R (m + 1) (m + 1) le_rfl (nuDual ν) (antiDiagGL R (m + 1)) _ hmem
  have hnext : ∀ (μ : Fin (m + 1) → ℕ) (s : Fin m), nuNext μ s.castSucc = μ s.succ := by
    intro μ s
    have : s.castSucc.val + 1 < m + 1 := by simp
    rw [nuNext, dif_pos this]
    rfl
  have e1 : Formalism.UG.dwAct R (m + 1) (m + 1) (antiDiagGL R (m + 1)) (hw R le_rfl (nuDual ν)) =
      ∏ s : Fin m, revInitMinor R (m + 1) (m + 1 - (s.val + 1)) ^ (ν s.castSucc - ν s.succ) := by
    rw [hw, map_prod, Fin.prod_univ_castSucc]
    simp only [map_pow, dwAct_antiDiag_lpMinor, hnext]
    have : nuDual ν (Fin.last m) = 0 := by simp [nuDual]
    rw [this, Nat.zero_sub, pow_zero, mul_one, ← Equiv.prod_comp Fin.revPerm]
    refine Finset.prod_congr rfl fun s _ => ?_
    have h1 : ν s.castSucc ≤ ν 0 := hν (Fin.zero_le _)
    have h2 : ν s.succ ≤ ν s.castSucc := hν (Fin.castSucc_lt_succ).le
    have hs := s.isLt
    congr 1
    · congr 1
      simp [Fin.val_rev]
      omega
    · simp only [nuDual, Fin.revPerm_apply, Fin.rev_castSucc, Fin.rev_succ, Fin.rev_rev]
      omega
  choose ε hε using fun s : Fin m =>
    cofAct_lpMinor R (m + 1) s.val (by have := s.isLt; omega) (by have := s.isLt; omega)
  refine ⟨(∏ s : Fin m, (ε s : ℤ) ^ (ν s.castSucc - ν s.succ)) • _, Submodule.smul_of_tower_mem _ _ hJ, ?_⟩
  have hsum : ∑ i, ν i - ν 0 = ∑ s : Fin m, s.val * (ν s.castSucc - ν s.succ) := by
    have := sum_mul_sub_succ m ν hν
    rw [h0] at this
    omega
  rw [CofRel, e1, hsum, hw, map_prod, Fin.prod_univ_castSucc, h0, Nat.zero_sub, pow_zero, map_one, mul_one]
  simp only [map_pow, hnext, Fin.val_castSucc, hε, zsmul_eq_mul, mul_pow, Finset.prod_mul_distrib, ← pow_mul,
    Finset.prod_pow_eq_pow_sum]
  push_cast
  ring

end GlobalTheory.ValCmp
