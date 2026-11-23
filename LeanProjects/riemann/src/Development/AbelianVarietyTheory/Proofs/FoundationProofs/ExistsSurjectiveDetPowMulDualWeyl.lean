import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSystemOf
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GenericDetPowMulHw
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsIrreducibleSmallRepUnitary
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.BasicNotions Formalism.CohomologicalDescent.DepthNonnegative GlobalTheory.ExpFrame GlobalTheory.FrameAut
open scoped Topology

noncomputable section

namespace GlobalTheory.Branching

def lastNat {n : ℕ} (ν : Fin n → ℕ) : ℕ := if h : 0 < n then ν ⟨n - 1, by omega⟩ else 0

theorem natW_add_lastNat {n : ℕ} (ν : Fin n → ℕ) (c : ℤ) (lam : DomWeight n)
    (h : ∀ a, lam.w a = (ν a : ℤ) + c) (a : Fin n) : lam.natW a + lastNat ν = ν a := by
  have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) a.2
  have ha : a ≤ (⟨n - 1, by omega⟩ : Fin n) := Fin.le_def.2 (by have := a.2; simp only; omega)
  have hl := lam.anti ha
  rw [h, h] at hl
  simp only [DomWeight.natW, DomWeight.detShift, lastNat, dif_pos hn, h]
  omega

theorem antitone_of_weight_eq {n : ℕ} (ν : Fin n → ℕ) (c : ℤ) (lam : DomWeight n)
    (h : ∀ a, lam.w a = (ν a : ℤ) + c) : Antitone ν := fun a b hab => by
  have := lam.anti hab
  rw [h, h] at this
  omega

theorem detPow_detShift_eq {n : ℕ} (ν : Fin n → ℕ) (c : ℤ) (lam : DomWeight n)
    (h : ∀ a, lam.w a = (ν a : ℤ) + c) (g : GL (Fin n) ℂ) :
    detPow ℂ n g lam.detShift = detPow ℂ n g c * (g : Matrix (Fin n) (Fin n) ℂ).det ^ lastNat ν := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h1 : Matrix.GeneralLinearGroup.det g = 1 := Units.ext (by simp)
    simp [detPow, h1, lastNat]
  · have hs : lam.detShift = (lastNat ν : ℤ) + c := by simp [DomWeight.detShift, lastNat, hn, h]
    rw [hs, detPow, detPow, zpow_add, Units.val_mul, zpow_natCast, mul_comm]
    simp

theorem detPowMul_mem {n : ℕ} (ν : Fin n → ℕ) (c : ℤ) (lam : DomWeight n)
    (h : ∀ a, lam.w a = (ν a : ℤ) + c) (v : nablaSq ℂ n lam) :
    Formalism.GradedWeylDivisibility.lpMinor ℂ n le_rfl le_rfl ^ lastNat ν * (v : MvPolynomial (Fin n × Fin n) ℂ) ∈
      Formalism.GradedWeylDivisibility.dualWeyl ℂ n n ν := by
  have hm := (genericDet_pow_mul n (lastNat ν) lam.natW).1 v v.2
  have e : (fun i => lam.natW i + lastNat ν) = ν := funext (natW_add_lastNat ν c lam h)
  rwa [e] at hm

def detPowMul {n : ℕ} (ν : Fin n → ℕ) (c : ℤ) (lam : DomWeight n) (h : ∀ a, lam.w a = (ν a : ℤ) + c) :
    nablaSq ℂ n lam →ₗ[ℂ] Formalism.GradedWeylDivisibility.dualWeyl ℂ n n ν :=
  LinearMap.codRestrict _ ((LinearMap.mulLeft ℂ (Formalism.GradedWeylDivisibility.lpMinor ℂ n le_rfl le_rfl ^ lastNat ν)).comp
    (nablaSq ℂ n lam).subtype) (detPowMul_mem ν c lam h)

theorem detPowMul_coe {n : ℕ} (ν : Fin n → ℕ) (c : ℤ) (lam : DomWeight n) (h : ∀ a, lam.w a = (ν a : ℤ) + c)
    (v : nablaSq ℂ n lam) : (detPowMul ν c lam h v : MvPolynomial (Fin n × Fin n) ℂ) =
      Formalism.GradedWeylDivisibility.lpMinor ℂ n le_rfl le_rfl ^ lastNat ν * (v : MvPolynomial (Fin n × Fin n) ℂ) := rfl

theorem detPowMul_sqRep {n : ℕ} (ν : Fin n → ℕ) (c : ℤ) (lam : DomWeight n) (h : ∀ a, lam.w a = (ν a : ℤ) + c)
    (g : GL (Fin n) ℂ) (v : nablaSq ℂ n lam) :
    (detPowMul ν c lam h (GlobalTheory.Branching.sqRep ℂ n lam g v) : MvPolynomial (Fin n × Fin n) ℂ) =
      detPow ℂ n g c • Formalism.GradedWeylDivisibility.rowAct ℂ (n := n) (g : Matrix (Fin n) (Fin n) ℂ).transpose
        (detPowMul ν c lam h v : MvPolynomial (Fin n × Fin n) ℂ) := by
  rw [detPowMul_coe, detPowMul_coe, sqRep_coe, sqAct, (genericDet_pow_mul n (lastNat ν) (fun _ => 0)).2.1,
    Matrix.det_transpose, detPow_detShift_eq ν c lam h, mul_smul_comm, smul_smul]

end GlobalTheory.Branching

namespace GlobalTheory.Branching

theorem exists_surjective_detPowMul_dualWeyl : ∀ (n : ℕ) (ν : Fin n → ℕ) (c : ℤ) (lam : DomWeight n), (∀ a, lam.w a = (ν a : ℤ) + c) → ∃ e : nablaSq ℂ n lam →ₗ[ℂ] Formalism.GradedWeylDivisibility.dualWeyl ℂ n n ν, Function.Surjective e ∧ ∀ (g : GL (Fin n) ℂ) v, (e (GlobalTheory.Branching.sqRep ℂ n lam g v) : MvPolynomial (Fin n × Fin n) ℂ) = detPow ℂ n g c • Formalism.GradedWeylDivisibility.rowAct ℂ (n := n) (g : Matrix (Fin n) (Fin n) ℂ).transpose (e v : MvPolynomial (Fin n × Fin n) ℂ) := by
  intro n ν c lam h
  refine ⟨detPowMul ν c lam h, ?_, detPowMul_sqRep ν c lam h⟩
  let M : Submodule ℂ (MvPolynomial (Fin n × Fin n) ℂ) :=
    (LinearMap.range (detPowMul ν c lam h)).map (Formalism.GradedWeylDivisibility.dualWeyl ℂ n n ν).subtype
  have hU : ∀ u ∈ Matrix.unitaryGroup (Fin n) ℂ, ∀ f ∈ M, Formalism.GradedWeylDivisibility.rowAct ℂ u f ∈ M := by
    rintro u hu _ ⟨_, ⟨v, rfl⟩, rfl⟩
    let t : Matrix.unitaryGroup (Fin n) ℂ := Matrix.UnitaryGroup.transpose ⟨u, hu⟩
    have h1 : (detPowMul ν c lam h (sqRep ℂ n lam (unitaryIncl n t) v) : MvPolynomial (Fin n × Fin n) ℂ) ∈ M :=
      ⟨_, ⟨_, rfl⟩, rfl⟩
    rw [detPowMul_sqRep] at h1
    have e : ((unitaryIncl n t : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ).transpose = u := by
      simp [t]
    rw [e] at h1
    exact (M.smul_mem_iff (Units.ne_zero _)).1 h1
  have hcl := rowDivClosed_of_rowAct_stable M (rowAct_mem_of_unitary_stable M hU)
  have hν := antitone_of_weight_eq ν c lam h
  have hle : M ≤ Formalism.GradedWeylDivisibility.dualWeyl ℂ n n ν := Submodule.map_subtype_le _ _
  have hne : M ≠ ⊥ := by
    intro e0
    have ha : Antitone lam.natW := fun i j hij => by
      have := lam.anti hij
      simp only [DomWeight.natW]
      omega
    let v : nablaSq ℂ n lam := ⟨_, Formalism.GradedWeylDivisibility.hwMem ℂ n n le_rfl _ ha⟩
    have hm : (detPowMul ν c lam h v : MvPolynomial (Fin n × Fin n) ℂ) ∈ M := ⟨_, ⟨v, rfl⟩, rfl⟩
    have e : (fun i => lam.natW i + lastNat ν) = ν := funext (natW_add_lastNat ν c lam h)
    rw [e0, Submodule.mem_bot, detPowMul_coe] at hm
    change Formalism.GradedWeylDivisibility.lpMinor ℂ n le_rfl le_rfl ^ lastNat ν * Formalism.GradedWeylDivisibility.hw ℂ le_rfl lam.natW = 0 at hm
    rw [genericDet_pow_mul_hw, e] at hm
    exact Formalism.GradedWeylDivisibility.hwNe ℂ n n le_rfl ν hm
  have hall := dualWeyl_le_of_rowDivClosed le_rfl ν hν M hle hcl hne
  intro y
  obtain ⟨_, ⟨x, rfl⟩, hx⟩ := hall y.2
  exact ⟨x, Subtype.ext hx⟩

end GlobalTheory.Branching
