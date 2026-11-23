import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ScaledIntegerPeriodic

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.KSplit

noncomputable section
namespace GlobalTheory.GJReg

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

def chiS (ν : kˣ →* ℂˣ) (s : ℂ) (g : GL (Fin n) k) : ℂ := (ν (gdet g) : ℂ) * apow (gdet g) s

theorem chiS_mul (ν : kˣ →* ℂˣ) (s : ℂ) (g h : GL (Fin n) k) : chiS ν s (g * h) = chiS ν s g * chiS ν s h := by
  simp only [chiS, gdet_mul, map_mul, Units.val_mul, apow_mul]; ring

@[simp] theorem chiS_one (ν : kˣ →* ℂˣ) (s : ℂ) : chiS ν s (1 : GL (Fin n) k) = 1 := by
  simp [chiS, gdet]

theorem chiS_inv_mul (ν : kˣ →* ℂˣ) (s : ℂ) (g : GL (Fin n) k) : chiS ν s g⁻¹ * chiS ν s g = 1 := by
  rw [← chiS_mul, inv_mul_cancel, chiS_one]

theorem chiS_of_mem_KO {ν : kˣ →* ℂˣ} (hν : IsUnram ν) (s : ℂ) {g : GL (Fin n) k} (hg : g ∈ KO k (Fin n)) :
    chiS ν s g = 1 := by
  have hv := valuation_gdet_of_mem_KO hg
  simp [chiS, hν _ hv, apow_of_valuation_eq_one hv]

def latInd (g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k → ℂ := fun X =>
  (intM k (Fin n) (Fin n)).indicator 1 (X * (g⁻¹ : GL (Fin n) k).val)

theorem latInd_mem_SB (g : GL (Fin n) k) : latInd g ∈ SB (Matrix (Fin n) (Fin n) k) :=
  restrict_mem_SB (P' := g.val) (by rw [← Units.val_mul, inv_mul_cancel, Units.val_one])
    indicator_intM_mem_SB

theorem mul_left_mem_SB (g : GL (Fin n) k) {φ : Matrix (Fin n) (Fin n) k → ℂ}
    (hφ : φ ∈ SB (Matrix (Fin n) (Fin n) k)) : (fun X => φ (g.val * X)) ∈ SB (Matrix (Fin n) (Fin n) k) := by
  obtain ⟨_, _⟩ := Model.secondCountable_and_t2_local_field (k := k)
  have c1 : Continuous fun X : Matrix (Fin n) (Fin n) k => g.val * X := continuous_const.matrix_mul continuous_id
  have c2 : Continuous fun X : Matrix (Fin n) (Fin n) k => (g⁻¹).val * X := continuous_const.matrix_mul continuous_id
  have e : Topology.IsClosedEmbedding fun X : Matrix (Fin n) (Fin n) k => g.val * X :=
    Function.LeftInverse.isClosedEmbedding (f := fun X => (g⁻¹).val * X)
      (fun X => by simp only [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul])
      c2 c1
  exact ⟨hφ.1.comp_continuous c1, hφ.2.comp_isClosedEmbedding e⟩

theorem mul_right_mem_SB (g : GL (Fin n) k) {φ : Matrix (Fin n) (Fin n) k → ℂ}
    (hφ : φ ∈ SB (Matrix (Fin n) (Fin n) k)) : (fun X => φ (X * g.val)) ∈ SB (Matrix (Fin n) (Fin n) k) :=
  restrict_mem_SB (P' := (g⁻¹).val) (by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]) hφ

variable (k n) in

def kInd : Matrix (Fin n) (Fin n) k → ℂ := {X | ∃ g ∈ KO k (Fin n), g.val = X}.indicator 1

def gjZ [MeasurableSpace k] [BorelSpace k] (ν : kˣ →* ℂˣ) (s : ℂ) (φ : Matrix (Fin n) (Fin n) k → ℂ) : ℂ :=
  ∫ g : GL (Fin n) k, φ g.val * (ν (gdet g) : ℂ) * apow (gdet g) s ∂(haarVol (KO k (Fin n)))

end GlobalTheory.GJReg
