import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnipotentRadicalBasic
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RootExchangeUnipotentHaarAndModulus
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsUnimodularBlockUpperTriangularSymmetricLevels
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemRootExchangeParabolicAndFourierJacobiIffEntri
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemFourierJacobiSubgroupIffParabolicMulColumn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.EqSemiMeasOfCovolOne
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilFormulaRootExchangeParabolicIntersection
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance high] GlobalTheory.SplitWeil.matrixMeasurableSpace

noncomputable section
namespace GlobalTheory.HaarR

variable {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}

def prodR (p : ℕ) (q : GL n k × N k n c p) : R k n c p :=
  ⟨embX c q.1 * (q.2 : GL (n ⊕ Fin c) k), mul_mem (Subgroup.mem_sup_left ⟨q.1, rfl⟩) (Subgroup.mem_sup_right q.2.2)⟩

def prodRFJ (ρ : ℕ) (q : (GL n k × N k n c (ρ + 1)) × (n → k)) : RFJ k n c ρ :=
  ⟨embX c q.1.1 * (q.1.2 : GL (n ⊕ Fin c) k) * colE c (ρ + 1) q.2,
    mul_mem (Subgroup.mem_sup_right (mul_mem (Subgroup.mem_sup_left ⟨q.1.1, rfl⟩) (Subgroup.mem_sup_right q.1.2.2)))
      (Subgroup.mem_sup_left (Subgroup.mem_sup_right
        ((GlobalTheory.RootEx.Radical.unipotent_radical_basic k n c ρ).2.2.2.2.2.2.2 (ρ + 1) q.2 (Nat.lt_succ_self ρ)).1))⟩

@[simp] theorem prodR_coe (p : ℕ) (q : GL n k × N k n c p) :
    (prodR p q : GL (n ⊕ Fin c) k) = embX c q.1 * (q.2 : GL (n ⊕ Fin c) k) := rfl

@[simp] theorem prodRFJ_coe (ρ : ℕ) (q : (GL n k × N k n c (ρ + 1)) × (n → k)) :
    (prodRFJ ρ q : GL (n ⊕ Fin c) k) = embX c q.1.1 * (q.1.2 : GL (n ⊕ Fin c) k) * colE c (ρ + 1) q.2 := rfl

def cjE (ρ : ℕ) (h1 : 1 ≤ ρ) (h2 : ρ < c) (β : n → k) (u : N k n c (ρ + 1)) : N k n c (ρ + 1) :=
  ⟨colE c (ρ + 1) β * (u : GL (n ⊕ Fin c) k) * (colE c (ρ + 1) β)⁻¹,
    (GlobalTheory.RootEx.FourierJacobiGroup.mem_RFJ_iff k n c ρ h1 h2).2 β u u.2⟩

@[simp] theorem cjE_coe (ρ : ℕ) (h1 : 1 ≤ ρ) (h2 : ρ < c) (β : n → k) (u : N k n c (ρ + 1)) :
    (cjE ρ h1 h2 β u : GL (n ⊕ Fin c) k) = colE c (ρ + 1) β * (u : GL (n ⊕ Fin c) k) * (colE c (ρ + 1) β)⁻¹ := rfl

end GlobalTheory.HaarR
end
