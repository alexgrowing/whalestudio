import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemIntMat
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem diag_unitary_exp_sym {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (c : L →+* L) (q : ℕ)
    (hU : IsUnramInv ϖ c q) (r : ℕ) (d : Fin r → ℤ) (t : GU c r)
    (ht : t.1.1 = Matrix.diagonal (fun i => ϖ ^ d i)) :
    ∑ i, max (-d i) 0 = ∑ i, max (d i) 0 := by
  obtain ⟨_, _, hcϖ, hv, _⟩ := hU
  have hmem := t.2
  change Formalism.UG.cT c (t.1.1) * Formalism.UG.antiJ L r * t.1.1 = Formalism.UG.antiJ L r at hmem
  rw [ht] at hmem
  have hcT : Formalism.UG.cT c (Matrix.diagonal (fun i => ϖ ^ d i)) = Matrix.diagonal (fun i => ϖ ^ d i) := by
    ext i j
    simp only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply, Matrix.diagonal_apply]
    by_cases h : i = j
    · subst h; simp [map_zpow₀, hcϖ]
    · simp [h, Ne.symm h]
  rw [hcT] at hmem
  have hϖ : ϖ ≠ 0 := by
    intro h0; rw [h0, map_zero] at hv; exact WithZero.zero_ne_coe hv
  have key : ∀ i : Fin r, d (Fin.rev i) = -d i := by
    intro i
    have e := congrArg (fun M => M i (Fin.rev i)) hmem
    simp only [Matrix.diagonal_mul, Matrix.mul_diagonal] at e
    have hJ : Formalism.UG.antiJ L r i (Fin.rev i) = 1 := by
      simp only [Formalism.UG.antiJ, Fin.val_rev]; rw [if_pos]; omega
    rw [hJ, mul_one] at e
    rw [← zpow_add₀ hϖ] at e
    have e2 := congrArg (fun x => Valued.v x) e
    simp only [map_zpow₀, map_one, hv] at e2
    rw [← WithZero.coe_zpow, ← ofAdd_zsmul] at e2
    have e3 : (d i + d (Fin.rev i)) • (-1 : ℤ) = 0 := by
      have := WithZero.coe_injective e2
      exact Multiplicative.ofAdd.injective (this.trans ofAdd_zero.symm)
    simp at e3
    omega
  calc ∑ i, max (-d i) 0 = ∑ i, max (d (Fin.rev i)) 0 := by simp [key]
    _ = ∑ i, max (d i) 0 := Equiv.sum_comp Fin.revPerm (fun i => max (d i) 0)

end GlobalTheory
