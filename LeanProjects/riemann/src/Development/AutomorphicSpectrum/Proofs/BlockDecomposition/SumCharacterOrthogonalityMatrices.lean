import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KvFintype

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.Jp

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.Jp

theorem coY_sum_mul_eq_zero : ∀ (k : Type) [Field k] [Fintype k] (n : ℕ) (ψ₀ : AddChar k ℂ), ψ₀ ≠ 1 →
    ∀ β T : Matrix (Fin n) (Fin n) k, T ≠ β →
      ∑ Y : Matrix (Fin n) (Fin n) k, coY ψ₀ β Y * ψ₀ (Matrix.trace (Y * T)) = 0 := by
  intro k _ _ n ψ₀ hψ β T hne
  classical
  let χ : AddChar (Matrix (Fin n) (Fin n) k) ℂ :=
    { toFun := fun Y => ψ₀ (Matrix.trace (Y * (T - β)))
      map_zero_eq_one' := by simp
      map_add_eq_mul' := fun X Y => by
        rw [Matrix.add_mul, Matrix.trace_add, AddChar.map_add_eq_mul] }
  have hχ : χ ≠ 1 := by
    have hA : T - β ≠ 0 := sub_ne_zero.mpr hne
    obtain ⟨i, j, hij⟩ : ∃ i j, (T - β) i j ≠ 0 := by
      by_contra h
      push_neg at h
      exact hA (Matrix.ext h)
    obtain ⟨a, ha⟩ := (AddChar.ne_one_iff).1 hψ
    refine (AddChar.ne_one_iff).2 ⟨Matrix.single j i (a / (T - β) i j), ?_⟩
    have htr : Matrix.trace (Matrix.single j i (a / (T - β) i j) * (T - β)) = a := by
      rw [Matrix.trace_single_mul]
      exact div_mul_cancel₀ a hij
    change ψ₀ (Matrix.trace (Matrix.single j i (a / (T - β) i j) * (T - β))) ≠ 1
    rw [htr]
    exact ha
  have hterm : ∀ Y : Matrix (Fin n) (Fin n) k,
      coY ψ₀ β Y * ψ₀ (Matrix.trace (Y * T)) = ((Fintype.card k : ℂ) ^ (n * n))⁻¹ * χ Y := by
    intro Y
    have hχY : χ Y = ψ₀ (Matrix.trace (Y * (T - β))) := rfl
    rw [coY, hχY, ← AddChar.map_neg_eq_conj, mul_assoc, ← AddChar.map_add_eq_mul, Matrix.mul_sub,
      Matrix.trace_sub]
    congr 2
    ring
  rw [Finset.sum_congr rfl (fun Y _ => hterm Y), ← Finset.mul_sum, AddChar.sum_eq_zero_of_ne_one hχ, mul_zero]

end GlobalTheory.CompanionTheory.Jp
