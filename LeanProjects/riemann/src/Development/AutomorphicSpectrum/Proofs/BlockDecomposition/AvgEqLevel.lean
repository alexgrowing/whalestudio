import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LeviOf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinsumOutOfLe

open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcN.F2
open scoped Classical TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CompanionTheory.AvgLevel

theorem avg_eq_level : ∀ {H : Type} [Group H] (S : Subgroup H) (u : H → ℂ), S ≤ rStab u →
    S.index ≠ 0 → avg u = ((S.index : ℂ))⁻¹ * ∑ᶠ q : H ⧸ S, u q.out := by
  intro H _ S u hS hfin
  have hmul := Subgroup.relIndex_mul_index hS
  have hm : S.relIndex (rStab u) ≠ 0 := fun h0 => hfin (by rw [← hmul, h0, zero_mul])
  have hmC : ((S.relIndex (rStab u) : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hm
  rw [GlobalTheory.CompanionTheory.HintLevel.finsum_out_of_le u hS le_rfl hm, ← hmul, avg, Nat.cast_mul, mul_inv,
    mul_mul_mul_comm, inv_mul_cancel₀ hmC, one_mul]

end GlobalTheory.CompanionTheory.AvgLevel
