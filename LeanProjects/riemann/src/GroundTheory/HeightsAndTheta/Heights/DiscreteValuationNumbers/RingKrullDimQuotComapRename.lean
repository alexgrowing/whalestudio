import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.IsVerticalDivOfIsVerticalDivisor
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagBundle
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsHsymmShift
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsGenericPoint
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PNumericalSegre
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.IsFieldIntersectionExample
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.AssemblyBridgeFull
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Assembly
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

set_option linter.unusedSectionVars false

namespace ProjectiveBundleNumbers

theorem sum_choose_succ (n : ℕ) (U : ℕ → ℤ) :
    ∑ k ∈ Finset.range (n + 2), ((n + 1).choose k : ℤ) * U k =
      ∑ k ∈ Finset.range (n + 1), (n.choose k : ℤ) * U k +
        ∑ k ∈ Finset.range (n + 1), (n.choose k : ℤ) * U (k + 1) := by
  rw [Finset.sum_range_succ', Finset.sum_range_succ' (fun k => (n.choose k : ℤ) * U k)]
  simp only [Nat.choose_succ_succ', Nat.cast_add, add_mul, Finset.sum_add_distrib,
    Nat.choose_zero_right]
  rw [Finset.sum_range_succ (fun k => (n.choose (k + 1) : ℤ) * U (k + 1)),
    Nat.choose_succ_self, Nat.cast_zero, zero_mul, add_zero]
  ring

def extMap {K : Type*} {ι : K → Type} {τ τ' : Type} (g : τ' → τ) :
    (Σ o, IndefiniteRowSideFullHecke.NumbersDVR.extIdx ι τ' o) → Σ o, IndefiniteRowSideFullHecke.NumbersDVR.extIdx ι τ o
  | ⟨none, t⟩ => ⟨none, g t⟩
  | ⟨some k, i⟩ => ⟨some k, i⟩

def extEquiv {K : Type*} {ι : K → Type} {τ τ' : Type} (g : τ' ≃ τ) :
    (Σ o, IndefiniteRowSideFullHecke.NumbersDVR.extIdx ι τ' o) ≃ Σ o, IndefiniteRowSideFullHecke.NumbersDVR.extIdx ι τ o where
  toFun := extMap g
  invFun := extMap g.symm
  left_inv := by
    rintro ⟨(_ | k), i⟩
    · exact congrArg (fun t : τ' => (⟨none, t⟩ : Σ o, IndefiniteRowSideFullHecke.NumbersDVR.extIdx ι τ' o))
        (g.symm_apply_apply i)
    · rfl
  right_inv := by
    rintro ⟨(_ | k), i⟩
    · exact congrArg (fun t : τ => (⟨none, t⟩ : Σ o, IndefiniteRowSideFullHecke.NumbersDVR.extIdx ι τ o))
        (g.apply_symm_apply i)
    · rfl

def bundleEquiv {K : Type*} (ι : K → Type) (M : ℕ) :
    (Σ o, bundleIdx ι M o) ≃ Σ o, IndefiniteRowSideFullHecke.NumbersDVR.extIdx ι (Fin M) o where
  toFun := FlagTypings.bundleToExt ι M
  invFun := FlagTypings.extToBundle ι M
  left_inv := by rintro ⟨(_ | k), i⟩ <;> rfl
  right_inv := by rintro ⟨(_ | k), i⟩ <;> rfl

section ProjBundle

variable {K : Type*} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {F : Type*} [Field F] {Ω : Type*} [Field Ω] [Algebra F Ω]
variable {E : Type*} [AddCommGroup E] [Module Ω E] {N : ℕ}

end ProjBundle

section Rename

variable {F : Type} [Field F] {S : Type} [Fintype S] [DecidableEq S] {κ ι' : S → Type}
  [∀ s, Fintype (κ s)] [∀ s, Fintype (ι' s)]

end Rename

end ProjectiveBundleNumbers

end

end GroundTheory.Heights₂.Heights.NumbersDVR
