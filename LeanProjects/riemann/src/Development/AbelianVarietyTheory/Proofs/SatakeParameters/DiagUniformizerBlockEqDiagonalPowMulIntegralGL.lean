import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsUniqueVec
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TendstoOneOfSummable
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftGoodProjectorIntertwinesMatchedHecke
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalLabelOperatorsOnHyperspecialFixedVector
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSplitLocalPlaceDataAtSplitPlaceStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceDoubleCosetOperatorsCommuteSpherical
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHomTrivOutsideLoc
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CompletedLatticeIntegralityFacts
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DivisorsAtInvDualLabelAndStabilizerMul
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitPlaceHeckeSatake
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct

namespace GlobalTheory.DiagUnifFactor

theorem getD_pattern (k m i : ℕ) :
    (List.replicate k (1 : ℤ) ++ List.replicate m 0).getD i 0 = if i < k then 1 else 0 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append]
  split_ifs with h1 h2 h2
  · simp [List.getElem?_replicate, h2]
  · simp at h1; omega
  · simp at h1; omega
  · simp [List.getElem?_replicate]
    split_ifs <;> rfl

theorem main : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (n k : ℕ)
    (ϖ π : v.adicCompletion F), Valued.v ϖ = WithZero.exp (-1 : ℤ) → Valued.v π = WithZero.exp (-1 : ℤ) →
    ∃ T ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.Ov F v), Formalism.UG.diagJ n ϖ k =
      Matrix.diagonal (fun i : Fin n => π ^ ((List.replicate k (1 : ℤ) ++ List.replicate (n - k) 0).getD i.1 0)) *
        (T : Matrix (Fin n) (Fin n) (v.adicCompletion F)) := by
  intro F _ _ v n k ϖ π hϖ hπ
  have hπ0 : π ≠ 0 := by
    intro h; rw [h, map_zero] at hπ; exact WithZero.zero_ne_coe hπ
  have hϖ0 : ϖ ≠ 0 := by
    intro h; rw [h, map_zero] at hϖ; exact WithZero.zero_ne_coe hϖ
  have hu : Valued.v (ϖ / π) = 1 := by
    rw [map_div₀, hϖ, hπ, div_self (WithZero.coe_ne_zero)]
  have hu' : Valued.v (π / ϖ) = 1 := by
    rw [map_div₀, hϖ, hπ, div_self (WithZero.coe_ne_zero)]
  let d : Fin n → v.adicCompletion F := fun i => if (i : ℕ) < k then ϖ / π else 1
  let d' : Fin n → v.adicCompletion F := fun i => if (i : ℕ) < k then π / ϖ else 1
  have hdd' : Matrix.diagonal d * Matrix.diagonal d' = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; funext i; simp only [d, d']
    split_ifs
    · rw [div_mul_div_comm, mul_comm ϖ π, div_self (mul_ne_zero hπ0 hϖ0)]
    · exact one_mul 1
  have hd'd : Matrix.diagonal d' * Matrix.diagonal d = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; funext i; simp only [d, d']
    split_ifs
    · rw [div_mul_div_comm, mul_comm π ϖ, div_self (mul_ne_zero hϖ0 hπ0)]
    · exact one_mul 1
  let T : GL (Fin n) (v.adicCompletion F) := ⟨Matrix.diagonal d, Matrix.diagonal d', hdd', hd'd⟩
  have hmem : ∀ (e : Fin n → v.adicCompletion F), (∀ i, Valued.v (e i) ≤ 1) →
      ∀ a b, Matrix.diagonal e a b ∈ Formalism.UG.Ov F v := by
    intro e he a b
    show Matrix.diagonal e a b ∈ v.adicCompletionIntegers F
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    by_cases hab : a = b
    · subst hab; rw [Matrix.diagonal_apply_eq]; exact he a
    · rw [Matrix.diagonal_apply_ne _ hab, map_zero]; exact zero_le'
  have hle : ∀ (x : v.adicCompletion F), Valued.v x = 1 → ∀ i : Fin n,
      Valued.v (if (i : ℕ) < k then x else 1) ≤ 1 := by
    intro x hx i; split_ifs
    · exact hx.le
    · rw [map_one]
  refine ⟨T, ?_, ?_⟩
  · have inj : Function.Injective ((Formalism.UG.Ov F v).subtype.mapMatrix (m := Fin n)) :=
      fun A B h => Matrix.ext fun i j => Subtype.ext (congrFun (congrFun h i) j)
    let A : Matrix (Fin n) (Fin n) (Formalism.UG.Ov F v) := fun i j => ⟨Matrix.diagonal d i j, hmem d (hle _ hu) i j⟩
    let B : Matrix (Fin n) (Fin n) (Formalism.UG.Ov F v) := fun i j => ⟨Matrix.diagonal d' i j, hmem d' (hle _ hu') i j⟩
    have hA : (Formalism.UG.Ov F v).subtype.mapMatrix A = Matrix.diagonal d := rfl
    have hB : (Formalism.UG.Ov F v).subtype.mapMatrix B = Matrix.diagonal d' := rfl
    refine ⟨⟨A, B, inj ?_, inj ?_⟩, Units.ext rfl⟩
    · rw [map_mul, hA, hB, map_one, hdd']
    · rw [map_mul, hA, hB, map_one, hd'd]
  · show Matrix.diagonal _ = _ * Matrix.diagonal d
    rw [Matrix.diagonal_mul_diagonal]
    congr 1; funext i
    rw [getD_pattern]
    simp only [d]
    split_ifs
    · rw [zpow_one, mul_div_cancel₀ _ hπ0]
    · rw [zpow_zero, one_mul]

end GlobalTheory.DiagUnifFactor
