import Mathlib
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsCharacterOverSubfieldRestrictClassFunctionOne
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsCharacterOverSubfieldRestrictClassFunctionOneStatement
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.PrimitiveClassFunctionExpansionRootSumsStatement
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.GeneralLinearFunctionExtendZeroEndPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.RootPowerSumCharpolyMemVirtualCharactersGLStatement
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.VirtualCharacterInnerEqIntMulCardStatement
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.InvariantSubspaceMobiusInverseOneProdIcoStatement
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.RootPowerSumCharacterAdditiveAndXSubOnePowStatement

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI

namespace GlobalTheory.CuspGL

theorem exists_int_coeff_of_isPrimitive (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ)
    (hθ : ∀ x y : AlgebraicClosure F, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) (d : ℕ) (χ : GL (Fin d) F → ℂ)
    (hd : 0 < d) (hχ : IsChar ℂ ℂ χ) (hp : IsPrimitive (extZero χ)) :
    ∃ a : ℕ → ℤ, (∀ k : ℕ, ipGL (extZero χ)
        (fun g : Module.End F (Fin d → F) => rootSum θ k (LinearMap.charpoly g)) = a k * glCard F d) ∧
      (d : ℂ) * χ 1 = (∑ k ∈ Finset.range (Nat.card F ^ d - 1), (a k : ℂ)) *
        ∏ i ∈ Finset.Ico 1 d, (1 - (Nat.card F : ℂ) ^ i) := by
  classical
  obtain ⟨-, hconj, -⟩ := GlobalTheory.T.isCharacterOverSubfield_restrict_classFunction_one ℂ ℂ _ χ hχ
  obtain ⟨hval, -, hip, hcls⟩ := GlobalTheory.T.generalLinearFunctionExtendZeroEnd_properties F d χ
  have hrank : Module.finrank F (Fin d → F) = d := Module.finrank_fin_fun F
  have hint : ∀ k : ℕ, ∃ m : ℤ, ipGL (extZero χ)
      (fun g : Module.End F (Fin d → F) => rootSum θ k (LinearMap.charpoly g)) = m * glCard F d := by
    intro k
    obtain ⟨m, hm⟩ := GlobalTheory.T.virtualCharacter_inner_eq_int_mul_card (GL (Fin d) F) χ
      (fun x : GL (Fin d) F => rootSum θ k (Matrix.charpoly (x : Matrix (Fin d) (Fin d) F)))
      (AddSubgroup.subset_closure hχ) (GlobalTheory.T.rootPowerSum_charpoly_mem_virtualCharacters_GL F θ hθ d k)
    refine ⟨m, ?_⟩
    rw [hip]
    simp only [hval, Matrix.charpoly_toLin']
    unfold glCard
    exact hm
  choose a ha using hint
  refine ⟨a, ha, ?_⟩
  have hdpos : 0 < Module.finrank F (Fin d → F) := by rw [hrank]; exact hd
  have hmain := GlobalTheory.T.primitiveClassFunction_expansion_rootSums F (Fin d → F) θ hθ (extZero χ) (hcls hconj) hp hdpos 1 isUnit_one
  have hpsi : ∀ k : ℕ, psi (rootSum θ k) (Fin d → F) 1 =
      ∏ i ∈ Finset.Ico 1 d, (1 - (Nat.card F : ℂ) ^ i) := by
    intro k
    have h := GlobalTheory.T.invariantSubspaceMobiusInverse_one_prod_Ico F (Fin d → F) (rootSum θ k) (GlobalTheory.T.rootPowerSumCharacter_additive_and_X_sub_one_pow F θ k).2 hdpos
    rwa [hrank] at h
  have hone : extZero χ (1 : Module.End F (Fin d → F)) = χ 1 := by
    have h := hval 1
    rw [Units.val_one, Matrix.toLin'_one] at h
    exact h
  rw [hrank] at hmain
  simp only [ha, hpsi, hone] at hmain
  have hne : glCard F d ≠ 0 := by
    have h : 0 < Nat.card (GL (Fin d) F) := Nat.card_pos
    unfold glCard
    exact_mod_cast h.ne'
  have hsum : ∑ k ∈ Finset.range (Nat.card F ^ d - 1),
      (a k : ℂ) * glCard F d * ∏ i ∈ Finset.Ico 1 d, (1 - (Nat.card F : ℂ) ^ i) =
      glCard F d * ((∑ k ∈ Finset.range (Nat.card F ^ d - 1), (a k : ℂ)) *
        ∏ i ∈ Finset.Ico 1 d, (1 - (Nat.card F : ℂ) ^ i)) := by
    rw [Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring
  apply mul_left_cancel₀ hne
  rw [← hsum, ← hmain]
  ring

end GlobalTheory.CuspGL
