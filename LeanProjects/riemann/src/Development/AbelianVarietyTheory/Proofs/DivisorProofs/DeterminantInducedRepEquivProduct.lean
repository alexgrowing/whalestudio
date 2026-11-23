import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMidJacAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSmoothDetPair
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CellFunctorTorusCharacter
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InducedCharIntertwiningUnif
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairInducedEquivProd
open scoped TensorProduct
open GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.IndLineGL

noncomputable section

namespace GlobalTheory.DetIndProd

open GlobalTheory.ThK.MidJac GlobalTheory.RankFibre GlobalTheory.DetIndScal

theorem detInd_equiv_prod₂ : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (a a' : ℕ) (χ₁ χ₂ : kˣ →* ℂˣ),
    Nonempty ((GlobalTheory.ThK.MidJac.detInd a a' χ₁ χ₂).Equiv (prod₂ (detRep (Fin a) χ₁) (detRep (Fin a') χ₂))) := by
  intro k _ _ _ _ a a' χ₁ χ₂
  obtain ⟨ν, rfl⟩ : ∃ ν : kˣ →* ℂˣ, χ₁ = ν * χ₂ := ⟨χ₁ * χ₂⁻¹, by ext x; simp⟩
  have hP : parab k (e2 a a') = parab k (blocks a a') := Subgroup.ext (mem_parabolic_two_blocks_iff a a')
  refine GlobalTheory.PairIndProd.nonempty_smInd_equiv (P := parab k (e2 a a')) (Q := parab k (blocks a a'))
    (σ := (twist (ofChar (GlobalTheory.ThK.DetProd.twoDet a a' (ν * χ₂) χ₂))
      (deltaHalf k (fun c : Fin 2 => Fin (![a, a'] c)))).comp (leviProj k (e2 a a')))
    (τ := (twist (detPair k a a' (ν * χ₂) χ₂) (deltaHalf k (Two (Fin a) (Fin a')))).comp
      (leviProj k (blocks a a'))) hP (TensorProduct.lid ℂ ℂ).symm ?_
  rintro ⟨p, h1⟩ ⟨q, h2⟩ hpq w
  obtain rfl : p = q := hpq
  have hc := char_eq ν χ₂ a a' p h1 h2
  have hp : parChar ν χ₂ a a' ⟨p, h2⟩ = deltaHalf k (Two (Fin a) (Fin a')) (leviProj k (blocks a a') ⟨p, h2⟩) *
      (ν * χ₂) (Matrix.GeneralLinearGroup.det (leviProj k (blocks a a') ⟨p, h2⟩ false)) *
        χ₂ (Matrix.GeneralLinearGroup.det (leviProj k (blocks a a') ⟨p, h2⟩ true)) := rfl
  have hdp : ∀ (x : Levi k (Two (Fin a) (Fin a'))) (v : ℂ ⊗[ℂ] ℂ), detPair k a a' (ν * χ₂) χ₂ x v =
      (((ν * χ₂) (Matrix.GeneralLinearGroup.det (x false)) *
        χ₂ (Matrix.GeneralLinearGroup.det (x true)) : ℂˣ) : ℂ) • v :=
    fun x v => CellTorus.extTensor_detRep_apply (ν * χ₂) χ₂ _ v
  simp only [MonoidHom.comp_apply, twist_apply, ofChar_apply]
  rw [hdp, smul_smul, ← map_smul, ← Units.val_mul, ← mul_assoc, ← hp, ← hc]
  congr 1
  simp only [smul_eq_mul, mul_assoc]

end GlobalTheory.DetIndProd
