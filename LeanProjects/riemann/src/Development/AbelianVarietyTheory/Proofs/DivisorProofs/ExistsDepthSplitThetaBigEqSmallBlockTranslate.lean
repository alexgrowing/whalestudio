import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockV
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveFrameDatumZetaIntegralEqSmaller
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZetaIntegralTwoSidedMovedDatumEqSmallZetaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNeZeroPrimitiveFrameDatumRenumberStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatBlockScaledHasLatticeDepthStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
attribute [local instance] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.measFv GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.borelFv
attribute [local instance] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.measFv GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.borelFv
open GlobalTheory.PureMatch GlobalTheory.SquareFlipReach ValuativeRel

namespace GlobalTheory.PureMatch

theorem smallP_smul_measure_mul {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] {A A' C : Type} [Fintype A'] [DecidableEq A'] [Fintype C] [DecidableEq C]
    (μ : Measure (GL A' k)) (c : NNReal) (z : ℂ) (σ : A ⊕ A' ≃ C) (ν α : kˣ →* ℂˣ) (Ψ : Matrix A' C k → ℂ)
    (h : GL C k) : smallP (c • μ) σ ν α (fun Y => z * Ψ Y) h = (c : ℂ) * z * smallP μ σ ν α Ψ h := by
  simp only [smallP, smallF, mul_assoc, integral_const_mul, integral_smul_nnreal_measure, NNReal.smul_def,
    Complex.real_smul]
  ring

theorem bigZetaIntegral_const_mul {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] {a : ℕ} {A' C : Type} [Fintype C] [DecidableEq C]
    (μ : @Measure (GL (Fin a) k) Units.instMeasurableSpace) (ϖ : kˣ) (σ : Fin a ⊕ A' ≃ C) (ν β : kˣ →* ℂˣ) (z : ℂ)
    (Φ : Matrix (Fin a) C k → ℂ) (h : GL C k) :
    bigP μ ϖ σ ν β (fun Z => z * Φ Z) h = z * bigP μ ϖ σ ν β Φ h := by
  simp only [bigZetaIntegral_eq, bigF, shellSum_smul]
  ring

theorem exists_depth_bigP_eq_smallP : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]
    (a : ℕ) (A' C : Type) [Fintype A'] [DecidableEq A'] [Fintype C] [DecidableEq C] (μ₀ : Measure (GL A' k)) [μ₀.IsHaarMeasure]
    (σ : Fin a ⊕ A' ≃ C) (ν β : kˣ →* ℂˣ) (ϖ : kˣ) (P : Finset C) (g₀ : GL (Fin a) k) (c₀ : GL C k) (Ψ : Matrix A' C k → ℂ),
    Ψ ∈ GlobalTheory.WeilM.SB (Matrix A' C k) → IsUnif ϖ → ∃ m : ℕ, ∀ n, 2 * m ≤ n →
      ∀ (μ : Measure (GL A' k)) [μ.IsHaarMeasure] (σ' : Fin a ⊕ A' ≃ C) (r : ℂ), r ≠ 0 → ∃ Ξ : Matrix A' C k → ℂ,
        HasDepth ϖ n (blockLat ϖ n P) Ξ ∧
        bigP (haarVol (KO k (Fin a))) ϖ σ ν β (fun Z => r * phiA μ σ' ν ϖ n (blockLat ϖ n P) Ξ
          (g₀.val * Z * (c₀ * diagGL (fun col => if col ∈ P then ϖ ^ m else (ϖ ^ m)⁻¹)).val)) = smallP μ₀ σ ν (ν * β) Ψ := by
  intro k _ _ _ _ _ _ a A' C _ _ _ _ μ₀ _ σ ν β ϖ P g₀ c₀ Ψ hΨ hϖ
  have hΨ' : (fun Y : Matrix A' C k => Ψ (Y * c₀.valᵀ)) ∈ GlobalTheory.WeilM.SB (Matrix A' C k) := by
    have := comp_mul_mem_SB (1 : GL A' k) (invT c₀)⁻¹ hΨ
    simp only [invT_inv_val, Units.val_one, Matrix.one_mul] at this
    exact this
  obtain ⟨m, hm⟩ := GlobalTheory.T.schwartzBruhat_blockScaled_hasLatticeDepth k A' C ϖ P _ hΨ' hϖ
  refine ⟨m, fun n hn μ _ σ' r hr => ?_⟩
  obtain ⟨u, hu, hphi⟩ := GlobalTheory.T.exists_ne_zero_primitiveFrameDatum_renumber k (Fin a) A' C μ σ σ' ν
  obtain ⟨c, hc0, hc⟩ : ∃ c : NNReal, c ≠ 0 ∧ μ = c • μ₀ :=
    ⟨Measure.haarScalarFactor μ μ₀, (Measure.haarScalarFactor_pos_of_isHaarMeasure μ μ₀).ne',
      Measure.isMulLeftInvariant_eq_smul μ μ₀⟩
  set N : GL C k := c₀ * diagGL (fun col => if col ∈ P then ϖ ^ m else (ϖ ^ m)⁻¹) with hN
  set κ : ℂ := (ν (gdet g₀) : ℂ) * apow (gdet g₀) ((Fintype.card C : ℂ) / 2) * (ν (gdet N) : ℂ) *
    apow (gdet N) ((Fintype.card C : ℂ) / 2) with hκ
  have hκ0 : κ ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (Units.ne_zero _) (apow_ne_zero _ _)) (Units.ne_zero _)) (apow_ne_zero _ _)
  have hc0' : ((c : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hc0
  have hNT : ∀ Y : Matrix A' C k, Y * N.valᵀ =
      Y * diagonal (fun col => if col ∈ P then ((ϖ ^ m : kˣ) : k) else (((ϖ ^ m)⁻¹ : kˣ) : k)) * c₀.valᵀ := by
    intro Y
    rw [hN, Units.val_mul, transpose_mul, diagGL_val, diagonal_transpose, Matrix.mul_assoc]
    congr 3
    funext col
    split_ifs <;> rfl
  refine ⟨fun Y => (κ / (r * u * c)) * Ψ (Y * N.valᵀ), ?_, ?_⟩
  · have h1 := (depthSpace A' ϖ n (blockLat ϖ n P)).smul_mem (κ / (r * u * c)) (hm n hn)
    simp only [hNT]
    exact h1
  · funext h
    have h2 := GlobalTheory.T.zetaIntegral_twoSidedMovedDatum_eq_smallZeta k a A' C μ σ ν β ϖ n (blockUnits ϖ n P)
      (fun Y => (κ / (r * u * c)) * Ψ (Y * N.valᵀ)) g₀ N h hϖ
    have h3 : ∀ Y : Matrix A' C k, Y * (invT N).val * N.valᵀ = Y := fun Y => by
      rw [Matrix.mul_assoc, ← invT_inv_val, Units.mul_inv, Matrix.mul_one]
    simp only [h3] at h2
    have h4 := smallP_smul_measure_mul μ₀ c (κ / (r * u * c)) σ ν (ν * β) Ψ h
    rw [← hc, ← h2, ← hκ] at h4
    simp only [hphi, ← mul_assoc]
    rw [bigZetaIntegral_const_mul]
    apply mul_left_cancel₀ hκ0
    rw [mul_left_comm]
    refine (congrArg (fun x => r * u * x) h4).trans ?_
    field_simp

end GlobalTheory.PureMatch
