import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockV
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveFrameDatumZetaIntegralEqSmaller
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumVolShellInterTranslate

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

noncomputable section

open GlobalTheory.OneSquareZeta

theorem GlobalTheory.LeftTranslateZeta.bigF_phiA_left : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]
    (a : ℕ) (A' C : Type) [Fintype A'] [DecidableEq A'] [Fintype C] [DecidableEq C] (μ : Measure (GL A' k)) [μ.IsHaarMeasure]
    (σ : Fin a ⊕ A' ≃ C) (ν : kˣ →* ℂˣ) (ϖ : kˣ) (n : ℕ) (c : C → kˣ) (Ψ : Matrix A' C k → ℂ) (g₀ : GL (Fin a) k) (h : GL C k),
    IsUnif ϖ →
    bigF (haarVol (KO k (Fin a))) ϖ ν (fun Z => phiA μ σ ν ϖ n (diagLat c) Ψ (g₀.val * Z)) (X0 k σ * (invT h).val) *
      (ν (gdet g₀) : ℂ) * apow (gdet g₀) ((Fintype.card C : ℂ) / 2) = fFun μ σ ν Ψ (X0 k σ * (invT h).val) := by
  intro k _ _ _ _ _ _ a A' C _ _ _ _ μ _ σ ν ϖ n c Ψ g₀ h hϖ

  have hlat : latA ϖ n (diagLat c) = diagLat (fun j => (ϖ ^ n)⁻¹ * (c j)⁻¹) := by
    rw [latA, dualLat_diagLat, smul_diagLat]
  have hrank : (X0 k σ * (invT h).val).rank = a := by
    rw [(rank_eq_card_iff_exists_frameMatrixFirstColumnBlock σ (X0 k σ * (invT h).val)).2 ⟨h, rfl⟩, Fintype.card_fin]

  obtain ⟨g₁, hg₁⟩ := exists_primFrame (fun j => (ϖ ^ n)⁻¹ * (c j)⁻¹) _ hrank
  rw [← hlat] at hg₁
  have hκ : (ν (gdet g₀) : ℂ) * apow (gdet g₀) ((Fintype.card C : ℂ) / 2) ≠ 0 :=
    mul_ne_zero (Units.ne_zero _) (apow_ne_zero _ _)

  have hpt : ∀ g : GL (Fin a) k,
      phiA μ σ ν ϖ n (diagLat c) Ψ (g₀.val * (g.val * (X0 k σ * (invT h).val))) * (ν (gdet g) : ℂ) *
        apow (gdet g) ((Fintype.card C : ℂ) / 2) =
      {g | g₀ * g * g₁⁻¹ ∈ KO k (Fin a)}.indicator
        (fun _ => fFun μ σ ν Ψ (X0 k σ * (invT h).val) /
          ((ν (gdet g₀) : ℂ) * apow (gdet g₀) ((Fintype.card C : ℂ) / 2))) g := by
    intro g
    have hgX : g₀.val * (g.val * (X0 k σ * (invT h).val)) = g₀.val * g.val * (X0 k σ * (invT h).val) :=
      (Matrix.mul_assoc _ _ _).symm
    rw [hgX]
    have key := fFun_mul_left (μ := μ) (σ := σ) (ν := ν) (Ψ := Ψ) (g := g₀ * g) (h := h)
    simp only [apow_mul, map_mul, Units.val_mul] at key
    by_cases hS : g₀ * g * g₁⁻¹ ∈ KO k (Fin a)
    · have hP : IsPrimFrame (latA ϖ n (diagLat c)) ((g₀ * g).val * (X0 k σ * (invT h).val)) :=
        (isPrimFrame_mul_iff hg₁ (g₀ * g)).2 hS
      rw [Units.val_mul] at hP
      rw [Set.indicator_of_mem (show g ∈ {g | g₀ * g * g₁⁻¹ ∈ KO k (Fin a)} from hS), phiA, if_pos hP,
        eq_div_iff hκ, ← key]
      ring
    · have hP : ¬ IsPrimFrame (latA ϖ n (diagLat c)) ((g₀ * g).val * (X0 k σ * (invT h).val)) :=
        fun hP => hS ((isPrimFrame_mul_iff hg₁ (g₀ * g)).1 hP)
      rw [Units.val_mul] at hP
      rw [Set.indicator_of_notMem (show g ∉ {g | g₀ * g * g₁⁻¹ ∈ KO k (Fin a)} from hS), phiA, if_neg hP]
      ring

  have hsum : (∑ᶠ m : {m : Fin a → ℤ // Antitone m}, ∫ g in shellSet ϖ m.1,
      phiA μ σ ν ϖ n (diagLat c) Ψ (g₀.val * (g.val * (X0 k σ * (invT h).val))) * (ν (gdet g) : ℂ) *
        apow (gdet g) ((Fintype.card C : ℂ) / 2) ∂haarVol (KO k (Fin a))) =
      fFun μ σ ν Ψ (X0 k σ * (invT h).val) /
        ((ν (gdet g₀) : ℂ) * apow (gdet g₀) ((Fintype.card C : ℂ) / 2)) := by
    have hint : ∀ m : {m : Fin a → ℤ // Antitone m}, (∫ g in shellSet ϖ m.1,
        phiA μ σ ν ϖ n (diagLat c) Ψ (g₀.val * (g.val * (X0 k σ * (invT h).val))) * (ν (gdet g) : ℂ) *
          apow (gdet g) ((Fintype.card C : ℂ) / 2) ∂haarVol (KO k (Fin a))) =
        (haarVol (KO k (Fin a))).real (shellSet ϖ m.1 ∩ {g | g₀ * g * g₁⁻¹ ∈ KO k (Fin a)}) •
          (fFun μ σ ν Ψ (X0 k σ * (invT h).val) /
            ((ν (gdet g₀) : ℂ) * apow (gdet g₀) ((Fintype.card C : ℂ) / 2))) := by
      intro m
      rw [integral_congr_ae (ae_of_all _ hpt)]
      refine (setIntegral_indicator ?_).trans (setIntegral_const (E := ℂ)
        (fFun μ σ ν Ψ (X0 k σ * (invT h).val) /
          ((ν (gdet g₀) : ℂ) * apow (gdet g₀) ((Fintype.card C : ℂ) / 2))))
      let : MeasurableSpace (GL (Fin a) k) := Units.instMeasurableSpace
      exact (ShellVolume.isOpen_translate g₀ g₁⁻¹).measurableSet
    rw [finsum_congr hint, ← finsum_smul,
      ShellVolume.finsum_vol_shell_inter_translate k a ϖ g₀ g₁⁻¹ hϖ, one_smul]
  unfold bigF shellSum shell
  refine (congrArg (fun s => s * (ν (gdet g₀) : ℂ) * apow (gdet g₀) ((Fintype.card C : ℂ) / 2)) hsum).trans ?_
  rw [mul_assoc]
  exact div_mul_cancel₀ _ hκ

end
