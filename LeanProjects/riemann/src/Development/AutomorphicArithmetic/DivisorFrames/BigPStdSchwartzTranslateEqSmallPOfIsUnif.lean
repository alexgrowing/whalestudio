import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.FinMatchDefs
import Development.AutomorphicArithmetic.DivisorFrames.ShellSumEqConstOfTwistEqIndicatorDoubleCoset
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardPairFrameBlocksDetAndNegTranspose

namespace UpperTheory.StandardFormChange
open GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdPairLoc GlobalTheory.StdPairCone MeasureTheory
open scoped Matrix

section
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instBorelGL Formalism.DoubleCosetMeasures.instMeasMat

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k]

private theorem std_key (α β ν : kˣ →* ℂˣ) (ϖ : kˣ) (c a a' : ℕ) (hϖ : IsUnif ϖ) (hν : ν = α / β) (h : GL (Fin (a + a')) k) :
    bigP (haarVol (KO k (Fin a))) ϖ finSumFinEquiv ν β (stdA ν ϖ c a a') h =
      smallP (haarVol (KO k (Fin a'))) finSumFinEquiv ν α (stdB ν ϖ c a a') h := by
  rw [bigZetaIntegral_eq, smallP]
  obtain ⟨hdet, hrel⟩ := standardPair_frameBlocks_det_and_neg_transpose a a' h
  obtain ⟨hA0, hA⟩ := bigF_stdA ν ϖ c a a' hϖ
  obtain ⟨hB0, hB⟩ := smallF_stdB (k := k) ν ϖ c a a'
  by_cases h0 : (blk₁ (X0 k (finSumFinEquiv (m := a) (n := a')) * (invT h).val)).det = 0
  · have h0' : (blk₂ (Y0 k (finSumFinEquiv (m := a) (n := a')) * h.val)).det = 0 := by rw [← hdet, h0, zero_mul]
    rw [hA0 _ h0, hB0 _ h0']; simp
  · have h0' : (blk₂ (Y0 k (finSumFinEquiv (m := a) (n := a')) * h.val)).det ≠ 0 := by
      rw [← hdet]; exact mul_ne_zero h0 h.det_ne_zero
    set g₁ := Matrix.GeneralLinearGroup.mkOfDetNeZero _ h0 with hg₁
    set g₂ := Matrix.GeneralLinearGroup.mkOfDetNeZero _ h0' with hg₂
    rw [hA _ g₁ rfl, hB _ g₂ rfl, hrel g₁ g₂ rfl rfl, cball_neg_transpose]
    have hd : gdet g₂ = gdet g₁ * gdet h := Units.ext (by
      simp only [gdet, Units.val_mul, Matrix.GeneralLinearGroup.val_det_apply, g₁, g₂,
        Matrix.GeneralLinearGroup.val_mkOfDetNeZero]
      exact hdet.symm)
    have hαν : α = ν * β := by rw [hν, div_mul_cancel]
    have e : apow (gdet h) ((Fintype.card (Fin a') : ℂ) / 2) * apow (gdet h) (-((Fintype.card (Fin (a + a')) : ℂ) / 2)) =
        apow (gdet h) (-(a : ℂ) / 2) := by
      rw [← apow_add]; congr 1; simp only [Fintype.card_fin]; push_cast; ring
    have e1 : (((ν (gdet g₁ * gdet h))⁻¹ : ℂˣ) : ℂ) = (((ν (gdet g₁))⁻¹ : ℂˣ) : ℂ) * (((ν (gdet h))⁻¹ : ℂˣ) : ℂ) := by
      rw [map_mul, _root_.mul_inv, Units.val_mul]
    have e2 : (α (gdet h) : ℂ) = (ν (gdet h) : ℂ) * (β (gdet h) : ℂ) := by
      rw [hαν, MonoidHom.mul_apply, Units.val_mul]
    have e3 : (ν (gdet h) : ℂ) * (((ν (gdet h))⁻¹ : ℂˣ) : ℂ) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    rw [hd, e1, apow_mul, e2]
    have key2 : ∀ B V Vi Vhi P1 Pa' PN I : ℂ, V * Vhi = 1 →
        B * (Pa' * PN) * (Vi * P1 * I) = V * B * Pa' * (Vi * Vhi * (P1 * PN) * I) := by
      intro B V Vi Vhi P1 Pa' PN I hV; linear_combination (-(B * Pa' * PN * Vi * P1 * I)) * hV
    rw [← e]
    exact key2 _ _ _ _ _ _ _ _ e3

private theorem std_ne (β ν : kˣ →* ℂˣ) (ϖ : kˣ) (c a a' : ℕ) (hϖ : IsUnif ϖ) :
    bigP (haarVol (KO k (Fin a))) ϖ finSumFinEquiv ν β (stdA ν ϖ c a a') 1 ≠ 0 := by
  intro h1
  obtain ⟨-, hA⟩ := bigF_stdA ν ϖ c a a' hϖ
  rw [bigZetaIntegral_eq, hA _ 1 ?_] at h1
  · simp [Set.indicator, gdet, cball, blk₂, X0] at h1
    obtain ⟨i, j, hij⟩ := h1
    have hne : Fin.castAdd a' i ≠ Fin.natAdd a j := by
      intro e; have := congrArg Fin.val e; simp at this; omega
    simp [hne] at hij
  · ext i j
    simp [blk₁, X0, invT_val, Matrix.one_apply]

private theorem bigF_change (ν : kˣ →* ℂˣ) (ϖ : kˣ) (c a a' : ℕ) (hϖ : IsUnif ϖ) (g : GL (Fin a) k)
    (M : Matrix (Fin (a + a')) (Fin (a + a')) k) (X : Matrix (Fin a) (Fin (a + a')) k) :
    bigF (haarVol (KO k (Fin a))) ϖ ν (fun Y : Matrix (Fin a) (Fin (a + a')) k => stdA ν ϖ c a a' (g.1 * Y * M)) X =
      ((ν (gdet g) : ℂ) * apow (gdet g) ((Fintype.card (Fin (a + a')) : ℂ) / 2))⁻¹ *
        bigF (haarVol (KO k (Fin a))) ϖ ν (stdA ν ϖ c a a') (X * M) := by
  obtain ⟨hA0, hA⟩ := bigF_stdA ν ϖ c a a' hϖ
  have has : ∀ y : GL (Fin a) k, g.1 * (y.1 * X) * M = (g * y).1 * (X * M) := fun y => by
    simp only [Units.val_mul, Matrix.mul_assoc]
  by_cases h0 : (blk₁ (X * M)).det = 0
  · rw [hA0 _ h0, mul_zero]
    have h1 : ∀ y : GL (Fin a) k, stdA ν ϖ c a a' (g.1 * (y.1 * X) * M) = 0 := fun y => by
      rw [has, stdA, dif_neg]
      rintro ⟨h, -⟩
      exact h (by rw [blk₁_mul, Matrix.det_mul, h0, mul_zero])
    simp [bigF, shellSum, shell, h1]
  · set g₁ := Matrix.GeneralLinearGroup.mkOfDetNeZero _ h0 with hg₁
    have hg : g₁.val = blk₁ (X * M) := rfl
    rw [hA _ g₁ hg]
    unfold bigF
    refine UpperTheory.shellSum_eq_const_of_twist_eq_indicator_double_coset k ϖ hϖ a ν _ _ _ g g₁ fun y => ?_
    have H := integrand_eq ν (ϖ ^ c) ((Fintype.card (Fin (a + a')) : ℂ) / 2) (blk₂ (X * M)) g₁ (g * y)
      (stdA ν ϖ c a a' ((g * y).1 * (X * M))) (fun h => ?_) (fun h => ?_)
    · have hne : (ν (gdet g) : ℂ) * apow (gdet g) ((Fintype.card (Fin (a + a')) : ℂ) / 2) ≠ 0 :=
        mul_ne_zero (Units.ne_zero _) (apow_ne_zero _ _)
      have H2 : stdA ν ϖ c a a' (g.1 * (y.1 * X) * M) * (ν (gdet y) : ℂ) * apow (gdet y) ((Fintype.card (Fin (a + a')) : ℂ) / 2) =
          ((ν (gdet g) : ℂ) * apow (gdet g) ((Fintype.card (Fin (a + a')) : ℂ) / 2))⁻¹ *
            (stdA ν ϖ c a a' ((g * y).1 * (X * M)) * (ν (gdet (g * y)) : ℂ) *
              apow (gdet (g * y)) ((Fintype.card (Fin (a + a')) : ℂ) / 2)) := by
        rw [eq_inv_mul_iff_mul_eq₀ hne, has, gdet_mul, map_mul, apow_mul, Units.val_mul (ν (gdet g))]
        ring
      refine H2.trans ?_
      rw [H]
      by_cases hy : g * y * g₁ ∈ KO k (Fin a)
      · rw [Set.indicator_of_mem (show g * y ∈ (fun g => g * g₁) ⁻¹' (KO k (Fin a) : Set (GL (Fin a) k)) from hy),
          Set.indicator_of_mem (show y ∈ {y : GL (Fin a) k | g * y * g₁ ∈ KO k (Fin a)} from hy)]
      · rw [Set.indicator_of_notMem (show g * y ∉ (fun g => g * g₁) ⁻¹' (KO k (Fin a) : Set (GL (Fin a) k)) from hy),
          Set.indicator_of_notMem (show y ∉ {y : GL (Fin a) k | g * y * g₁ ∈ KO k (Fin a)} from hy), mul_zero]
    · have h' : (blk₁ ((g * y).val * (X * M))).det ≠ 0 ∧ IsGLO (blk₁ ((g * y).val * (X * M))) ∧
          ∀ i j, blk₂ ((g * y).val * (X * M)) i j ∈ cball (ϖ ^ c) := by
        rw [blk₁_mul, blk₂_mul, ← hg]; exact h
      rw [stdA, dif_pos h']
      congr 3
    · rw [stdA, dif_neg]
      rwa [blk₁_mul, blk₂_mul, ← hg]

private theorem smallF_change (ν : kˣ →* ℂˣ) (a' d : ℕ) (Ψ : Matrix (Fin a') (Fin d) k → ℂ) (l : ℂ) (g : GL (Fin a') k)
    (M : Matrix (Fin d) (Fin d) k) (Y : Matrix (Fin a') (Fin d) k) :
    smallF (haarVol (KO k (Fin a'))) ν (l • fun Y : Matrix (Fin a') (Fin d) k => Ψ (g.1 * Y * M)) Y =
      l * ((ν (gdet g) : ℂ) * apow (gdet g) ((Fintype.card (Fin d) : ℂ) / 2))⁻¹ *
        smallF (haarVol (KO k (Fin a'))) ν Ψ (Y * M) := by
  have hne : (ν (gdet g) : ℂ) * apow (gdet g) ((Fintype.card (Fin d) : ℂ) / 2) ≠ 0 :=
    mul_ne_zero (Units.ne_zero _) (apow_ne_zero _ _)
  unfold smallF
  rw [← integral_mul_left_eq_self (fun y : GL (Fin a') k =>
    Ψ (y.val * (Y * M)) * (ν (gdet y) : ℂ) * apow (gdet y) ((Fintype.card (Fin d) : ℂ) / 2)) g, ← integral_const_mul]
  congr 1
  funext y
  simp only [Pi.smul_apply, smul_eq_mul, Units.val_mul, map_mul, apow_mul, Matrix.mul_assoc]
  rw [mul_assoc l, mul_assoc l, mul_assoc l]
  congr 1
  rw [eq_inv_mul_iff_mul_eq₀ hne]
  ring

private theorem main (ϖ : kˣ) (hϖ : IsUnif ϖ) (α β ν : kˣ →* ℂˣ) (hν : ν = α / β) (c a a' : ℕ) (g : GL (Fin a) k)
    (g' : GL (Fin a') k) (κ : GL (Fin (a + a')) k) :
    bigP (haarVol (KO k (Fin a))) ϖ finSumFinEquiv ν β
        (fun Y : Matrix (Fin a) (Fin (a + a')) k => stdA ν ϖ c a a' (g.1 * Y * κ.1ᵀ)) ≠ 0 ∧
      ∃ l : ℂ, bigP (haarVol (KO k (Fin a))) ϖ finSumFinEquiv ν β
          (fun Y : Matrix (Fin a) (Fin (a + a')) k => stdA ν ϖ c a a' (g.1 * Y * κ.1ᵀ)) =
        smallP (haarVol (KO k (Fin a'))) finSumFinEquiv ν α
          (l • fun Y : Matrix (Fin a') (Fin (a + a')) k => stdB ν ϖ c a a' (g'.1 * Y * (κ⁻¹).1)) := by
  set A : ℂ := ((ν (gdet g) : ℂ) * apow (gdet g) ((Fintype.card (Fin (a + a')) : ℂ) / 2))⁻¹ *
    ((β (gdet κ) : ℂ) * apow (gdet κ) (-(a : ℂ) / 2)) with hA
  set B : ℂ := ((ν (gdet g') : ℂ) * apow (gdet g') ((Fintype.card (Fin (a + a')) : ℂ) / 2))⁻¹ *
    ((α (gdet κ) : ℂ) * apow (gdet κ) ((Fintype.card (Fin a') : ℂ) / 2)) with hB
  have hA0 : A ≠ 0 := mul_ne_zero (inv_ne_zero (mul_ne_zero (Units.ne_zero _) (apow_ne_zero _ _)))
    (mul_ne_zero (Units.ne_zero _) (apow_ne_zero _ _))
  have hB0 : B ≠ 0 := mul_ne_zero (inv_ne_zero (mul_ne_zero (Units.ne_zero _) (apow_ne_zero _ _)))
    (mul_ne_zero (Units.ne_zero _) (apow_ne_zero _ _))
  have h1 : ∀ u : GL (Fin (a + a')) k, bigP (haarVol (KO k (Fin a))) ϖ finSumFinEquiv ν β
      (fun Y : Matrix (Fin a) (Fin (a + a')) k => stdA ν ϖ c a a' (g.1 * Y * κ.1ᵀ)) (u * κ) =
      A * bigP (haarVol (KO k (Fin a))) ϖ finSumFinEquiv ν β (stdA ν ϖ c a a') u := by
    intro u
    have e : X0 k (finSumFinEquiv (m := a) (n := a')) * (invT (u * κ)).val * κ.1ᵀ =
        X0 k (finSumFinEquiv (m := a) (n := a')) * (invT u).val := by
      rw [← invT_inv_val κ, Matrix.mul_assoc, ← Units.val_mul, map_mul, mul_inv_cancel_right]
    rw [bigZetaIntegral_eq, bigZetaIntegral_eq, bigF_change ν ϖ c a a' hϖ, e, gdet_mul, map_mul, apow_mul, Units.val_mul, hA]
    ring
  have h2 : ∀ (l : ℂ) (u : GL (Fin (a + a')) k), smallP (haarVol (KO k (Fin a'))) finSumFinEquiv ν α
      (l • fun Y : Matrix (Fin a') (Fin (a + a')) k => stdB ν ϖ c a a' (g'.1 * Y * (κ⁻¹).1)) (u * κ) =
      l * B * smallP (haarVol (KO k (Fin a'))) finSumFinEquiv ν α (stdB ν ϖ c a a') u := by
    intro l u
    have e : Y0 k (finSumFinEquiv (m := a) (n := a')) * (u * κ).val * (κ⁻¹).1 =
        Y0 k (finSumFinEquiv (m := a) (n := a')) * u.val := by
      rw [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel_right]
    rw [smallP, smallP, smallF_change, e, gdet_mul, map_mul, apow_mul, Units.val_mul, hB]
    ring
  refine ⟨fun H => ?_, A / B, funext fun h => ?_⟩
  · have := congrFun H (1 * κ)
    rw [h1] at this
    exact mul_ne_zero hA0 (std_ne β ν ϖ c a a' hϖ) this
  · obtain ⟨u, rfl⟩ : ∃ u, h = u * κ := ⟨h * κ⁻¹, by simp⟩
    rw [h1, h2, div_mul_cancel₀ _ hB0, std_key α β ν ϖ c a a' hϖ hν]

end

end UpperTheory.StandardFormChange

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints GlobalTheory.Grid GlobalTheory.ChainFr GlobalTheory.SquareComm GlobalTheory.FinMatch
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model piW chrW unifAt latAtV At SInf)
open GlobalTheory.TripleRead (thO ptO)
open GlobalTheory.AdelicU (evFin splitPrime)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.bigZeta_stdSchwartz_translate_eq_smallZeta :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ϖ : kˣ), GlobalTheory.SplitFlip.IsUnif ϖ →
        ∀ (α β ν : kˣ →* ℂˣ), ν = α / β → ∀ (c a a' : ℕ) (g : GL (Fin a) k) (g' : GL (Fin a') k) (κ : GL (Fin (a + a')) k),
        GlobalTheory.SplitFlip.bigP (GlobalTheory.SplitFlip.haarVol (GlobalTheory.SplitWeil.KO k (Fin a))) ϖ finSumFinEquiv ν β
                     (fun Y : Matrix (Fin a) (Fin (a + a')) k => GlobalTheory.StdPairCone.stdA ν ϖ c a a' (g.1 * Y * κ.1ᵀ)) ≠ 0 ∧
        ∃ l : ℂ, GlobalTheory.SplitFlip.bigP (GlobalTheory.SplitFlip.haarVol (GlobalTheory.SplitWeil.KO k (Fin a))) ϖ finSumFinEquiv ν β
            (fun Y : Matrix (Fin a) (Fin (a + a')) k => GlobalTheory.StdPairCone.stdA ν ϖ c a a' (g.1 * Y * κ.1ᵀ)) =
          GlobalTheory.SplitFlip.smallP (GlobalTheory.SplitFlip.haarVol (GlobalTheory.SplitWeil.KO k (Fin a'))) finSumFinEquiv ν α
            (l • fun Y : Matrix (Fin a') (Fin (a + a')) k => GlobalTheory.StdPairCone.stdB ν ϖ c a a' (g'.1 * Y * (κ⁻¹).1)) := by
  intro k _ _ _ _ _ _ ϖ hϖ α β ν hν c a a' g g' κ
  exact UpperTheory.StandardFormChange.main ϖ hϖ α β ν hν c a a' g g' κ
