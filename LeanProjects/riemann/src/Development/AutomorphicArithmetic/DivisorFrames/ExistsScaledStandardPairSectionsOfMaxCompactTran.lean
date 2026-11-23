import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.ComplEquivEvW
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ZetaIdentityPersistsRowColumnChangesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardPairLocalZetaMatchNeZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardPairMembersMemSchwartzBruhatStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels ComplexConjugate
open GlobalTheory.FunObj GlobalTheory.StdFrames GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.LFun.SplitTie
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep Acts SInf At piW chrW)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

section SlopeTestRemainingChoices

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

private noncomputable def subst {m n : ℕ} (g : GL (Fin m) k) (h : GL (Fin n) k) :
    Matrix (Fin m) (Fin n) k ≃ₜ Matrix (Fin m) (Fin n) k where
  toFun X := g.val * X * h.val
  invFun X := (g⁻¹).val * X * (h⁻¹).val
  left_inv X := by
    show (g⁻¹).val * (g.val * X * h.val) * (h⁻¹).val = X
    rw [Matrix.mul_assoc g.val, ← Matrix.mul_assoc (g⁻¹).val, Units.inv_mul, Matrix.one_mul, Matrix.mul_assoc,
      Units.mul_inv, Matrix.mul_one]
  right_inv X := by
    show g.val * ((g⁻¹).val * X * (h⁻¹).val) * h.val = X
    rw [Matrix.mul_assoc (g⁻¹).val, ← Matrix.mul_assoc g.val, Units.mul_inv, Matrix.one_mul, Matrix.mul_assoc,
      Units.inv_mul, Matrix.mul_one]
  continuous_toFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  continuous_invFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const

private theorem subst_SB {m n : ℕ} (g : GL (Fin m) k) (h : GL (Fin n) k) {f : Matrix (Fin m) (Fin n) k → ℂ}
    (hf : f ∈ GlobalTheory.WeilM.SB (Matrix (Fin m) (Fin n) k)) :
    (fun X => f (g.val * X * h.val)) ∈ GlobalTheory.WeilM.SB (Matrix (Fin m) (Fin n) k) :=
  ⟨hf.1.comp_continuous (subst g h).continuous, hf.2.comp_homeomorph (subst g h)⟩

private theorem subst_ne {m n : ℕ} (g : GL (Fin m) k) (h : GL (Fin n) k) {f : Matrix (Fin m) (Fin n) k → ℂ}
    {Y : Matrix (Fin m) (Fin n) k} (hf : f Y ≠ 0) : ∃ X : Matrix (Fin m) (Fin n) k, f (g.val * X * h.val) ≠ 0 := by
  obtain ⟨X, rfl⟩ := (subst g h).surjective Y
  exact ⟨X, hf⟩

open GlobalTheory.StdPairCone in
private theorem stdA_ne (ν : kˣ →* ℂˣ) (ϖ : kˣ) (c a a' : ℕ) : ∃ X, stdA ν ϖ c a a' X ≠ 0 := by
  let X : Matrix (Fin a) (Fin (a + a')) k :=
    Matrix.of fun i => Fin.append ((1 : Matrix (Fin a) (Fin a) k) i) (fun _ => 0)
  have h1 : blk₁ X = 1 := by ext i j; simp [blk₁, X]
  have h2 : blk₂ X = 0 := by ext i j; simp [blk₂, X]
  refine ⟨X, ?_⟩
  have h : (blk₁ X).det ≠ 0 ∧ IsGLO (blk₁ X) ∧ ∀ i j, blk₂ X i j ∈ GlobalTheory.SplitWeil.cball (ϖ ^ c) := by
    rw [h1, h2]
    refine ⟨by simp, ⟨fun i j => ?_, by simp⟩, fun i j => by simp [GlobalTheory.SplitWeil.cball]⟩
    rw [Matrix.one_apply]
    split_ifs
    exacts [one_mem _, zero_mem _]
  rw [stdA, dif_pos h]
  exact Units.ne_zero _

open GlobalTheory.StdPairCone in
private theorem stdB_ne (ν : kˣ →* ℂˣ) (ϖ : kˣ) (c a a' : ℕ) : ∃ Y, stdB ν ϖ c a a' Y ≠ 0 := by
  let X : Matrix (Fin a') (Fin (a + a')) k :=
    Matrix.of fun i => Fin.append (fun _ => 0) ((1 : Matrix (Fin a') (Fin a') k) i)
  have h1 : blk₂ X = 1 := by ext i j; simp [blk₂, X]
  have h2 : blk₁ X = 0 := by ext i j; simp [blk₁, X]
  refine ⟨X, ?_⟩
  have h : (blk₂ X).det ≠ 0 ∧ IsGLO (blk₂ X) ∧ ∀ i j, blk₁ X i j ∈ GlobalTheory.SplitWeil.cball (ϖ ^ c) := by
    rw [h1, h2]
    refine ⟨by simp, ⟨fun i j => ?_, by simp⟩, fun i j => by simp [GlobalTheory.SplitWeil.cball]⟩
    rw [Matrix.one_apply]
    split_ifs
    exacts [one_mem _, zero_mem _]
  rw [stdB, dif_pos h]
  exact Units.ne_zero _

end SlopeTestRemainingChoices

theorem UpperTheory.exists_scaled_standardPairSections_of_maxCompact_translate :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]
        (α β ν : kˣ →* ℂˣ) (ϖ : kˣ) (c m a a' : ℕ), GlobalTheory.SplitFlip.IsUnif ϖ → ν = α / β → 1 ≤ c → GlobalTheory.SplitFlip.CondLE ϖ c ν →
        GlobalTheory.SplitFlip.CondLE ϖ m α → GlobalTheory.SplitFlip.CondLE ϖ m β → (∀ x, ‖(α x : ℂ)‖ = 1) → (∀ x, ‖(β x : ℂ)‖ = 1) →
        ∀ (gA : GL (Fin a) k) (gB : GL (Fin a') k) (cc : GL (Fin (a + a')) k), gA ∈ GlobalTheory.SplitWeil.KO k (Fin a) →
        ∃ (lam : ℂ) (Ξ : Matrix (Fin a) (Fin (a + a')) k → ℂ) (Ψ : Matrix (Fin a') (Fin (a + a')) k → ℂ), lam ≠ 0 ∧
          (∀ X, Ξ X = GlobalTheory.StdPairCone.stdA ν ϖ c a a' (gA.val * X * (cc⁻¹).valᵀ)) ∧
          (∀ Y, Ψ Y = lam * GlobalTheory.StdPairCone.stdB ν ϖ c a a' (gB.val * Y * cc.val)) ∧
          Ξ ∈ GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin (a + a')) k) ∧ Ψ ∈ GlobalTheory.WeilM.SB (Matrix (Fin a') (Fin (a + a')) k) ∧ Ξ ≠ 0 ∧ Ψ ≠ 0 ∧
          GlobalTheory.SplitFlip.bigP (GlobalTheory.SplitFlip.haarVol (GlobalTheory.SplitWeil.KO k (Fin a))) ϖ finSumFinEquiv ν β Ξ =
            GlobalTheory.SplitFlip.smallP (GlobalTheory.SplitFlip.haarVol (GlobalTheory.SplitWeil.KO k (Fin a'))) finSumFinEquiv ν α Ψ := by
  intro k _ _ _ _ _ _ α β ν ϖ c m a a' hϖ hν hc hcν hα hβ nα nβ gA gB cc hgA
  obtain ⟨hz, -⟩ := GlobalTheory.T.standardPair_localZetaMatch_ne_zero α β ν ϖ c m a a' hϖ hν hc hcν hα hβ nα nβ
  obtain ⟨hA, hB⟩ := GlobalTheory.T.standardPair_members_mem_schwartzBruhat ν ϖ c a a' hϖ hcν
  have hab : ν * β = α := by
    rw [hν]
    ext x
    simp
  obtain ⟨lam, hl, H⟩ := GlobalTheory.T.zetaIdentity_persists_row_column_changes k a a rfl (Fin a') (Fin a') (Fin (a + a')) (Fin (a + a')) (Equiv.refl _)
    (Equiv.refl _) finSumFinEquiv finSumFinEquiv (GlobalTheory.SplitFlip.haarVol (GlobalTheory.SplitWeil.KO k (Fin a')))
    (GlobalTheory.SplitFlip.haarVol (GlobalTheory.SplitWeil.KO k (Fin a'))) ϖ ν β gA gB cc hgA
  rw [hab] at H
  have H' := H _ _ hz
  refine ⟨lam, fun X => GlobalTheory.StdPairCone.stdA ν ϖ c a a' (gA.val * X * (GlobalTheory.SplitFlip.invT cc).val),
    fun Y => lam * GlobalTheory.StdPairCone.stdB ν ϖ c a a' (gB.val * Y * cc.val), hl, fun _ => rfl, fun _ => rfl,
    subst_SB gA _ hA, (GlobalTheory.WeilM.SB _).smul_mem lam (subst_SB gB cc hB), ?_, ?_, H'⟩
  · obtain ⟨Y, hY⟩ := stdA_ne ν ϖ c a a'
    obtain ⟨X, hX⟩ := subst_ne gA (GlobalTheory.SplitFlip.invT cc) hY
    exact fun h => hX (congrFun h X)
  · obtain ⟨Y, hY⟩ := stdB_ne ν ϖ c a a'
    obtain ⟨X, hX⟩ := subst_ne gB cc hY
    exact fun h => mul_ne_zero hl hX (congrFun h X)
