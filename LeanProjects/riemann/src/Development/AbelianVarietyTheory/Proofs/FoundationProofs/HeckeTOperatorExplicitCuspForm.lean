import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.PetEqRelIndexMulPetProd
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CuspFormGamma1InterGamma0SlashRatIsZeroAtStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MdifferentiableHeckeOperatorsExplicitStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeTSlashInvariantStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeUOperatorExplicitEqSumSlashStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PowSmulHeckeVOperatorExplicitEqSlashDiagStatement
open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold

namespace GlobalTheory.Hk

theorem map_mapGL_rat (σ : SL(2, ℤ)) :
    Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) (Matrix.SpecialLinearGroup.mapGL ℚ σ) =
      Matrix.SpecialLinearGroup.mapGL ℝ σ := by
  ext i j
  simp

theorem isZeroAt_sum {c : OnePoint ℝ} {k : ℤ} {ι : Type} (s : Finset ι) (F : ι → ℍ → ℂ)
    (h : ∀ i ∈ s, c.IsZeroAt (F i) k) : c.IsZeroAt (∑ i ∈ s, F i) k := by
  refine Finset.sum_induction F (fun G => c.IsZeroAt G k) (fun a b ha hb => ha.add hb) ?_ h
  intro g _
  show IsZeroAtImInfty ((0 : ℍ → ℂ) ∣[k] g)
  rw [SlashAction.zero_slash]
  exact Filter.zero_zeroAtFilter _

theorem heckeT_cuspForm : ∀ (N l q : ℕ) (k : ℤ) (σ : SL(2, ℤ)), 0 < N → q.Prime → ¬ q ∣ N * l →
    GlobalTheory.Hk.IsDia N l q σ → ∀ f : CuspForm (GlobalTheory.Hk.lev N l) k,
    ∃ g : CuspForm (GlobalTheory.Hk.lev N l) k, ⇑g = GlobalTheory.Hk.heckeT k q σ ⇑f := by
  intro N l q k σ hN hq hql hσ f
  have hl : 0 < l := by
    rcases Nat.eq_zero_or_pos l with h | h
    · subst h; simp at hql
    · exact h
  have hq0 : 0 < q := hq.pos
  have hinv := GlobalTheory.T.heckeT_slash_eq_of_slash_eq N l q k σ (⇑f) hN hq hql hσ
    (fun γ hγ => by
      rw [ModularForm.SL_slash]
      exact SlashInvariantFormClass.slash_action_eq f _ ⟨γ, hγ, rfl⟩)
  have hhol := (GlobalTheory.T.mdifferentiable_heckeOperatorsExplicit q k σ (⇑f) hq0 (CuspFormClass.holo f)).2.2
  refine ⟨{ toFun := GlobalTheory.Hk.heckeT k q σ ⇑f
            slash_action_eq' := ?_
            holo' := hhol
            zero_at_cusps' := ?_ }, rfl⟩
  · rintro A ⟨γ, hγ, rfl⟩
    exact hinv γ hγ
  · intro c hc
    show c.IsZeroAt (GlobalTheory.Hk.heckeT k q σ ⇑f) k
    rw [GlobalTheory.Hk.heckeT, GlobalTheory.T.heckeUOperatorExplicit_eq_sum_slash q k (⇑f) hq0, GlobalTheory.T.pow_smul_heckeVOperatorExplicit_eq_slash_diag q k _ hq0, ModularForm.SL_slash,
      ← SlashAction.slash_mul]
    refine OnePoint.IsZeroAt.add (isZeroAt_sum _ _ fun j _ => ?_) ?_
    · exact GlobalTheory.T.cuspForm_gamma1InterGamma0_slash_rat_isZeroAt N l k _ hN hl (by simp [Matrix.det_fin_two_of]; exact_mod_cast hq0) f c hc
    · have h := GlobalTheory.T.cuspForm_gamma1InterGamma0_slash_rat_isZeroAt N l k (Matrix.SpecialLinearGroup.mapGL ℚ σ *
        Matrix.GeneralLinearGroup.mkOfDetNeZero !![(q : ℚ), 0; 0, 1]
          (by simp [Matrix.det_fin_two_of]; exact_mod_cast hq0.ne')) hN hl
        (by simp [Matrix.det_fin_two_of]; exact_mod_cast hq0) f c hc
      rw [map_mul, map_mapGL_rat] at h
      exact h

end GlobalTheory.Hk
