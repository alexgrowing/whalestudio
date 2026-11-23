import Mathlib
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.MemMulAAOfTrace
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SelfDualCLatP

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate

namespace GlobalTheory.Ker.Inhab

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem exists_ctx_base : ∀ (D : D7) (n p q : ℕ), ∃ (S T : HSp D) (C : Ctx S T), S.rank = 2 * n ∧ C.X.p0 = p ∧
    C.q0 = q ∧ S.SigOK ∧ T.SigOK ∧ ∃ (Lv : GlobalTheory.SW.Level C.X) (B : C.Bas) (f : WO S T → ℂ),
      IdemTwo Lv.w ∧ C.IsB B ∧ C.IsBase Lv B f := by
  intro D n p q
  obtain ⟨S, T, C, h1, h2, h3, h4, h5, B, hB⟩ := exists_ctx_sig D n p q
  obtain ⟨⟨Lv, hw⟩, h6, -⟩ := GlobalTheory.Ker.Base.level_base_fam D S T C
  obtain ⟨f, hf⟩ := h6 Lv B hB
  exact ⟨S, T, C, h1, h2, h3, h4, h5, Lv, B, f, hw, hB, hf⟩

theorem inhabitants :
    (∀ (D : D7) (S T : HSp D) (p q : ℕ) (L : Lt D.host.E T.rank), S.gram = 1 → Even S.rank → p + q = T.rank →
      T.SigOK → (∀ τ, T.sig (tauE D τ) = (p, q)) → IsSelfDualC T L →
      ∃ C : Ctx S T, C.X.p0 = p ∧ C.q0 = q ∧ IsAA C.X.Λ L ∧ ∃ B : C.Bas, C.IsB B) ∧
    ∀ (D : D7) (n p q : ℕ), ∃ (S T : HSp D) (C : Ctx S T), S.rank = 2 * n ∧ C.X.p0 = p ∧ C.q0 = q ∧ S.SigOK ∧
      T.SigOK ∧ ∃ (Lv : GlobalTheory.SW.Level C.X) (B : C.Bas) (f : WO S T → ℂ),
        IdemTwo Lv.w ∧ C.IsB B ∧ C.IsBase Lv B f :=
  ⟨exists_ctx, exists_ctx_base⟩

end GlobalTheory.Ker.Inhab

end
