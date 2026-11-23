import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexConjIntegralGLColumnCongruence
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrdL
open GlobalTheory.FunObj GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx GlobalTheory.DiagVol ValuativeRel Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relIndex_conj_integralGL_column_congruence : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {ι : Type} [Fintype ι] [DecidableEq ι] (ϖ : kˣ), IsUnif ϖ → ∀ (t : ι) (S : Finset ι), t ∉ S → ∀ (H : Subgroup (GL ι k)), H ≤ KO k ι → (∀ x ∈ H, ∀ r, r ∉ S → x.val r t = (1 : Matrix ι ι k) r t) → (∀ y : ι → k, (∀ r, y r ∈ 𝒪[k]) → (∀ r, r ∉ S → y r = 0) → ∃ x ∈ H, x.val = 1 + Matrix.of (fun r s => if s = t then y r else 0)) → ((KO k ι).map (MulAut.conj ((diagGL (Pi.mulSingle t ϖ))⁻¹)).toMonoidHom).relIndex H = resCard k ^ S.card := by
  first | exact @GlobalTheory.IndexCol.relIndex_conj_col | exact GlobalTheory.IndexCol.relIndex_conj_col | (intros; apply GlobalTheory.IndexCol.relIndex_conj_col <;> assumption)
