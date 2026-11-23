import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ArchimedeanSchwartz.ShiftOf
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SumPermOfNotInjective
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.AbsoluteValueAlt

theorem UpperTheory.Reformulated.B.LocalSmoothExtension.exists_smooth_eq : ∀ {K : Type} [Field K] [NumberField K] {n : ℕ}
    {U : Set (GlobalTheory.CuspRep.Lie K n)}, IsOpen U →
    ∀ {F : GlobalTheory.CuspRep.Lie K n → ℂ}, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F U →
    ∀ {x : GlobalTheory.CuspRep.Lie K n}, x ∈ U →
      ∃ G : GlobalTheory.CuspRep.Lie K n → ℂ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G ∧ G =ᶠ[nhds x] F := by
  intro K _ _ n U hU F hF x hx
  exact UpperTheory.Reformulated.B.ContDiffOnLocalExtension.abs hU hF hx
