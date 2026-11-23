import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ApplyMulTorProd
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaKernelOrthonormalFrameInDomainPeriodLinearStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArchimedeanLiftUnitaryGroupProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdSpan.ConjHol

theorem torProd_spec : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (B : C.Bas), C.IsB B → ∀ (s : D.what₂.Tau → Fin T.rank → ℝ), GlobalTheory.AdSpan.ConjHol.torProd C.θ T B s ∈ GinfC T ∧ ∀ ρ, compAt C.θ ρ (Formalism.L2.Theta.mt T (GlobalTheory.AdSpan.ConjHol.torProd C.θ T B s)) = B ρ * diagonal (fun c => cexp ((s ρ c : ℂ) * I)) * (B ρ)⁻¹ := by
  intro D S T C B hB s
  have R : GlobalTheory.SmoothForms.RealPoints C.θ T := (GlobalTheory.SmoothForms.RealPts.realPoints D).2 C.θ C.inf T
  have hu : ∀ ρ, IsAtTau C.θ T ρ (B ρ * diagonal (fun c => cexp ((s ρ c : ℂ) * I)) * (B ρ)⁻¹) (torAt C.θ T B ρ (s ρ)) := by
    intro ρ
    have hS : (diagonal fun c => cexp ((s ρ c : ℂ) * I))ᴴ * sgnM C.X * (diagonal fun c => cexp ((s ρ c : ℂ) * I)) = sgnM C.X := by
      unfold sgnM
      exact GlobalTheory.HolRead.AdExt.diag_unitary _ _
    exact GlobalTheory.HolRead.AdExt.atTau_spec R ρ (GlobalTheory.HolRead.AdExt.conj_mem_unitary (isUnit_det_B C hB ρ) (hB ρ) hS)
  suffices H : ∀ l : List D.what₂.Tau, l.Nodup → (l.map fun ρ => torAt C.θ T B ρ (s ρ)).prod ∈ GinfC T ∧
      ∀ ρ, infMat D.sp.cm.sig T.gram (C.θ ρ) (l.map fun ρ => torAt C.θ T B ρ (s ρ)).prod =
        if ρ ∈ l then B ρ * diagonal (fun c => cexp ((s ρ c : ℂ) * I)) * (B ρ)⁻¹ else 1 by
    obtain ⟨h1, h2⟩ := H (Finset.univ : Finset D.what₂.Tau).toList (Finset.nodup_toList _)
    refine ⟨h1, fun ρ => ?_⟩
    have := h2 ρ
    rw [if_pos (Finset.mem_toList.2 (Finset.mem_univ _))] at this
    exact this
  intro l hl
  induction l with
  | nil =>
    refine ⟨one_mem _, fun ρ => ?_⟩
    simpa using R.2.2.2.2.1 1 (one_mem _) ρ
  | cons τ l ih =>
    rw [List.nodup_cons] at hl
    obtain ⟨i1, i2⟩ := ih hl.2
    rw [List.map_cons, List.prod_cons]
    refine ⟨mul_mem (hu τ).1 i1, fun ρ => ?_⟩
    rw [R.2.2.2.1, i2 ρ]
    by_cases c : ρ = τ
    · subst c
      rw [(hu ρ).2.1, if_neg hl.1, if_pos List.mem_cons_self, Matrix.mul_one]
    · rw [(hu τ).2.2 ρ c, Matrix.one_mul]
      simp only [List.mem_cons, c, false_or]

end GlobalTheory.AdSpan.ConjHol
