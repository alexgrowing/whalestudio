import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsReduction
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.TopfBasis
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsCuspHom
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CuspidalSubspaceClosedRightTranslationStable
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CommutantScalar
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralInvOfSupport

open MeasureTheory Formalism.MainNotions.S Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult GlobalTheory.RowLev NumberField Matrix
open scoped InnerProductSpace TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowLev

theorem isCuspHom_of_cusp_lowest : ∀ (B : RowsAut), (∀ v, IsDS (B.I.ε v) (B.lam v) (B.σ v)) → (∀ v, ‖B.w v‖ = 1) → ∀ A ∈ B.I.eHom B.σs B.μf B.fund B.R B.Re, B.I.IsCuspFn (B.I.muA B.μf) (B.I.ext (A (B.tens B.w))) → IsCuspHom B.I A := by
  intro B hDS hw A hA hcusp
  obtain ⟨S, hS, hSc, hSR, -⟩ := GlobalTheory.CuspSubspace.cuspidal_closed_stable B
  obtain ⟨-, -, -, -, hirr⟩ :=
    GlobalTheory.HilbTensorRep.tensor_rep_rows B fun v => ⟨(hDS v).2.2.1, (hDS v).2.2.2.1⟩
  obtain ⟨T₀, hT₀, rfl⟩ := Submodule.mem_map.mp hA
  have hT₀' : ∀ g : B.I.Ginf, T₀.comp (B.σs g) = (B.R (g, 1)).comp T₀ := hT₀
  have hRe := (GlobalTheory.IdemProj.re_orth_proj B).2.1

  have hint : ∀ (g : B.I.Ginf) (u : B.Hs),
      B.Re (T₀ (B.σs g u)) = B.R (g, 1) (B.Re (T₀ u)) := by
    intro g u
    have h1 := congrArg (fun L => L u) (hT₀' g)
    have h2 := congrArg (fun L => L (T₀ u)) (hRe g)
    simp only [ContinuousLinearMap.comp_apply] at h1 h2
    rw [h1, h2]

  let P : Submodule ℂ B.Hs := S.comap (B.Re.comp T₀ : B.Hs →L[ℂ] B.I.L2 B.μf B.fund).toLinearMap
  have hPc : IsClosed (P : Set B.Hs) :=
    hSc.preimage (B.Re.comp T₀).continuous
  have hPs : ∀ g, ∀ u ∈ P, B.σs g u ∈ P := by
    intro g u hu
    change B.Re (T₀ (B.σs g u)) ∈ S
    rw [hint]
    exact hSR _ _ hu
  have hw0 : B.tens B.w ∈ P := by
    change B.Re (T₀ (B.tens B.w)) ∈ S
    rw [hS]
    simpa [ContinuousLinearMap.compL_apply] using hcusp
  have hne : B.tens B.w ≠ 0 := by
    intro h0
    have hn := GlobalTheory.HilbTensorRep.norm_tens B.tens_spec.1 B.w
    rw [h0, norm_zero] at hn
    simp [hw] at hn
  rcases hirr P hPc hPs with hbot | htop
  · exact absurd ((Submodule.mem_bot ℂ).mp (hbot ▸ hw0)) hne
  · intro u
    have hu : u ∈ P := htop ▸ Submodule.mem_top
    have : B.Re (T₀ u) ∈ S := hu
    simpa [ContinuousLinearMap.compL_apply] using (hS _).mp this

end GlobalTheory.RowLev
