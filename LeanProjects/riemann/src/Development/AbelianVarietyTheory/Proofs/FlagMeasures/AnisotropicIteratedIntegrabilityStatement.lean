import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AnisotropicIteratedIntegrability
import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsBesPosOfBesselTied
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Per MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.IndefiniteRowSideFullHecke.BesselData (hA vecA actV)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_convolution_anisotropic : ∀ (D : D7) (X : ThetaX D) (T : ThetaTied D X) (Wl : WeilTied D X T) (L A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V) (d : FJDat L A B ι), 1 < A.rank → IsAniso A → ∀ μ 𝓕, μ.IsHaarMeasure → IsFundamentalDomain (GQ A) 𝓕 μ → ∀ ν 𝓝, IsUnitN B d.eM ν 𝓝 → ∀ s : GA D A → GA D B, (∀ h, EmbRel B A ι (s h) h) → ∀ (Φ : X.Sch L A) φ F, IsAutFun A φ → IsAutFun B F → d.Conv Wl.ψ (omZ Wl L A Φ) μ 𝓕 ν 𝓝 s φ F := by
  first | exact @GlobalTheory.Per.FJConv.conv_of_isAniso | exact GlobalTheory.Per.FJConv.conv_of_isAniso | (intros; apply GlobalTheory.Per.FJConv.conv_of_isAniso <;> assumption)
