import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchrodingerImagesOrthogonalDisjointSplitSupport
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdjFormula
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaPairingInvariant
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DatP
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open GlobalTheory.BadPlace
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schrodingerImages_orthogonal_disjoint_splitSupport : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (Pf : Finset (Pl D.host.E)) (ea e : AE D) (f₀ : WO S T → ℂ) (Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsStdChar D ψ (-1) → IsSelfDualC S ΛS → IsSelfDualC T ΛT → IsIdemSum ea Pf → IsSplitIdem D e → e * ea = e → IsThetaFunO ψ S T f₀ → IsLatVac (heisO ψ S T) (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) f₀ → IsPlaceModel ψ (symplO S T) (heisO ψ S T) (cA D ea) (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) 1 f₀ Tm → IsCovolOne (ratL T S) μ 𝓕 → ∀ Φ₁ Φ₂ : WO S T → ℂ, IsSBHalf (cA D ea) (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) Φ₁ → IsSBHalf (cA D ea) (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) Φ₂ → (∀ x x' : WO S T, (∀ a b, (e + cA D e) * x a b = (e + cA D e) * x' a b) → Φ₁ x ≠ 0 → Φ₂ x' ≠ 0 → False) → ∀ Ω : Module.End ℂ (WO S T → ℂ), (∀ g, IsThetaFunO ψ S T g → IsThetaFunO ψ S T (Ω g)) → (∀ y : WO S T, IsHalf e y → ∀ g, IsThetaFunO ψ S T g → Ω (heisO ψ S T y g) = heisO ψ S T y (Ω g)) → thetaIP μ 𝓕 (Tm Φ₁) (Ω (Tm Φ₂)) = 0 := by
  first | exact @GlobalTheory.BadOrth.orth_of_disjoint | exact GlobalTheory.BadOrth.orth_of_disjoint | (intros; apply GlobalTheory.BadOrth.orth_of_disjoint <;> assumption)
