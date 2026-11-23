import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilDatumRealPlaceDerivativesAdd
import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.WeilFull
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilDatum_realPlaceDerivatives_add : ∀ (D : D7) (V W : HSp D) (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ) (χS χT : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (τ : D.what₂.Tau), IsInfFam θ → IsWeilDatumO ψ V W χS χT ω → ∀ X ∈ lieAt V τ, ∀ Y ∈ lieAt W τ, ∀ F F₁ F₂ : WO V W → ℂ, IsThetaFunO ψ V W F → (∀ z, HasDerivAt (fun t : ℝ => ω (oneP θ V τ X t, 1) F z) (F₁ z) 0) → (∀ z, HasDerivAt (fun t : ℝ => ω (1, oneP θ W τ Y t) F z) (F₂ z) 0) → ∀ z, HasDerivAt (fun t : ℝ => ω (oneP θ V τ X t, oneP θ W τ Y t) F z) (F₁ z + F₂ z) 0 := by
  first | exact @GlobalTheory.Mem.LieSum.hasDerivAt_add | exact GlobalTheory.Mem.LieSum.hasDerivAt_add | (intros; apply GlobalTheory.Mem.LieSum.hasDerivAt_add <;> assumption)
