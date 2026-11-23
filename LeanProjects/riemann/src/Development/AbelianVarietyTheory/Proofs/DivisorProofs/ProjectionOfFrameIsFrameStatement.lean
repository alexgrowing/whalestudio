import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectionOfFrameIsFrame
import Development.AbelianVarietyTheory.Definitions.Divisors.GrNormCompCast
open CategoryTheory Limits AlgebraicGeometry IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory GlobalTheory.QCoh GlobalTheory.LocM GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ChainPts
open Formalism.MainNotions.DIV.Cons (intO)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.projection_of_frame_is_frame : ∀ {X : Scheme.{0}} {F F₁ : X.Modules} (i : F₁ ⟶ F) (q : F ⟶ F₁), i ≫ q = 𝟙 F₁ → ∀ {r r' : ℕ} (σ : Fin r' → Fin r), Function.Injective σ → ∀ {U : X.Opens} (s : Fin r → Γ(F, U)), GlobalTheory.VB.IsFrame s → (∀ k, i.app U (q.app U (s (σ k))) = s (σ k)) → (∀ j, j ∉ Set.range σ → q.app U (s j) = 0) → GlobalTheory.VB.IsFrame (fun k => q.app U (s (σ k))) := by
  first | exact @GlobalTheory.VB.IsFrame.of_retract | exact GlobalTheory.VB.IsFrame.of_retract | (intros; apply GlobalTheory.VB.IsFrame.of_retract <;> assumption)
