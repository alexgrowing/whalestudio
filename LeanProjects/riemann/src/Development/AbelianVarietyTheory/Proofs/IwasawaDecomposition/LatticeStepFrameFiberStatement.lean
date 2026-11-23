import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LatticeStepFrameFiber
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsPrincipalMapDifferent
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasDROfAllStepsHold
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepHoldsLocalTangentFrames
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsMapUnique
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepAt
open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_step_frame_fiber : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ), p.Prime → (p : ℂ) ∈ W.nonunits → ∀ (Y : LocalSystem Xo p W) (i₀ : Idx H p) (Z B : Mdl Y i₀) (L : Lat B) (σ : E →+* ℂ) (r : ℕ) (hr : r ≤ Dw.mult σ) (g : Z.X ⟶ B.X), IsMap Z B g → Step.Holds ⟨B, L, σ, r, hr⟩ Z → ∀ (V : B.X.Opens) (n : ℕ) (m : Fin n → Γ(L.N.toMod, V)), GlobalTheory.VB.IsFrame m → ∀ x : Z.X, g x ∈ V → ∃ (U : Z.X.Opens) (hU : IsAffineOpen U) (a : GL (Fin n) Γ(Z.X, U)), x ∈ U ∧ U ≤ g ⁻¹ᵁ V ∧ LatCover.StepAt Z B g L σ r hU m a := by
  first | exact @GlobalTheory.LocM.LatNorm.stepAt_of_frame | exact GlobalTheory.LocM.LatNorm.stepAt_of_frame | (intros; apply GlobalTheory.LocM.LatNorm.stepAt_of_frame <;> assumption)
