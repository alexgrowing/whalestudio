import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselDatumBothSidesAreSides
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselDatum_both_sides_are_sides : ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [CompleteSpace Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (u u' : ℕ → ℝ), Q.IsType k r D.z D.π u → Q.IsType k r D.z' D.π' u' → ∃ νq νq', SideG k r D.z D.π u D.μW D.μN D.μG νq ∧ SideG k r D.z' D.π' u' D.μW' D.μN D.μG νq' := by
  first | exact @GlobalTheory.exists_sideG_both_of_isType | exact GlobalTheory.exists_sideG_both_of_isType | (intros; apply GlobalTheory.exists_sideG_both_of_isType <;> assumption)
