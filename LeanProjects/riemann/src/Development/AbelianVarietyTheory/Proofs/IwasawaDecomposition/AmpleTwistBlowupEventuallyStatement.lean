import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AmpleTwistBlowupEventually
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ample_twist_blowup_eventually : ∀ (K : Type) [Field K] [NumberField K] (X X' N : Scheme.{0}) (s : X ⟶ Sp (𝓞 K)) (J : X.IdealSheafData)
    (b : X' ⟶ X) (ν : N ⟶ X') (EX : GlobalTheory.EffCartierData N), IsProjOver s → FinalTheorems.Blowup b J → IsFinite ν →
    EX.idealSheaf = J.comap (ν ≫ b) → ∀ L : LB X, GlobalTheory.IsAmpleLB L → ∃ T₀ : ℕ, ∀ T, T₀ ≤ T →
      GlobalTheory.IsAmpleLB (GlobalTheory.CechPic.tens (lbPow (L.pull (ν ≫ b)) T) (GlobalTheory.CechPic.dual EX.lb)) := by
  first | exact @GlobalTheory.BlowAmple.ample_twist_of_blowup | exact GlobalTheory.BlowAmple.ample_twist_of_blowup | (intros; apply GlobalTheory.BlowAmple.ample_twist_of_blowup <;> assumption)
