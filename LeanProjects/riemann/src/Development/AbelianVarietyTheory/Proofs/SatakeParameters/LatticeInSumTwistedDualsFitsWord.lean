import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NotDvdCondN
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.FrobeniusOrbits.HostCorollaries
import Formalism.SharpRestriction.ParConsts
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.BaseFont
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PeriodDataDeRhamAdmissible
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PeriodDataProperties
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualJumpsMemWindowBoxStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GoodCoefficientRingIntegersPadicFiniteExtensionStatement
open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW.Rec

theorem fits_of_isSubOfSums : ∀ {D : D7} (L : SizeData₂ D) (C : ℝ) (j : Fin D.R.m) (ε : ℤˣ) {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l) (W : Wach P K LL) (c : D.host.E →+* ↥K.1) (κ : D.host.E →+* ↥LL.1) {ι : Type} {k r : ℕ} (Ms : ι → (↥(GK K) →* Matrix (Fin k) (Fin k) ↥LL.1)) (M' : ↥(GK K) →* Matrix (Fin r) (Fin r) ↥LL.1) (g : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → D.R.GG), Roomy L C → Formalism.MainNotions.LocalSituation.fontCore (P.PD K) → JumpIn P D j ε c κ Ms M' → (∀ τ a, Over W τ a → Reads D.host c κ τ (g a)) → ∀ T : Lat K LL, IsSubOfSums T.ρ (fun x s => Ms x s) → Fits W T (recWord L j ε g) := by
  intro D L C j ε l _ P K LL W c κ ι k r Ms M' g hR hF hJ hRd T hT
  have hO := GlobalTheory.T.goodCoefficientRing_integers_padicFiniteExtension l LL
  have hW := GlobalTheory.T.twistedDualJumps_mem_window_box L C j ε g hR
  have hjump : ∀ a τ, Over W τ a →
      JumpsInV (P.PD K) T.ρ τ {u | u ∈ jT1 (hcAt D (g a)) j (pos ε (g a))} := fun a τ hτ =>
    GlobalTheory.SubSumJumps.jumpsInV_of_isSubOfSums (P.PD K) T.ρ Ms τ _ hT
      (fun x => hJ.jumps x τ (g a) (hRd τ a hτ))
  refine ⟨?_, ?_, ?_⟩
  · exact GlobalTheory.CrysSub.isCrys_of_isSubOfSums (P.PD K) hF hO (GRep.ofLat T) Ms hJ.cont hT hJ.crys
  · intro a τ hτ u hu
    exact ((hW a).1 u (hjump a τ hτ u hu)).1
  · intro a τ hτ u hu
    exact ((hW a).1 u (hjump a τ hτ u hu)).2

end GlobalTheory.HTW.Rec
