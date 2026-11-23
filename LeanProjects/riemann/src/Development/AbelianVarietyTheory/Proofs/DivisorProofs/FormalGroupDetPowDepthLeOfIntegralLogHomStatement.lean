import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupDetPowDepthLeOfIntegralLogHom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueEqZeroIffV
open NumberField MvPowerSeries IsLocalRing ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes GlobalTheory.PrimePart
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formalGroupDetPowDepth_le_of_integralLogHom : ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)), ∀ (i d d' k : ℕ) (G : LogFGL v d) (G' : LogFGL v d') (φ : Fin d' → MvPowerSeries (Fin d) C) (M : Matrix (Fin d') (Fin d) C), IsIntHom G G' φ M → ∀ u : Fin i → Fin d → C, detDepth G u k ≤ detDepth G' (fun a => M.mulVec (u a)) k := by
  first | exact @GlobalTheory.DepthMono.detDepth_le_of_isIntHom | exact GlobalTheory.DepthMono.detDepth_le_of_isIntHom | (intros; apply GlobalTheory.DepthMono.detDepth_le_of_isIntHom <;> assumption)
