import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HalfMatrixMoveDeepCongruenceBound
import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SplitPart
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevChiEqOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftsInvOne
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemIffOfCarries
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.halfMatrix_move_deepCongruence_bound : ∀ (D : D7) (S T : HSp D) {a b : ℕ} (ha : S.rank = a) (hb : T.rank = b) (e : AE D) (M : WO S T), IsHalf e M → ∀ (k : ℕ), 0 < k → ∃ N₀ : ℕ, ∀ (w : GA D S) (w' : GA D T), w ∈ GfC S → w' ∈ GfC T → (∀ (P : HeightOneSpectrum (𝓞 D.host.E)) (r s : Fin a), Valued.v (adAt D.host.F P (finM S ha w r s - (1 : Matrix (Fin a) (Fin a) (EF D)) r s)) ≤ WithZero.exp (-(N₀ : ℤ))) → (∀ (P : HeightOneSpectrum (𝓞 D.host.E)) (r s : Fin b), Valued.v (adAt D.host.F P (finM T hb w' r s - (1 : Matrix (Fin b) (Fin b) (EF D)) r s)) ≤ WithZero.exp (-(N₀ : ℤ))) → ∃ t : WO S T, t ∈ stdHom S T ∧ IsHalf e t ∧ actO S T w⁻¹ w'⁻¹ M = M + k • t := by
  first | exact @GlobalTheory.AdForm.DeepMove.actO_deep | exact GlobalTheory.AdForm.DeepMove.actO_deep | (intros; apply GlobalTheory.AdForm.DeepMove.actO_deep <;> assumption)
