import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasSumLocalSphericalZetaUnramified
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConstMemBddAut
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasSum_localSphericalZeta_unramified : GlobalTheory.Published.UnramifiedDoublingGL → ∀ (D : D7) (V : HSp D), V.rank = D.R.r → ∀ (χ : (AE D)ˣ →* Circle), Formalism.L2.Theta.ResEta D χ D.R.nV → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)), (∀ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) = v → UnrAt χ w) → ∀ φ : Gv V v → ℂ, IsLocKer V D.R.nV (val χ) v φ → ∀ (X : Type) [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ (Gv V v) X), IsUnitarisable ρ → ∀ (x : X) (B : Fam D.host.E), (∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (h : w.under (𝓞 D.host.F) = v), IsParamVec D.sp.cm.sig V.gram (frameLat V) h ρ x (B w) ∧ ∀ β ∈ B w, ‖(β : ℂ)‖ ≤ ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ (((D.R.r : ℝ) - 1) / 2)) → ∀ ℓ : X →ₗ[ℂ] ℂ, (∃ C : ℝ, ∀ g, ‖ℓ (ρ g x)‖ ≤ C) → HasSum (fun a : Gv V v ⧸ Kv V v => φ a.out * starRingEnd ℂ (ℓ (ρ a.out x))) (LvTw B (val χ) v ((1 + (D.R.t : ℂ)) / 2) / (dLoc D v : ℂ) * starRingEnd ℂ (ℓ x)) := by
  first | exact @GlobalTheory.LocZeta.hasSum_localZeta | exact GlobalTheory.LocZeta.hasSum_localZeta | (intros; apply GlobalTheory.LocZeta.hasSum_localZeta <;> assumption)
