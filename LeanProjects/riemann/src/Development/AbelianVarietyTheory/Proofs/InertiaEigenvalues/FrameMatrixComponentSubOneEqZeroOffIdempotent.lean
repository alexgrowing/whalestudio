import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdjFormula
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaPairingInvariant
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DatP
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatSelfDualOfUnimod
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatIffOfSelfDual
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelCharacterEmbeddingCompat
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open GlobalTheory.BadPlace
open Classical

namespace GlobalTheory.FrameOff

theorem cpt_frame_sub_one_eq_zero_of_suppF : ∀ (D : D7) (W : HSp D) (β : GL (Fin W.rank) (Formalism.IndefR.Lev.EAf D)) (f : AE D) (k : GA D W) (PP : Pl D.host.E), SuppF W f k → GlobalTheory.StdFrames.cpt PP (toEAf D f) = 0 → ∀ a b, GlobalTheory.StdFrames.cpt PP (((HMul.hMul (HMul.hMul ((β)⁻¹).val ((Formalism.L2.Theta.mt W k).map (toEAf D))) (β).val : Matrix (Fin (W).rank) (Fin (W).rank) (Formalism.IndefR.Datum.EAf D)) - 1) a b) = 0 := by
  intro D W β f k PP hS hf a b
  set M := Formalism.L2.Theta.mt W k with hMdef
  have hmap : M.map (toEAf D) - 1 = (M - 1).map (toEAf D) := by
    rw [Matrix.map_sub (toEAf D) (fun x y => (toEAf D).map_sub x y),
      Matrix.map_one _ (toEAf D).map_zero (toEAf D).map_one]
  have hM : ((M - 1).map (toEAf D)).map (GlobalTheory.StdFrames.cpt PP) = 0 := by
    refine Matrix.ext fun i j => ?_
    change GlobalTheory.StdFrames.cpt PP (toEAf D ((M - 1) i j)) = 0
    rw [← hS i j, RingHom.map_mul, RingHom.map_mul, hf, zero_mul]
  have hk : (HMul.hMul (HMul.hMul ((β)⁻¹).val (M.map (toEAf D))) (β).val :
        Matrix (Fin (W).rank) (Fin (W).rank) (Formalism.IndefR.Datum.EAf D)) - 1
      = ((β)⁻¹).val * (M.map (toEAf D) - 1) * (β).val := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Units.inv_mul]
  rw [hk]
  change ((((β)⁻¹).val * (M.map (toEAf D) - 1) * (β).val).map (GlobalTheory.StdFrames.cpt PP)) a b = 0
  rw [Matrix.map_mul, Matrix.map_mul, hmap, hM, Matrix.mul_zero, Matrix.zero_mul]
  rfl

end GlobalTheory.FrameOff
