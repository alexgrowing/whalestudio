import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.EventuallyAllScaleContextsAndOfBoth
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LogCondLeThree
import Development.AutomorphicArithmetic.CharacterBoxes.HostOfField
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormPrimesAndLevelPrimeUnconditional
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SmallPrimeOneOfPrimesRel
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.KitOfPoints
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.WeightWindowRequirementHostOfPoint
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.WindowShareRequirementClosedFormProofStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsObjectsOfAdmissibleTwistDatumStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HasWithDutyWallAndChoices
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FixAndWinOfNumAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.VolumesEqMassesOfUnfold
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLayerParametersAdmissible
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RecExGOfRecAtG
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TwGoodOneSetDiv

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc NumberField IsDedekindDomain

namespace GlobalTheory.Fc

theorem isSel_of_sAnd {Bd : BdT} {Q R : V4.Slot} {Lk : LkT Bd} {E : Par → BdP Bd} {𝒜 : FamClass} {σ : RawSel Bd 𝒜}
    (s : IsSel (sAnd Q R) Lk E 𝒜 σ) : IsSel Q Lk E 𝒜 σ := fun Fm hc => by
  obtain ⟨κ, h1, h2, h3⟩ := s Fm hc
  refine ⟨κ, h1, h2, fun x hx i => ⟨?_, (h3 x hx i).2⟩⟩
  obtain ⟨K, β, b, a0, a1, a2, a3⟩ := (h3 x hx i).1
  exact ⟨K, β, b, a0, a1.1, a2, a3⟩

end GlobalTheory.Fc
