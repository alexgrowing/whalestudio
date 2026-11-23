import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CyclicStrongAtCusp
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsWeight
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Imports
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsComplementaryProductOfIsCuspidal
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.GelfandKazhdanDual
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterAboveIff
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.AlgebraicCharacterWD
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolarizedTwistAbsPow
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.ExBridge
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InfiniteQuadraticCMGoodBaseChangeSplit
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PolarizedPairBaseChangePolarizedSameWeight
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeaklyAttachedGaloisRepresentationBaseChangeRest
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.QuadLift
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsPlaceNormVEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicFormsFiniteGL
import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.BridgeJMemKwOfDecLe
import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.DRSstCrysPstJumpsDescend
import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.InducedEmbeddingExtends
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.RoadU

set_option maxHeartbeats 1000000 in

theorem holdsS_dR_all_of_good : Inputs → SphericalLevelCondition .good .dR → SphericalLevelCondition .all .dR := by
  intro hI hG E Ω _ _ _ _ _ _ l _ ι a ha π χ hS r hr w _ B hB
  have hAF : GlobalTheory.Published.AutomorphicFormsFiniteGL := GlobalTheory.automorphicFormsFiniteGL
  have hQL : QuadLift := GlobalTheory.QuadLiftBridge.quadLift hI.ac hI.js
  obtain ⟨Q, hdec, hsplit, hram, hgood⟩ := (GlobalTheory.GalCut.infinite_qcm_split_good hAF E Ω l a π w).nonempty
  obtain ⟨P, hP⟩ := hQL E Q.K Q.two a ha π hram
  obtain ⟨⟨χ', hχ'⟩, -⟩ := GlobalTheory.LiftPolar.main hAF hI.js hI.gk E Q.K l a ha π χ P hP hS.all
  have hrP := GlobalTheory.GalCut.weak_comp_res E Q.K Ω l ι a π P hP r hr
  show ClauseAt .dR π ι r w
  intro Pr AI hT A hA O _ _ _ Bw hj
  have hdA := hdec A hA
  have hjK := GlobalTheory.RealGal.bridge_j_mem_Kw_of_dec_le E Ω Q.K l A O Bw hdA
  obtain ⟨Bw', e1, e2, e3⟩ := UpperTheory.V.Af.Cq.exBridge E Q.K Ω l A O Bw hjK
  have hj' : Induces Bw' := fun x => by rw [e2]; exact hj x
  obtain ⟨w', hu, hw', hn⟩ := GlobalTheory.PlaceNormDec.exists_place_normV_eq E Ω Q w A hA hdA
  have hBP : (CG.mk P).HasSat w' (B.map (· ^ 1)) :=
    hP.sat w' 1 B (by rw [hu, pow_one]; exact hn) (by rw [hu]; exact hB)
  have hc : ClauseAt .dR P ι _ w' :=
    hG Q.K Ω l ι a ha P χ' ⟨hχ'.1, hχ'.2.1, hgood P hP⟩ _ hrP w' (hsplit w' hu) _ hBP
  have hc' := hc Pr AI hT A hw' O Bw' hj'
  have D := GlobalTheory.RealGal.dRSstCrysPstJumps_descend E Ω Q.K l Pr A O Bw Bw' e1 e2 e3 a r
  refine ⟨D.1 hc'.1, fun τ LL' τ' hτ J hJ => ?_⟩
  obtain ⟨τK, τ'', hτK, hind⟩ := GlobalTheory.induced_embedding_extends E Ω Q.K l A O Bw Bw' e1 e2 τ LL' τ' hτ
  have hJK : J.map (fun n : ℤ => (n : ℂ)) =
      ((CG.mk P).infChar (ι.toRingHom.comp τK)).map (fun z => ((a : ℂ) - 1) / 2 - z) := by
    rw [hP.inf, RingHom.comp_assoc, hτK]
    exact hJ
  have hres := D.2.2.2.2 τK J (hc'.2 τK LL' τ'' hind J hJK)
  rwa [hτK] at hres

end GlobalTheory.RoadU
