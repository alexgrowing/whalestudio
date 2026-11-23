import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CyclicStrongAtCusp
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Imports
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicFormsFiniteGL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolarizedTwistAbsPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLocCompAndIsLocLoc
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PlaceOverTransportRingIso
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.ExBridge
import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.RamificationIdxEqOneAndInertiaDegEqOne
import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.BridgeJMemKwOfDecLe
import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.DRSstCrysPstJumpsDescend
import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.IwahoriSphericalTransfer
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InfiniteQuadraticCMGoodBaseChangeSplit
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PolarizedPairBaseChangePolarizedSameWeight
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeaklyAttachedGaloisRepresentationBaseChangeRest
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.QuadLift
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem GlobalTheory.RoadU.holdsS_all_crys : Inputs → SphericalLevelCondition .good .crys → SphericalLevelCondition .all .crys := by
  intro hIn hgood E Ω _ _ _ _ _ _ l _ ι a ha π χ hsc r hr w _ B hB
  have hAF := GlobalTheory.automorphicFormsFiniteGL
  have hQL : QuadLift := GlobalTheory.QuadLiftBridge.quadLift hIn.ac hIn.js
  intro Pr AI hT A hA O _ _ _ Bw hj σ hσ hsph
  obtain ⟨Q, hQ1, hQ2, hQ3, hQ4⟩ := (GlobalTheory.GalCut.infinite_qcm_split_good hAF E Ω l a π w).nonempty
  obtain ⟨Pc, hPc⟩ := hQL E Q.K Q.two a ha π hQ3
  have hres := GlobalTheory.GalCut.weak_comp_res E Q.K Ω l ι a π Pc hPc r hr
  obtain ⟨⟨χ', hχ'⟩, -⟩ := GlobalTheory.LiftPolar.main hAF hIn.js hIn.gk E Q.K l a ha π χ Pc hPc hsc
  have hin : InScope .good l Pc χ' := ⟨hχ'.1, hχ'.2.1, hQ4 Pc hPc⟩
  have hdec := hQ1 A hA
  have hjK := GlobalTheory.RealGal.bridge_j_mem_Kw_of_dec_le E Ω Q.K l A O Bw hdec
  obtain ⟨Bw', e1, e2, e3⟩ := UpperTheory.V.Af.Cq.exBridge E Q.K Ω l A O Bw hjK
  have hj' : Induces Bw' := fun x => by rw [e2]; exact hj x
  obtain ⟨w', h', i, hi⟩ := GlobalTheory.PlaceIsoDec.exists_placeIso_of_dec_le_range E Ω Q.K w A hA hdec
  have hund : w'.under (𝓞 E) = w := by
    have := GlobalTheory.PlaceIsoDec.liesOver_of_isPlaceOver hA h'
    ext1
    exact this.over.symm
  obtain ⟨c, -, -, hq, -⟩ := GlobalTheory.WeilTransport.weil_equiv E Ω A w hA Q.K Ω A w' h' (RingEquiv.refl Ω) (algebraMap E Q.K) i hi
  have hB' : (CG.mk Pc).HasSat w' B := by
    have := hPc.sat w' 1 B (by rw [pow_one, hund, hq]) (by rw [hund]; exact hB)
    simpa using this
  obtain ⟨σ', hσ', -⟩ := GlobalTheory.CuspRep.LocEx.exists_isLocComp hAF Q.K a Pc w'
  obtain ⟨e, he⟩ := hPc.loc w w' i hi.cont hi.loc σ σ' hσ hσ'
  have hsph' := (GlobalTheory.CompletionIso.iwahori_spherical_transfer E Q.K w w' i hi.cont a σ σ' e he).2 hsph
  have hcr : ClauseAt .crys Pc ι (r.comp (UpperTheory.V.Af.Bc.res E Ω Q.K)) w' :=
    hgood Q.K Ω l ι a ha Pc χ' hin _ hres w' (hQ2 w' hund) B hB'
  exact (GlobalTheory.RealGal.dRSstCrysPstJumps_descend E Ω Q.K l Pr A O Bw Bw' e1 e2 e3 a r).2.2.1
    (hcr Pr AI hT A h' O Bw' hj' σ' hσ' hsph')
