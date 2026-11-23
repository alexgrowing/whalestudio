import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.HeckeCl
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PBcSplits
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PSplitsBasic
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PSplitsPts
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PPtsOfSplits
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PIsoPts

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV UpperTheory.Gal.G3

private theorem bcSplits : BcSplits :=
  pBcSplits (pSplitsBasic (pSplitsPts pIsoPts) pPtsOfSplits)

theorem UpperTheory.Gal.crystallineComparison.Br.trBc :
    UpperTheory.Gal.crystallineComparison.Br.TrBc := by
  intro B B' R _ T g Z Y p q s _ _ hs tr htr W r c hc J _ σ hσ hsp x
  exact htr _ (pullback.snd r g) (UpperTheory.Gal.G3.bcMap g c hc) (bcMap_snd g c hc) J
    (fun j ↦ UpperTheory.Gal.G3.bcMap g (σ j) ((hσ j).trans rfl)) (fun j ↦ bcMap_snd g (σ j) _)
    ((bcSplits g p q r s hs c hc J σ hσ).2.2 hsp) x
