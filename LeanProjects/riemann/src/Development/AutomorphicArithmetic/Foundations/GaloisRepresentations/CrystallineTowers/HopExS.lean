import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CrystallineTowers.LocTower
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PHopSpec
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PEtGood
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PEtnGood
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PEtTr
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PFEtBasic
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PPtsOfSplits
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PBcGood
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PBcGal
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PBcSplits
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PSplitsBasic
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PSplitsPts
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PIsoPts
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PGalClos
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PGalClosD
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.POrdEx
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.POrdStep
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.POpEx
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.POpTr
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.POpEt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PullIdentityMove

open UpperTheory.Gal.Seam

private theorem bcSplits : UpperTheory.Gal.G3.BcSplits :=
  UpperTheory.Gal.G3.pBcSplits (UpperTheory.Gal.G3.pSplitsBasic (UpperTheory.Gal.G3.pSplitsPts UpperTheory.Gal.G3.pIsoPts) UpperTheory.Gal.G3.pPtsOfSplits)

private theorem hopSpec : UpperTheory.Gal.G3.HopSpec :=
  UpperTheory.Gal.G3.pHopSpec
    (UpperTheory.Gal.G3.pEtGood (UpperTheory.Gal.G3.pEtnGood (UpperTheory.Gal.G3.pFEtBasic UpperTheory.Gal.G3.pPtsOfSplits) UpperTheory.Gal.G3.pEtTr))
    (UpperTheory.Gal.G3.pBcGood bcSplits (UpperTheory.Gal.G3.pBcGal bcSplits))
    (UpperTheory.Gal.G3.pGalClos (UpperTheory.Gal.G3.pGalClosD (UpperTheory.Gal.G3.pSplitsPts UpperTheory.Gal.G3.pIsoPts)
      (UpperTheory.Gal.G3.pOrdEx UpperTheory.Gal.G3.pOrdStep)))
    (UpperTheory.Gal.G3.pOpEx UpperTheory.Gal.G3.pOpTr) UpperTheory.Gal.G3.pOpTr UpperTheory.Gal.G3.pOpEt
    (UpperTheory.Gal.G3.pOpBc bcSplits (UpperTheory.Gal.G3.pBcGal bcSplits)) bcSplits

theorem UpperTheory.Gal.Seam.hopExS :
    True → HopEx := by
  intro _ l _ k Ω _ _ _ _ _ H hN g
  obtain ⟨d, hd⟩ := hN.2.2 g
  have hl : (l : k) ≠ 0 := by
    intro h
    have h0 : (l : Ω) = 0 := by rw [← map_natCast (algebraMap k Ω), h, map_zero]
    exact (Fact.out : l.Prime).ne_zero (Nat.cast_eq_zero.mp h0)
  exact (hopSpec l hl H Ω g d hd).1
