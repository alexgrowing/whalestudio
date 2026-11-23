import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.HeckeCl
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.BrauerTraceSplitting.GenFEt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.BrauerTraceSplitting.TrTot
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.BrauerTraceSplitting.BcSplits
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.BrauerTraceSplitting.TrPush
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.DescIsoOfPb
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
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PLiesOp
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PLiesGen
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PLiesAbs
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PTrBase
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PTrPushM
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PSplitsComp
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PMultiSplit
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PFEtInj

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV CrystallineSemistableComparison UpperTheory.Ru.crystallineComparison UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen)

namespace UpperTheory.Gal.crystallineComparison.Br

private theorem splitsBasic : SplitsBasic := pSplitsBasic (pSplitsPts pIsoPts) pPtsOfSplits

private theorem bcSplits : BcSplits := pBcSplits splitsBasic

private theorem fEtBasic : FEtBasic := pFEtBasic pPtsOfSplits

private theorem etnGood : EtnGood := pEtnGood fEtBasic pEtTr

private theorem etGood : EtGood := pEtGood etnGood

private theorem bcGood : BcGood.{1} := pBcGood bcSplits (pBcGal bcSplits)

private theorem galClosD : GalClosD := pGalClosD (pSplitsPts pIsoPts) (pOrdEx pOrdStep)

private theorem hopSpec : HopSpec :=
  pHopSpec etGood bcGood (pGalClos galClosD) (pOpEx pOpTr) pOpTr pOpEt (pOpBc bcSplits (pBcGal bcSplits)) bcSplits

private theorem liesOp : LiesOp.{1} :=
  pLiesOp pLiesGen (pLiesAbs fEtBasic (pTrBase fEtBasic splitsBasic galClosD)
    (pTrPushM fEtBasic splitsBasic (pSplitsComp (pSplitsPts pIsoPts) pPtsOfSplits)
      (pMultiSplit fEtBasic splitsBasic galClosD) (pFEtInj galClosD)))

private theorem l_unit (l : ℕ) [Fact l.Prime] : IsUnit (l : Γ(G3.sp (PadicAlgCl l), ⊤)) := by
  have h : IsUnit (l : PadicAlgCl l) := (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero).isUnit
  simpa using h.map (Scheme.ΓSpecIso (CommRingCat.of (PadicAlgCl l))).inv.hom

private theorem l_ne (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) : (l : K) ≠ 0 := by
  intro h
  have h2 := congrArg (algebraMap K (PadicAlgCl l)) h
  rw [map_natCast, map_zero] at h2
  exact (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero) h2

private theorem lmap_pull {l : ℕ} [Fact l.Prime] {E E' E'' : Spc} (f : E ⟶ E')
    (tr : ∀ n : ℤ, HQ l E n 0 →ₗ[ℚ_[l]] HQ l E'' n 0) (j : ℤ) (v : HQ l E' j 0) :
    DirectSum.lmap tr (pullTot l f (DirectSum.lof ℚ_[l] ℤ (fun n : ℤ => HQ l E' n 0) j v)) =
      DirectSum.lof ℚ_[l] ℤ (fun n : ℤ => HQ l E'' n 0) j (tr j (pullHQ l f j 0 v)) := by
  unfold pullTot
  rw [DirectSum.lmap_lof, DirectSum.lmap_lof]

theorem heckeCl : HeckeCl := by
  intro l _ K L _ H θ C T hr γ m d hfet hlies
  have hl := l_ne l K
  have hu := l_unit l
  have hgood : (etG l K (PadicAlgCl l)).Good := bcGood _ _ (etGood l _ hu)
  have hs := genFEt l (OK l K) K hl C.p T
  obtain ⟨hsF, hsE, -⟩ := id hs
  obtain ⟨hcF, hcE, -⟩ := bcSplits (Spec.map (CommRingCat.ofHom (algebraMap K (PadicAlgCl l))))
    (pullback.snd C.p (gen (OK l K) K)) (pullback.snd (T.p ≫ C.p) (gen (OK l K) K))
    (pullback.snd C.p (gen (OK l K) K)) (G3.bcMap (gen (OK l K) K) T.p rfl)
    (bcMap_snd _ _ _) (𝟙 _) (Category.id_comp _) PEmpty (fun j ↦ j.elim) (fun j ↦ j.elim)
  have htrn : ∀ n : ℤ, ∃ tr, (etn l (G3.sp (PadicAlgCl l)) n 0).IsTr
      (pullback.snd (pullback.snd C.p (gen (OK l K) K))
        (Spec.map (CommRingCat.ofHom (algebraMap K (PadicAlgCl l)))))
      (pullback.snd (pullback.snd (T.p ≫ C.p) (gen (OK l K) K))
        (Spec.map (CommRingCat.ofHom (algebraMap K (PadicAlgCl l)))))
      (G3.bcMap (Spec.map (CommRingCat.ofHom (algebraMap K (PadicAlgCl l))))
        (G3.bcMap (gen (OK l K) K) T.p rfl) (bcMap_snd _ _ _)) tr :=
    fun n ↦ (etnGood l _ hu n 0).tr _ _ _ (bcMap_snd _ _ _)
  choose trn htrn using htrn
  have htot := trTot l _ _ _ trn htrn
  have hbc := trBc (et l (G3.sp (PadicAlgCl l)))
    (Spec.map (CommRingCat.ofHom (algebraMap K (PadicAlgCl l))))
    (pullback.snd C.p (gen (OK l K) K)) (pullback.snd (T.p ≫ C.p) (gen (OK l K) K))
    (G3.bcMap (gen (OK l K) K) T.p rfl) (bcMap_snd _ _ _) (DirectSum.lmap trn) htot
  have hF := hfet.1
  have hE := hfet.2.1
  obtain ⟨trg, htrg⟩ := hgood.tr H.q (H.s γ ≫ H.q) (H.s γ) rfl
  have hop_eq := (hopSpec l hl H (PadicAlgCl l) γ d hfet).2 trg htrg
  have hp : ∀ j : ℕ, LateralTheory.EtaleTrace.IsPush l
      (G3.bcMap (Spec.map (CommRingCat.ofHom (algebraMap K (PadicAlgCl l))))
        (G3.bcMap (gen (OK l K) K) T.p rfl) (bcMap_snd _ _ _)) j (trn j) :=
    fun j ↦ trPush l _ _ _ (bcMap_snd _ _ _) j (trn j) (htrn j)
  have hc : corrP (mdl C) T = G3.bcMap (Spec.map (CommRingCat.ofHom (algebraMap K (PadicAlgCl l))))
      (G3.bcMap (gen (OK l K) K) T.p rfl) (bcMap_snd _ _ _) := by
    unfold corrP GlobalTheory.Et.geomMap Model.genMap
    rfl
  have hp2 : ∀ j : ℕ, LateralTheory.EtaleTrace.IsPush l (corrP (mdl C) T) j (trn j) := by
    intro j
    rw [hc]
    exact hp j
  have hk := fun j : ℕ ↦ hkOfPush l K (mdl C) T hr j _ (hp2 j)
  refine ⟨_, fun j ↦ ⟨hk j, fun v ↦ ?_⟩⟩
  have key := liesOp C γ T.p T.r hr m T.d hlies hs (etG l K (PadicAlgCl l)) hgood
    (DirectSum.lmap trn) trg hbc htrg
    (DirectSum.lof ℚ_[l] ℤ (fun n : ℤ ↦ HQ l (mdl C).spc n 0) j v)
  rw [hop_eq, LinearMap.comp_apply]
  refine key.trans ?_
  congr 2
  exact lmap_pull _ trn j v

end UpperTheory.Gal.crystallineComparison.Br
