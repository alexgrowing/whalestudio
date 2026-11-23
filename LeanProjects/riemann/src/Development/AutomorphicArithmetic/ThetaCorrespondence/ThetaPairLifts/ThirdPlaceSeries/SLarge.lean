import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SEta
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PublishedInputsThirdLayer
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ThetaDataExists
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SameGaloisLevelExists
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ForcedByAutomorphicSemisimpleData
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RootsOfUnityRingLeWittIntegers
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CuspidalGaloisUnramified
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NonGaloisEtaJMem
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FixedFieldStarStableOfThirdJump
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RamificationIndexIntegralOfThirdJump
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MemberAuxiliaryPrimeSplits
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsSplitPlaceByChebotarevDensity
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsGaloisRepOfCuspidalAutomorphic
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EvOLaws
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeOpen
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EvOLawsStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EvOHypOStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsBigOSplitStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EvOTakenAllStatement
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.CoefDuty
namespace GlobalTheory.CoefDuty
theorem large_of_large_rings_alt : GlobalTheory.TwSys.Cheb → ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C), ChoiceSide D cf M Bs.exp C tp → MtInput D M tp.tup C.Q → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) → (∀ j g, ∃ z : ℤ, eExp D j g = z) → (∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) → GlobalTheory.RowTie.ChebSplit D.nd → _root_.GlobalTheory.CoefDuty.AutomorphicSideExists A M C tp.tup → _root_.GlobalTheory.CoefDuty.ForcedByAutomorphicSemisimpleData A M C tp.tup (fun D' => (SumRepresentations.hypO D' → _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D' ∧ AutomorphicSideWildInertia.ResidualIrreducibleGood D') ∧ GlobalTheory.BlockComplement.GaloisRepsCusp D') → _root_.GlobalTheory.CoefDuty.ForcedByAutomorphicSemisimpleData A M C tp.tup Large := by
  intro hCheb D cf jE A low Pq S hL eig θ Bs M C tp hCS hMt hStar hExp hSplit hCh hEx hO
  have hStd : HeckeStdPlain := GlobalTheory.T.heckeDoubleCosetOperators_standardFacts
  have hConj := fun P₁ P₂ => (_root_.GlobalTheory.T.eventually_conjunction_mono_alt D cf jE A M C tp.tup P₁ P₂).1
  have hMono := fun P₁ P₂ => (_root_.GlobalTheory.T.eventually_conjunction_mono_alt D cf jE A M C tp.tup P₁ P₂).2.1
  have E1 : _root_.GlobalTheory.CoefDuty.ForcedByAutomorphicSemisimpleData A M C tp.tup SumRepresentations.hypO :=
    _root_.GlobalTheory.T.side_eigen_rationality_alt hStd D cf jE A low Pq S hL eig θ Bs M C tp hCS hMt hStar hExp hSplit hCh
  have E2 : _root_.GlobalTheory.CoefDuty.ForcedByAutomorphicSemisimpleData A M C tp.tup GlobalTheory.SplitCoef.OSplit := by
    obtain ⟨big, hbig⟩ := _root_.GlobalTheory.T.side_multiplicity_cusp_alt D cf jE A low Pq S hL eig θ Bs M C tp hCS hMt hStar hExp hSplit hCh
    refine ⟨big, fun L hB => ?_⟩
    obtain ⟨Sp, ⟨hA⟩, -⟩ := hB
    exact hbig L Sp hA
  have E3 : _root_.GlobalTheory.CoefDuty.ForcedByAutomorphicSemisimpleData A M C tp.tup (fun D' => ∀ i, ZDecomp D'.nd i) :=
    hMono _ _ (fun D' h => GlobalTheory.T.thetaLocusDecomposesOverCoefRing_of_chebotarev hCheb D' h.2) hO
  have E4 : _root_.GlobalTheory.CoefDuty.ForcedByAutomorphicSemisimpleData A M C tp.tup (fun D' => _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D' ∧ AutomorphicSideWildInertia.ResidualIrreducibleGood D') :=
    hMono _ _ (fun D' h => h.2.1 h.1) (hConj _ _ E1 hO)
  have E5 : _root_.GlobalTheory.CoefDuty.ForcedByAutomorphicSemisimpleData A M C tp.tup TakenAll :=
    _root_.GlobalTheory.T.side_eigen_hecke_match_alt hCheb hStd D cf jE A low Pq S hL eig θ Bs M C tp hCS hMt hStar hExp hSplit hCh hEx
      (hMono _ _ (fun D' h => ⟨h.1.1, h.2.1, h.2.2⟩) (hConj _ _ E4 (hConj _ _ E2 E3)))
  have EL : _root_.GlobalTheory.CoefDuty.ForcedByAutomorphicSemisimpleData A M C tp.tup Large :=
    hMono _ _ (fun D' h => ⟨h.1, h.2.1, h.2.2⟩) (hConj _ _ E1 (hConj _ _ E2 E5))
  exact EL
end GlobalTheory.CoefDuty
end
namespace GlobalTheory.StEta
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
theorem sEta_alt_alt_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.PointStatement hL → _root_.GlobalTheory.HeightCounting.Up.EtaStatement' hL := by
  intro hP hL hPt
  refine ((((((hPt.and (_root_.GlobalTheory.T.eventually_etaJ_eq_eta_of_levelC hP hL hPt)).and (_root_.GlobalTheory.T.star_mem_LL0_at_level_c hP hL)).and (_root_.GlobalTheory.T.eExp_integer_of_levelC hP hL)).and (_root_.GlobalTheory.T.places_over_pde_isSplitPl_of_levelC hP hL)).and (_root_.GlobalTheory.T.chebSplit_of_published_inputs_at_level_c hP hL)).and
    (_root_.GlobalTheory.T.eventually_galoisRepsCusp_of_level_c hP hL)).trans (StepW.of_all ?_)
  intro K B f T w _ _ H P x l hB
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, hst⟩, hex⟩, hsp⟩, hch⟩, h4⟩ := H
  have law := fun P₁ P₂ => _root_.GlobalTheory.CoefDuty.LargeRing.evO_laws_alt (Dof x) (cfOf x) l.a.jE l.a.A l.mt.M l.c.ch l.c.tp.tup P₁ P₂
  have hin : _root_.GlobalTheory.CoefDuty.ForcedByAutomorphicSemisimpleData l.a.A l.mt.M l.c.ch l.c.tp.tup fun D' =>
      (SumRepresentations.hypO D' → _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D' ∧ AutomorphicSideWildInertia.ResidualIrreducibleGood D') ∧ GlobalTheory.BlockComplement.GaloisRepsCusp D' :=
    (law _ _).1 ((law _ _).2.1 (fun D' h hO => ⟨(h.1 hO).1, (h.1 hO).2.1⟩) (h1 P x l)) (h4 P x l)
  have hMt : MtInput (Dof x) l.mt.M l.c.tp.tup l.c.ch.Q := by
    show MtInput (Dof x) l.mt.M (fun μ j => (cfOf x).mu0 j * l.c.tp.xi μ) l.c.ch.Q
    rw [l.c.xi_eq, l.c.Q_eq]; exact l.mt.mt
  have hm := (_root_.GlobalTheory.CoefDuty.large_of_large_rings_alt hP.cheb (Dof x) (cfOf x) l.a.jE l.a.A (lowAll (Dof x)) l.Pq l.rat.S l.rat.In.hL l.rat.In.eig
    l.rat.In.θ l.b.Bs l.mt.M l.c.ch l.c.tp l.c.side hMt (hst P x l) (hex P x l) (hsp P x l) (hch P x l) hB hin)
  refine (law _ _).2.1 ?_ ((law _ _).1 hm (h2 P x l))
  intro D' h
  have hO : SumRepresentations.hypO D' := by have h' := h.1; unfold GlobalTheory.CoefDuty.Large at h'; exact h'.1
  exact ⟨h.1, h.2 hO⟩
end GlobalTheory.StEta
end
end
