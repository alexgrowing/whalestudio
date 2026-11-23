import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaSubSelf
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HypothesesAbsDet
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HoweDualityFiniteOfUnitary
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatchedMapsGlobalSumStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatchedMapsLocalSumStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HoweDualityRealPlacesTrivialCharFockLiftStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatchedMapsIntertwiningStatement

open NumberField IsDedekindDomain

namespace GlobalTheory.HoweEveryPlace

theorem allInKer : GlobalTheory.Published.HoweDualityUnitary → GlobalTheory.Published.HoweDualityReal → GlobalTheory.Published.MinguezThetaGL → GlobalTheory.FunPr.Hypotheses₂ →
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs G Xc om om' →
    ∀ (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs G Xc om om' R Rf →
    ∀ N, GlobalTheory.CoinvKer.IsThetaSub om Bs.emb (GlobalTheory.SquareAgree.algD G.M Bs.ψ Bs.emb) N →
      N ≠ GlobalTheory.SquareAgree.algD G.M Bs.ψ Bs.emb →
      ∀ ΦD ∈ N, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PolMatch Bs G Xc R Rf ΦD 0 := by
  intro hU hR hMin hP F E _ _ _ _ _ σ Bs a a' G Xc om om' _ R Rf hM N hN hne
  refine GlobalTheory.T.matched_maps_intertwining hP F E σ Bs a a' G Xc om om' R Rf hM (fun v => ?_)
    (GlobalTheory.T.howeDuality_realPlaces_trivialChar_fockLift hR F E σ Bs a a' G Xc om om' R Rf hM) N hN hne
  rcases isEmpty_or_nonempty (E →ₐ[F] Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) with h | h
  · exact GlobalTheory.T.matched_maps_global_sum (GlobalTheory.T.howe_duality_finite_of_unitary hP hU) F E σ Bs a a' G Xc om om' R Rf hM v h
  · exact GlobalTheory.T.matched_maps_local_sum hP hMin F E σ Bs a a' G Xc om om' R Rf hM v h

end GlobalTheory.HoweEveryPlace
