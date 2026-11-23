import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CartFrSgn
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelWeilSectionDoublingEqMatrixCoefficientStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsWeilDatumHermitianSpaceDoubledStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingSiegelWeilSectionMemDegeneratePrincipalSStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingMapThetaIdentityAnyWeilDataStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicIwasawaDoubledGroupSelfDualLatticeStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingSeesawTensorMapPolynomialFockVectorStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubledCartanInvolutionCommuteMaximalCompactStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FockVectorFiniteUnderCompactCommutingCartanStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsEtaTildeUnramified
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilDatumOfSplittingCharacters
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilDatumAtPlaceEqLatticeIntertwinerMulDetChar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramNegTransposeDiag
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FockOfVacStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Doubling GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero)

noncomputable section

namespace GlobalTheory.TwBound

theorem hgt_io_eq_prod (D : D7) (V : HSp D) (a : GL (Fin V.rank) (AE D)) (ha : IsMaj V a) (g : GA D V) (hg : g ∈ GinfC V) :
    (hgt V a (io V (g, 1)) : ℝ) = ∏ w, GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtW V a w (GlobalTheory.AdelicU.projArch D.sp.cm.sig V.gram w g) := by
  haveI := GlobalTheory.Doubling.t2Space_adeleRing' (F := D.host.F)
  have hI := GlobalTheory.T.adelicIwasawa_doubledGroup_selfDualLattice D V (frameLat V) a (GlobalTheory.WeilAtPlace.isSelfDualC_frameLat V) ha
  rw [hgt, hI.hgtAd_eq (isCMExt_host D)]
  have hf : ∀ v, hgtFin D.sp.cm.sig (dblSp V).gram (frameLat V) v (proj D.sp.cm.sig (dblSp V).gram v (io V (g, 1))) = 1 := by
    intro v
    have e : proj D.sp.cm.sig (dblSp V).gram v (io V (g, 1)) = 1 := by
      rw [io, proj_ioH, mem_infPts_iff_forall.1 hg v, map_one, ioH_one]
    rw [e]
    exact hgtH_of_mem (continuous_absEv v) (isCompact_KFin v) (one_mem _)
  simp only [hf, finprod_one, mul_one, NNReal.coe_prod]
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [io, projArch_ioH, map_one]
  rfl

theorem tw_bound : ∀ (D : D7) (V W : HSp D) (S S' : D.what₂.Tau → SPar) (M : DSModel V S) (M' : DSModel W S') (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ) (χS χT : (AE D)ˣ →* Circle) (ω : (GA D V × GA D W →* Module.End ℂ (WO V W → ℂ))), IsInfFam θ → IsWeilDatumO ψ V W χS χT ω → ∀ (m : Measure (WO V W)) (X : Set (WO V W)), IsCovolOne (ratL W V) m X → ∀ f, IsVacVec ψ θ M M' f → ∀ a : GL (Fin V.rank) (AE D), GlobalTheory.Doubling.IsMaj V a → (∀ τ, (compAt θ τ a.1)ᴴ * (gramAt D V τ * cart M τ) * compAt θ τ a.1 = 1) → ∀ P Q, ∃ C : ℝ, ∀ g ∈ GinfC V, ‖GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ipTh m X (ω (g, 1) (ptOf ψ θ M M' f P)) (ptOf ψ θ M M' f Q)‖ ≤ C * (∏ w, GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtW V a w (GlobalTheory.AdelicU.projArch D.sp.cm.sig V.gram w g)) ^ ((W.rank : ℝ) / 2) := by
  intro D V W S S' M M' θ ψ χS χT ω hθ hω m X hm f hf a ha hmaj P Q
  have hpr : GlobalTheory.Published.WeilRepresentationUnitaryPair := fun D ψ S T χS χT hψ hS hT rS rT =>
    GlobalTheory.WeilExist.exists_isWeilDatumO D ψ hψ S T χS χT (GlobalTheory.WeilParts.exists_isEtaTilde_unramified D) hS hT rS rT
  obtain ⟨omh, homh⟩ := GlobalTheory.T.exists_weilDatum_hermitianSpaceDoubled hpr D ψ V W χS χT ω hω
  have hth := GlobalTheory.T.doublingMap_thetaIdentity_any_weilData D ψ V W χS χT ω omh hω homh
  have hco := GlobalTheory.T.siegelWeilSection_doubling_eq_matrixCoefficient D ψ V W χS χT ω omh hω hth m X hm
  have h1 := GlobalTheory.T.isFockVec_ptOf_of_isVacVec D V W S S' M M' θ ψ hω.std hθ f hf P
  have h2 := GlobalTheory.T.isFockVec_ptOf_of_isVacVec D V W S S' M M' θ ψ hω.std hθ f hf Q
  have hS := fun τ => GlobalTheory.FrameEquiv.isCartanInv_cart_model M τ
  have hT := fun τ => GlobalTheory.FrameEquiv.isCartanInv_cart_model M' τ
  have hc := GlobalTheory.T.doubled_cartanInvolution_commute_maximalCompact D θ V (cart M) a hθ hS hmaj
  have hb := GlobalTheory.T.doublingSeesawTensorMap_polynomial_fock_vector D ψ θ V W (cart M) (cart M') hω.std hθ _ _ h1 h2
  have hk := GlobalTheory.T.fock_vector_finite_under_compact_commuting_cartan D ψ θ (dblSp V) W 1 χT omh _ (cart M') homh hθ hc.1 hT (Khat V a) (isCompact_Khat V a) hc.2 _ hb
  have hmem := GlobalTheory.T.doublingSiegelWeilSection_mem_degeneratePrincipalSeries hpr D ψ V W χT omh homh m X hm _ (hth _ _ h1.1 h2.1).1 a hk
  have hI := GlobalTheory.T.adelicIwasawa_doubledGroup_selfDualLattice D V (frameLat V) a (GlobalTheory.WeilAtPlace.isSelfDualC_frameLat V) ha
  haveI := GlobalTheory.Doubling.t2Space_adeleRing' (F := D.host.F)
  obtain ⟨C, hC⟩ := GlobalTheory.Doubling.HasIwasawa.exists_norm_le continuous_absE (isCompact_Khat V a) hI hmem
  refine ⟨C, fun g hg => ?_⟩
  have e1 := (hco _ _ h1.1 h2.1).2 g
  have e2 : GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ipTh m X (ω (g, 1) (ptOf ψ θ M M' f P)) (ptOf ψ θ M M' f Q) =
      swSec V W omh m X (delta V W (ptOf ψ θ M M' f P) (ptOf ψ θ M M' f Q)) (io V (g, 1)) := by
    rw [e1]; rfl
  rw [e2, ← hgt_io_eq_prod D V a ha g hg]
  have ex : (sZero V W).re + (V.rank : ℝ) / 2 = (W.rank : ℝ) / 2 := by
    simp only [sZero, Complex.div_ofNat_re, Complex.sub_re, Complex.natCast_re]; ring
  have := hC (io V (g, 1))
  rw [ex] at this
  exact this

end GlobalTheory.TwBound

end
