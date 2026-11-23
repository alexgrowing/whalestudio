import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedVectorEqOfStandardData
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsTwIffCanonEq
import Formalism.LocalToGlobal.KernelLattices.TopPin
import Formalism.LocalToGlobal.KernelLattices.InterlaceAll
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JetsInIffStepField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianChartComplexRationalIntegralFormsStatement
import Formalism.LocalToGlobal.KernelLattices.ColumnData.DiagramFitsSourceRank
import Formalism.UnipotentAdelicQuotients.WeylLatDual
import Formalism.LocalRingCardinality.FactDelDualNabla
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DominantWeightPolynomialFunctionalMinorsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MainProofStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPolynomialModelValueRationalStepStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LatticeIffIntegralWeylCoordinatesStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LatSCore

theorem prSC_int_iff (hW : WeylLatticeDuality.Stmt) {D : D7} (Pl : Examples₂.EntPl D) (O : ∀ u μ, GL3Theta.LiftObj D (D.chTw u μ)) (Bs : PlaceMatrixFamily D)
    (hC : CanOnto Pl) (u : D.what₂.Word) (μ : D.what₂.Tup) (w : D.what₂.places.Pl) (i : ℕ) (hi : i < D.R.m) (c : (D.chTw u μ).cls i)
    (v : ValQ O u μ i) :
    (∀ J : KM.ColChoice (D.R.N i) (nuD D u i),
        ‖prSC Pl O Bs u μ w i c v (MvPolynomial.map (Int.castRingHom _) (KM.nablaX (D.R.N i) (nuD D u i) J))‖ ≤ 1) ↔
      srcFun Pl Bs u μ w i c (secC O u μ i v) ∈
        WeylLatticeDuality.DelW (D.what₂.places.resChar w) D.what₂.Tau (D.R.N i) (nuT D u i) := by
  have hS := canS_of Pl Bs hC u μ w i hi c (secC O u μ i v)
  have hcan : canM D w (D.R.N i) (nuD D u i) (prSC Pl O Bs u μ w i c v) = srcFun Pl Bs u μ w i c (secC O u μ i v) :=
    canInv_spec D w (D.R.N i) (nuD D u i) _ hS
  rw [← hcan]
  exact hW (D.what₂.places.resChar w) _ D.what₂.Tau (tauPl D) (tauPl_bij D) (D.R.N i) (nuD D u i) (nuT D u i)
    (diagram_fits_source_rank D u i hi).1 (diagram_fits_source_rank D u i hi).2 (prSC Pl O Bs u μ w i c v)

theorem latS_at_class : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (Y : DivX (I.rec7 l Z)) (O : ∀ u a, GL3Theta.LiftObj (I.rec7 l Z) ((I.rec7 l Z).chTw u a)) (Pl : Examples₂.EntPl (I.rec7 l Z)) (Bs : PlaceMatrixFamily (I.rec7 l Z)), I.QpIs Y.Qp → I.StdO l Z Y.Qp O → BasOk Pl O Bs → (∀ u a w, LevFree Y u a w → ∀ i, i ≤ B.R.m → ∀ c τ j k, ∃ x : (I.rec7 l Z).what₂.LL, Bs u a w i c τ j k = Pl.iL w x) → ∀ (u : B.Word) (μ : I.ι) (w : (I.rec7 l Z).what₂.places.Pl), LevFree Y u μ w → ∀ (i : ℕ) (hi : i < B.R.m) (eY : (I.chain l u μ).Y i ≃ Formalism.L2.Forms.Fr (I.rec7 l Z) i hi.le), I.IdY l Z u μ i hi.le eY → ∀ (c : (I.stp u μ i).Cl) (f : (I.chain l u μ).Y i → ℂ), (∃ P ∈ Formalism.L2.Forms.RatSpan (I.rec7 l Z) ((I.fm l u μ).lam i), ∀ z, f z = fnOf (gramC (gramN (I.rec7 l Z) i hi.le) (embT (I.rec7 l Z))) (shiftOf (lamTG (I.fm l u μ) i)) 1 P (eY z)) → ∀ Bm : GL (Fin ((I.rec7 l Z).R.N i)) (I.rec7 l Z).host.E, Formalism.L2.Forms.IsLocBasis ((I.rec7 l Z).what₂.places.resChar w) (((I.stp u μ i).rep c).1.1.deco.1.N : Set (Sp B.fields.E (B.R.N i))) Bm → ((∃ P ∈ Formalism.L2.Forms.IntSpan (I.rec7 l Z) w ((I.fm l u μ).lam i), ∀ z, f z = fnOf (gramC (gramN (I.rec7 l Z) i hi.le) (embT (I.rec7 l Z))) (shiftOf (lamTG (I.fm l u μ) i)) (atInf (embT (I.rec7 l Z)) ((Bm⁻¹ : GL (Fin ((I.rec7 l Z).R.N i)) (I.rec7 l Z).host.E) : Matrix (Fin ((I.rec7 l Z).R.N i)) (Fin ((I.rec7 l Z).R.N i)) (I.rec7 l Z).host.E)) P (eY z)) ↔ ∃ v : ValQ O u μ i, evC O u μ i v = f ∧ ∀ J : KM.ColChoice ((I.rec7 l Z).R.N i) (nuD (I.rec7 l Z) u i), ‖prSC Pl O Bs u μ w i c v (MvPolynomial.map (Int.castRingHom _) (KM.nablaX ((I.rec7 l Z).R.N i) (nuD (I.rec7 l Z) u i) J))‖ ≤ 1) := by
  intro B X I hOk hPins l Z Y O Pl Bs hQp hStd hBas hEnt u μ w hw i hi eY hId c f hrat Bm hBm
  have hi' : i < (I.rec7 l Z).R.m := hi
  have key := prSC_int_iff GlobalTheory.T.weyl_lattice_duality Pl O Bs (GlobalTheory.T.toy_entPl_canOnto _ Pl) u μ w i hi' c
  constructor
  · intro hL
    obtain ⟨v, hv⟩ := GlobalTheory.T.exists_polynomialModel_value_rational_step I hOk hPins l Z Y O Pl Bs hQp hStd hBas hEnt u μ w hw i hi eY hId c f hrat
    refine ⟨v, hv, ?_⟩
    rw [key v]
    exact (GlobalTheory.T.lattice_iff_integralWeyl_coordinates I hOk hPins l Z Y O Pl Bs hQp hStd hBas hEnt u μ w hw i hi eY hId c f hrat Bm hBm v hv).1 hL
  · rintro ⟨v, hv, hJ⟩
    rw [key v] at hJ
    exact (GlobalTheory.T.lattice_iff_integralWeyl_coordinates I hOk hPins l Z Y O Pl Bs hQp hStd hBas hEnt u μ w hw i hi eY hId c f hrat Bm hBm v hv).2 hJ

end GlobalTheory.LatSCore
