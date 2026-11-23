import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedVectorEqOfStandardData
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsTwIffCanonEq
import Formalism.LocalToGlobal.KernelLattices.TopPin
import Formalism.LocalToGlobal.KernelLattices.InterlaceAll
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JetsInIffStepField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DominantWeightPolynomialFunctionalMinorsStatement
import Formalism.LocalToGlobal.KernelLattices.ColumnData.DiagramFitsSourceRank
import Formalism.UnipotentAdelicQuotients.WeylLatDual
import Formalism.LocalToGlobal.Divisibility.NumbersLemmas
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MemLocWDelAtrIff
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TrueChainComplexFormsStabiliserLaw
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TrueWeightConsecutiveStepsPartition
import Formalism.LocalToGlobal.GlobalTheory.GL6.PBwLocGen
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeylLatticeDualInvariantUnitIffStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemWeylLatticeIntegralSpanIffPadicFunctionStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalBasisAndEmbeddedBasisDifferByUnimodularInteStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DualLatticeClassLocalizationEqUnimodularCompanioStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.LocDictT

theorem eval_map_actP {K S ι : Type} [Field K] [CommRing S] [Fintype ι] {n : ℕ} (φ : K →+* S)
    (lam : ι → DomWeight n) (g : ι → GL (Fin n) K) (P : Pol K ι n) (y : ι → Matrix (Fin n) (Fin n) S) :
    MvPolynomial.eval (fun k : ι × Fin n × Fin n => y k.1 k.2.1 k.2.2) (MvPolynomial.map φ (actP lam g P)) =
      φ (detTwK lam g) * MvPolynomial.eval (fun k : ι × Fin n × Fin n =>
        (((((g k.1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ).map φ) * y k.1) k.2.1 k.2.2) (MvPolynomial.map φ P) := by
  have key : ((MvPolynomial.eval (fun k : ι × Fin n × Fin n => y k.1 k.2.1 k.2.2)).comp
      ((MvPolynomial.map φ).comp (trAct g).toRingHom)) =
      (MvPolynomial.eval (fun k : ι × Fin n × Fin n =>
        (((((g k.1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ).map φ) * y k.1) k.2.1 k.2.2)).comp (MvPolynomial.map φ) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [trAct]
    · intro v
      simp [trAct, Formalism.GradedWeylDivisibility.blockAct, Matrix.mul_apply]
  unfold actP
  rw [LinearMap.smul_apply, MvPolynomial.smul_eq_C_mul, map_mul, map_mul, MvPolynomial.map_C, MvPolynomial.eval_C]
  congr 1
  exact RingHom.congr_fun key P

theorem invTr_bc_inv_transpose {E K : Type} [Field E] [Field K] {n : ℕ} (φ : E →+* K) (Bm : GL (Fin n) E) :
    ((((inside₂ K n (bc φ Bm))⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))ᵀ = (Bm : Matrix (Fin n) (Fin n) E).map φ := by
  rfl

theorem iL_emb {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l))
    (Pl : Examples₂.EntPl (I.rec7 l Z)) (w : (I.rec7 l Z).what₂.places.Pl) (τ : (I.rec7 l Z).what₂.Tau) (x : B.fields.E) :
    Pl.iL w (B.fields.emb τ x) = TaylorLogMetric.tauEmb (I.rec7 l Z) (Pl.lam w) τ x := by
  refine (Pl.iL_lam w (B.fields.emb τ x)).trans ?_
  have h : TaylorLogMetric.embT (I.rec7 l Z) τ x = B.embLL (B.fields.emb τ x) := by
    rw [GlobalTheory.Pdv.FormsStd.embT_eq I l Z]
    rfl
  unfold TaylorLogMetric.tauEmb
  rw [h]
  rfl

theorem detPow_map {K S : Type} [Field K] [Field S] {n : ℕ} (φ : K →+* S) (g : GL (Fin n) K) (e : ℤ) :
    φ (detPow K n g e) = ((((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ).map φ).det ^ e := by
  unfold detPow
  rw [Units.val_zpow_eq_zpow_val, map_zpow₀]
  congr 1
  show φ (g : Matrix (Fin n) (Fin n) K).det = _
  rw [RingHom.map_det, RingHom.mapMatrix_apply, ← Matrix.det_transpose]
  rfl

theorem atBas_apply {D : D7} (P : Examples₂.EntPl D) (w : D.what₂.places.Pl) {N : ℕ}
    (M : D.what₂.Tau → Matrix (Fin N) (Fin N) (Cw D w)) (Q : MvPolynomial (GL3Theta.FrV D N) D.what₂.LL) (y : FrP D w N) :
    atBas P w M Q y = MvPolynomial.eval (fun k : GL3Theta.FrV D N => (M k.1 * y k.1) k.2.1 k.2.2) (MvPolynomial.map (P.iL w) Q) := rfl

theorem final_eq {S T LL : Type} [Field S] [CommRing LL] [Fintype T] {N : ℕ} (φ : LL →+* S)
    (P : MvPolynomial (T × Fin N × Fin N) LL) (A g M y : T → Matrix (Fin N) (Fin N) S) (e : T → ℤ)
    (hM : ∀ τ, M τ = A τ * g τ) :
    (∏ τ, (g τ).det ^ e τ) * ((∏ τ, (A τ).det ^ e τ) *
      MvPolynomial.eval (fun k : T × Fin N × Fin N => (A k.1 * (g k.1 * y k.1)) k.2.1 k.2.2) (MvPolynomial.map φ P)) =
    (∏ τ, (M τ).det ^ e τ) * MvPolynomial.eval (fun k : T × Fin N × Fin N => (M k.1 * y k.1) k.2.1 k.2.2) (MvPolynomial.map φ P) := by
  simp only [hM, Matrix.det_mul, mul_zpow, Finset.prod_mul_distrib, Matrix.mul_assoc]
  ring

theorem detTwisted_polyEval_mul_factor_eq_of_eq {S T LL : Type} [Field S] [CommRing LL] [Fintype T] {N : ℕ} (φ : LL →+* S)
    (P : MvPolynomial (T × Fin N × Fin N) LL) (A G g M y : T → Matrix (Fin N) (Fin N) S) (e e' : T → ℤ)
    (hA : ∀ τ, G τ = A τ) (he : ∀ τ, e' τ = e τ) (hM : ∀ τ, M τ = A τ * g τ) :
    (∏ τ, (g τ).det ^ e τ) * ((∏ τ, (A τ).det ^ e' τ) *
      MvPolynomial.eval (fun k : T × Fin N × Fin N => (G k.1 * (g k.1 * y k.1)) k.2.1 k.2.2) (MvPolynomial.map φ P)) =
    (∏ τ, (M τ).det ^ e τ) * MvPolynomial.eval (fun k : T × Fin N × Fin N => (M k.1 * y k.1) k.2.1 k.2.2) (MvPolynomial.map φ P) := by
  have h1 : G = A := funext hA
  have h2 : e' = e := funext he
  subst h1 h2
  exact final_eq φ P G g M y e' hM

set_option maxHeartbeats 1000000 in

theorem mem_locW_iff_delW : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (l0 : I.Law0 l) (Y : DivX (I.rec7 l Z)) (O : ∀ u a, GL3Theta.LiftObj (I.rec7 l Z) ((I.rec7 l Z).chTw u a)) (Pl : Examples₂.EntPl (I.rec7 l Z)) (Bs : PlaceMatrixFamily (I.rec7 l Z)), I.QpIs Y.Qp → I.StdO l Z Y.Qp O → BasOk Pl O Bs → (∀ u a w, LevFree Y u a w → ∀ i, i ≤ B.R.m → ∀ c τ j k, ∃ x : (I.rec7 l Z).what₂.LL, Bs u a w i c τ j k = Pl.iL w x) → (∀ u a i, i < B.R.m → UnfIsAll (O u a) i) → ColIn.JetsIn I → ∀ (u : B.Word) (μ : I.ι) (w : (I.rec7 l Z).what₂.places.Pl), LevFree Y u μ w → ∀ i, i < (I.rec7 l Z).R.m → ∀ (c' : (I.stp u μ (i + 1)).Cl) (z : VV B.LL (lamT (B.hcW u) (i + 1))), (z ∈ locW B.places w (delAtr B.fields.emb (lamT (B.hcW u) (i + 1)) ((I.stp u μ (i + 1)).Lsh c'.1 ((I.stp u μ (i + 1)).rep c'))) ↔ (fun y => (∏ τ, (Bs u μ w (i + 1) c' τ).det ^ (-((I.rec7 l Z).chTw u μ).sDiv i τ)) * atBas Pl w (Bs u μ w (i + 1) c') (show MvPolynomial (GL3Theta.FrV (I.rec7 l Z) ((I.rec7 l Z).R.N (i + 1))) (I.rec7 l Z).what₂.LL from z.1) y) ∈ WeylLatticeDuality.DelW ((I.rec7 l Z).what₂.places.resChar w) (I.rec7 l Z).what₂.Tau ((I.rec7 l Z).R.N (i + 1)) (extNu ((I.rec7 l Z).R.N (i + 1)) (nuT (I.rec7 l Z) u i))) := by
  intro B X I hOk hPins l Z l0 Y O Pl Bs hQp hStd hBas hEnt hUnf hJets u μ w hLF i hi c' z
  obtain ⟨hlat, hloc⟩ := GlobalTheory.T.dualLattice_class_localization_eq_unimodularCompanion I hOk hPins l Z Y u μ w hLF (i + 1) hi c'
  haveI : Fact (B.places.resChar w).Prime := ⟨B.places.resChar_prime w⟩
  obtain ⟨Bm, hBm⟩ := Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.LocB.exists_isLocBasis (B.places.resChar w) B.fields.E _ hlat.fg hlat.span_eq_top
  have hBmN : Formalism.L2.Forms.IsLocBasis (B.places.resChar w) (((O u μ).lat (i + 1) c').1 : Set (Fin ((I.rec7 l Z).R.N (i + 1)) → (I.rec7 l Z).host.E)) Bm := by
    intro x
    rw [hStd.lat u μ (i + 1) c']
    exact (hloc x).symm.trans (hBm x)
  rw [GlobalTheory.WeylLocOnePlace.mem_locW_delAtr_iff B.fields.emb B.embLL B.places (I.rec7 l Z).plEq
    (fun w x hx => (I.rec7 l Z).val_eq w x hx)
    (lamT (B.hcW u) (i + 1)) (lamT (B.hcW u) (i + 1)) (fun _ => rfl) _ hlat w Bm hBm z]
  rw [GlobalTheory.T.mem_weylLatticeIntegralSpan_iff_padic_function B.embLL B.places w (Pl.iL w) (Pl.iL_int w) (lamT (B.hcW u) (i + 1)) _
    (((rhoVr B.fields.emb (lamT (B.hcW u) (i + 1))) Bm⁻¹) z).2]
  obtain ⟨n, hw, hn, hnat, hds⟩ := GlobalTheory.KerWtStep.trueWt_step (I.rec7 l Z) u _ _ _ ((I.tw l l0 Z).fm u μ) i hi
  have hlam := GlobalTheory.Pdv.FormsStd.lamTG_eq I l Z l0 u μ
  have e : (fun τ => (lamT (B.hcW u) (i + 1) τ).natW) = extNu ((I.rec7 l Z).R.N (i + 1)) (nuT (I.rec7 l Z) u i) := by
    funext τ r
    rw [← hlam]
    refine (hnat τ r).trans ?_
    congr 1
    funext τ' r'
    exact hw τ' r'
  have eds : ∀ τ, (lamT (B.hcW u) (i + 1) τ).detShift = -((I.rec7 l Z).chTw u μ).sDiv i τ := fun τ => by
    rw [← hlam]
    exact hds τ
  rw [e]
  choose g hg1 hg2 hg3 using fun τ => GlobalTheory.T.localBasis_and_embeddedBasis_differ_by_unimodular_integral (I.rec7 l Z) (Pl.lam w) τ _ Bm (Bs u μ w (i + 1) c' τ) hBmN
    (hBas u μ w (i + 1) hi c' τ)
  refine (GlobalTheory.T.weyl_lattice_dual_invariant_unit_iff _ _ _ _ g (∏ τ, (g τ).det ^ (-((I.rec7 l Z).chTw u μ).sDiv i τ)) hg1 hg2 ?_ _).trans ?_
  · rw [norm_prod]
    exact Finset.prod_eq_one fun τ _ => by rw [norm_zpow, hg2, _root_.one_zpow]
  · apply iff_of_eq
    congr 1
    funext y
    have hM : ∀ τ, ((((vlBdF B.fields.emb fun _ => Bm)⁻¹ τ : GL (Fin (B.R.N (i + 1))) B.LL) :
        Matrix (Fin (B.R.N (i + 1))) (Fin (B.R.N (i + 1))) B.LL)ᵀ).map (Pl.iL w) =
        (Bm : Matrix (Fin (B.R.N (i + 1))) (Fin (B.R.N (i + 1))) B.fields.E).map (TaylorLogMetric.tauEmb (I.rec7 l Z) (Pl.lam w) τ) := by
      intro τ
      rw [show (vlBdF B.fields.emb fun _ => Bm)⁻¹ τ = (inside₂ _ _ (bc (B.fields.emb τ) Bm))⁻¹ from rfl,
        invTr_bc_inv_transpose]
      ext a b
      exact iL_emb I l Z Pl w τ _
    have hdet : Pl.iL w (detTwK (lamT (B.hcW u) (i + 1)) (vlBdF B.fields.emb fun _ => Bm)⁻¹) =
        ∏ τ, ((Bm : Matrix (Fin (B.R.N (i + 1))) (Fin (B.R.N (i + 1))) B.fields.E).map
          (TaylorLogMetric.tauEmb (I.rec7 l Z) (Pl.lam w) τ)).det ^ (lamT (B.hcW u) (i + 1) τ).detShift := by
      unfold detTwK
      rw [map_prod]
      refine Finset.prod_congr rfl fun τ _ => ?_
      rw [detPow_map]
      exact congrArg (fun M => Matrix.det M ^ (lamT (B.hcW u) (i + 1) τ).detShift) (hM τ)
    beta_reduce
    rw [GlobalTheory.WeylLocOnePlace.rhoVr_inv_coe]
    have hev := eval_map_actP (Pl.iL w) (lamT (B.hcW u) (i + 1)) (vlBdF B.fields.emb fun _ => Bm)⁻¹ z.1 (fun τ => g τ * y τ)
    beta_reduce at hev
    erw [hev]
    erw [atBas_apply, hdet]
    exact detTwisted_polyEval_mul_factor_eq_of_eq (Pl.iL w) z.1
      (fun τ => (Bm : Matrix (Fin (B.R.N (i + 1))) (Fin (B.R.N (i + 1))) B.fields.E).map (TaylorLogMetric.tauEmb (I.rec7 l Z) (Pl.lam w) τ))
      (fun τ => ((((vlBdF B.fields.emb fun _ => Bm)⁻¹ τ : GL (Fin (B.R.N (i + 1))) B.LL) :
        Matrix (Fin (B.R.N (i + 1))) (Fin (B.R.N (i + 1))) B.LL)ᵀ).map (Pl.iL w))
      g (Bs u μ w (i + 1) c') y (fun τ => -((I.rec7 l Z).chTw u μ).sDiv i τ)
      (fun τ => (lamT (B.hcW u) (i + 1) τ).detShift) hM eds hg3

end GlobalTheory.Mem.LocDictT
