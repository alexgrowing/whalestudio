import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedVectorEqOfStandardData
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsTwIffCanonEq
import Formalism.LocalToGlobal.KernelLattices.TopPin
import Formalism.LocalToGlobal.KernelLattices.InterlaceAll
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JetsInIffStepField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianChartComplexRationalIntegralFormsStatement
import Formalism.LocalToGlobal.KernelLattices.ColumnData.DiagramFitsSourceRank
import Formalism.UnipotentAdelicQuotients.WeylLatDual
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolFunApply
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EvalTwSubK
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.TiedRec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AutomorphicFormFnInvIffTwistedSubstitutionMemStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeylLatticeDualInvariantUnitStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DetPowerProductMulMemDelWShiftIffStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntegralSpanIffPadicWeylDualLatticeStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistedEmbeddingMatrixSubstitutionMemRatSpanStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalBasisChangeIntegralUnitDetStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChainStepWeightArithmeticStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistedSourceValueReadInChangedBasesStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IntegralityCompare

noncomputable section

namespace GlobalTheory.IntegralityCompare

theorem lift_ratSpan (D : D7) {n : ℕ} (lam : D.what₂.Tau → DomWeight n) (P0 : MvPolynomial (D.what₂.Tau × Fin n × Fin n) ℂ) :
    P0 ∈ Formalism.L2.Forms.RatSpan D lam → ∃ R0 : MvPolynomial (D.what₂.Tau × Fin n × Fin n) D.what₂.LL,
      MvPolynomial.map D.what₂.embLL R0 = P0 := by
  intro h
  have hle : Formalism.L2.Forms.RatSpan D lam ≤ (MvPolynomial.map D.what₂.embLL).toAddMonoidHom.range := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro p ⟨r, f, -, rfl⟩
    refine ⟨MvPolynomial.C r * Formalism.L2.Forms.ten (fun τ => MvPolynomial.map (Int.castRingHom D.what₂.LL) (f τ)), ?_⟩
    have hc : (D.what₂.embLL).comp (Int.castRingHom D.what₂.LL) = Int.castRingHom ℂ := RingHom.ext_int _ _
    simp [Formalism.L2.Forms.ten, map_prod, MvPolynomial.map_map, MvPolynomial.smul_eq_C_mul, MvPolynomial.map_rename, hc]
  obtain ⟨R0, hR0⟩ := hle h
  exact ⟨R0, hR0⟩

theorem lattice_iff_weyl : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (Y : DivX (I.rec7 l Z)) (O : ∀ u a, GL3Theta.LiftObj (I.rec7 l Z) ((I.rec7 l Z).chTw u a)) (Pl : Examples₂.EntPl (I.rec7 l Z)) (Bs : PlaceMatrixFamily (I.rec7 l Z)), I.QpIs Y.Qp → I.StdO l Z Y.Qp O → BasOk Pl O Bs → (∀ u a w, LevFree Y u a w → ∀ i, i ≤ B.R.m → ∀ c τ j k, ∃ x : (I.rec7 l Z).what₂.LL, Bs u a w i c τ j k = Pl.iL w x) → ∀ (u : B.Word) (μ : I.ι) (w : (I.rec7 l Z).what₂.places.Pl), LevFree Y u μ w → ∀ (i : ℕ) (hi : i < B.R.m) (eY : (I.chain l u μ).Y i ≃ Formalism.L2.Forms.Fr (I.rec7 l Z) i hi.le), I.IdY l Z u μ i hi.le eY → ∀ (c : (I.stp u μ i).Cl) (f : (I.chain l u μ).Y i → ℂ), (∃ P ∈ Formalism.L2.Forms.RatSpan (I.rec7 l Z) ((I.fm l u μ).lam i), ∀ z, f z = fnOf (gramC (gramN (I.rec7 l Z) i hi.le) (embT (I.rec7 l Z))) (shiftOf (lamTG (I.fm l u μ) i)) 1 P (eY z)) → ∀ Bm : GL (Fin ((I.rec7 l Z).R.N i)) (I.rec7 l Z).host.E, Formalism.L2.Forms.IsLocBasis ((I.rec7 l Z).what₂.places.resChar w) (((I.stp u μ i).rep c).1.1.deco.1.N : Set (Sp B.fields.E (B.R.N i))) Bm →  ∀ v : ValQ O u μ i, evC O u μ i v = f → ((∃ P ∈ Formalism.L2.Forms.IntSpan (I.rec7 l Z) w ((I.fm l u μ).lam i), ∀ z, f z = fnOf (gramC (gramN (I.rec7 l Z) i hi.le) (embT (I.rec7 l Z))) (shiftOf (lamTG (I.fm l u μ) i)) (atInf (embT (I.rec7 l Z)) ((Bm⁻¹ : GL (Fin ((I.rec7 l Z).R.N i)) (I.rec7 l Z).host.E) : Matrix (Fin ((I.rec7 l Z).R.N i)) (Fin ((I.rec7 l Z).R.N i)) (I.rec7 l Z).host.E)) P (eY z)) ↔ srcFun Pl Bs u μ w i c (secC O u μ i v) ∈ WeylLatticeDuality.DelW ((I.rec7 l Z).what₂.places.resChar w) (I.rec7 l Z).what₂.Tau ((I.rec7 l Z).R.N i) (nuT (I.rec7 l Z) u i)) := by
  intro B X I hOk hPins l Z Y O Pl Bs hQp hStd hBas hEnt u μ w hLev i hi eY hIdY c f hRat Bm hBm v hv
  obtain ⟨P0, hP0, hf⟩ := hRat
  have hL : ∀ τ, GL3Columns.BasR (I.rec7 l Z) (Pl.lam w) τ (((I.stp u μ i).rep c).1.1.deco.1.N) (Bs u μ w i c τ) := by
    intro τ
    have h := hBas u μ w i hi.le c τ
    have e := hStd.lat u μ i c
    exact (congrArg (fun L => GL3Columns.BasR (I.rec7 l Z) (Pl.lam w) τ L (Bs u μ w i c τ)) e).mp h
  choose g hg1 hg2 hg3 using fun τ => GlobalTheory.T.localBasis_change_integral_unit_det _ (Pl.lam w) τ _ Bm _ (hL τ) hBm
  obtain ⟨k, hk1, hk⟩ := GlobalTheory.T.chainStep_weight_arithmetic I hOk hPins l Z u μ i hi
  obtain ⟨R0, hR0⟩ := lift_ratSpan _ _ P0 hP0
  have hsrc := GlobalTheory.T.twistedSourceValue_read_in_changed_bases I hOk hPins l Z Y O Pl Bs hQp hStd hBas hEnt u μ w hLev i hi eY hIdY c f P0 hf R0 hR0 k hk1 Bm g hg3 v hv
  set R := twSubK (Formalism.L2.G.Cmp.tEL (I.rec7 l Z)) Bm (shiftOf (lamTG (I.fm l u μ) i)) R0 with hRdef
  have hR : MvPolynomial.map (I.rec7 l Z).what₂.embLL R = twSub (embT (I.rec7 l Z)) Bm (shiftOf (lamTG (I.fm l u μ) i)) P0 := by
    have h := map_twSubK (Formalism.L2.G.Cmp.tEL (I.rec7 l Z)) Bm (shiftOf (lamTG (I.fm l u μ) i)) R0 (I.rec7 l Z).what₂.embLL
    have h' : MvPolynomial.map (I.rec7 l Z).what₂.embLL R = twSub (fun τ => ((I.rec7 l Z).what₂.embLL).comp (Formalism.L2.G.Cmp.tEL (I.rec7 l Z) τ)) Bm (shiftOf (lamTG (I.fm l u μ) i)) P0 :=
      h.trans (congrArg (twSub _ Bm _) hR0)
    have he : (fun τ => ((I.rec7 l Z).what₂.embLL).comp (Formalism.L2.G.Cmp.tEL (I.rec7 l Z) τ)) = embT (I.rec7 l Z) :=
      funext fun τ => RingHom.ext fun x => Formalism.L2.G.Cmp.tEL_emb _ τ x
    rw [he] at h'
    exact h'
  set c0 := ∏ τ, (g τ).det ^ (-((I.rec7 l Z).chTw u μ).sSharp i τ) with hc0def
  have hc0 : ‖c0‖ = 1 := by
    rw [hc0def, norm_prod]
    exact Finset.prod_eq_one fun τ _ => by rw [norm_zpow, hg2 τ, _root_.one_zpow]
  have hRat' : MvPolynomial.map (I.rec7 l Z).what₂.embLL R ∈ Formalism.L2.Forms.RatSpan (I.rec7 l Z) ((I.fm l u μ).lam i) := by
    rw [hR]; exact GlobalTheory.T.twistedEmbeddingMatrixSubstitution_mem_ratSpan _ _ Bm _ P0 hP0
  have hν : nuT (I.rec7 l Z) u i = fun τ r => (((I.fm l u μ).lam i τ).natW r) + k τ :=
    funext fun τ => funext fun r => hk τ r
  refine (GlobalTheory.T.automorphicFormFn_inv_iff_twistedSubstitution_mem (embT (I.rec7 l Z)) Bm _ _ P0 _ eY f hf).trans ?_
  rw [← hR]
  refine (GlobalTheory.T.integralSpan_iff_padic_weylDualLattice _ Pl w _ R hRat').trans ?_
  rw [hsrc, hν]
  refine Iff.trans ?_ (GlobalTheory.T.weyl_lattice_dual_invariant_unit _ _ _ _ g c0 (fun y => (∏ τ, (y τ).det ^ k τ) * polFun (MvPolynomial.map (Pl.iL w) R) y) hc0 hg1 hg2).symm
  exact (GlobalTheory.T.detPowerProduct_mul_mem_delW_shift_iff _ _ _ _ k _).symm

end GlobalTheory.IntegralityCompare

end
