import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SchurOrthogonalityDimPairingEqInnerStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowLevelFormsSpanDefiniteMultiplicitySpaceStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HilbertInnerRowFormsEqLevelClassSumStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HilbertInnerLiftFormsEqBaseLevelHermitianStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpanLiftFormsBaseLevelEqHilbertImageStatement

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section

namespace GlobalTheory.TopNorm

theorem ipVia_self {H N : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [AddCommGroup N] [Module ℂ N]
    (e : H →ₗ[ℂ] N) (he : Function.Injective e) (u v : H) : ipVia e (e u) (e v) = ⟪u, v⟫_ℂ := by
  unfold ipVia
  split_ifs with h
  · have h1 : h.1.choose = u := he h.1.choose_spec
    have h2 : h.2.choose = v := he h.2.choose_spec
    rw [h1, h2]
  · exact absurd ⟨⟨u, rfl⟩, ⟨v, rfl⟩⟩ h

set_option maxHeartbeats 2000000 in

theorem classSums_topNorm : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (tupT : D.what₂.Tup → T) (hm : 0 < D.R.m) (hTop : TopMultH R) (hinj : ∀ i t, Function.Injective (R.extV i t)), R.BaseW F → Seed.PrIso R.MX R.cX R.prX → A.fam.Ok 1 → let C := toChainReal R F tupT hm hTop; let L := toLiftReal R F tupT hm hTop hinj; ∀ μ : D.what₂.Tup, (let a := fun x => R.cX.toMap R.prX ((R.HX (tupT μ)).e (R.jX (tupT μ) (rowForm A F.P1 F.ψ1 (tupT μ) x))); Submodule.span ℂ (Set.range a) = C.CCXP true μ ∧ ∀ x y, C.ipXP true μ (a x) (a y) = D.what₂.embLL (Formalism.DivisionValues.hform (rH D A F.P1 F.ψ1 (tupT μ)) x y)) ∧ (let a := fun x => R.cX.toMap R.prX ((R.HX (tupT μ)).e (R.jX (tupT μ) (rowForm A F.P0 F.ψ0 (tupT μ) x))); Submodule.span ℂ (Set.range a) = C.CCXP false μ ∧ ∀ x y, C.ipXP false μ (a x) (a y) = D.what₂.embLL (Formalism.DivisionValues.hform (rH D A F.P0 F.ψ0 (tupT μ)) x y)) ∧ ∀ i : Fin D.R.m, (let a := fun x => R.extV i (tupT μ) (R.jV i (tupT μ) (liftForm A F.P0 F.ψ0 i (tupT μ) x)); Submodule.span ℂ (Set.range a) = L.Amt μ i ∧ ∀ x y, L.ipA μ i (a x) (a y) = D.what₂.embLL (Formalism.DivisionValues.hform (lH D A F.P0 F.ψ0 i (tupT μ)) x y)) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F tupT hm hTop hinj hB hPr hOk C L μ
  refine ⟨⟨GlobalTheory.T.rowLevelForms_span_definiteMultiplicitySpace D G Pl0 T A Ks R F hB hPr hOk hTop true (tupT μ), fun x y => ?_⟩,
    ⟨GlobalTheory.T.rowLevelForms_span_definiteMultiplicitySpace D G Pl0 T A Ks R F hB hPr hOk hTop false (tupT μ), fun x y => ?_⟩,
    fun i => ⟨GlobalTheory.T.span_liftForms_baseLevel_eq_hilbertImage D G Pl0 T A Ks R F hB hOk hinj i (tupT μ), fun x y => ?_⟩⟩
  · have h1 := GlobalTheory.T.schur_orthogonality_dim_pairing_eq_inner D G Pl0 T A Ks R F hB hPr (tupT μ) (R.jX (tupT μ) (rowForm A F.P1 F.ψ1 (tupT μ) x))
      (R.jX (tupT μ) (rowForm A F.P1 F.ψ1 (tupT μ) y))
    have h3 := GlobalTheory.T.hilbert_inner_rowForms_eq_level_class_sum D G Pl0 T A Ks R F hB true (tupT μ) x y
    have e1 : ((((∏ τ, (Module.finrank ℂ (R.MX.H τ) : ℝ)) / (1 : ℝ) : ℝ) : ℂ)) =
        (((∏ τ, (Module.finrank ℂ (R.MX.H τ) : ℝ)) : ℝ) : ℂ) :=
      congrArg (fun r : ℝ => (r : ℂ)) (div_one (∏ τ, (Module.finrank ℂ (R.MX.H τ) : ℝ)))
    refine Eq.trans ?_ h3
    show (((RealDat.nP F true)⁻¹ : ℝ) : ℂ) * ((((∏ τ, (Module.finrank ℂ (R.MX.H τ) : ℝ)) / (1 : ℝ) : ℝ) : ℂ) *
        ipMT R.MX (R.νX (tupT μ)) (R.fdX (tupT μ))
          (R.cX.toMap R.prX ((R.HX (tupT μ)).e (R.jX (tupT μ) (rowForm A F.P1 F.ψ1 (tupT μ) x))))
          (R.cX.toMap R.prX ((R.HX (tupT μ)).e (R.jX (tupT μ) (rowForm A F.P1 F.ψ1 (tupT μ) y))))) = _
    exact congrArg (fun z : ℂ => (((RealDat.nP F true)⁻¹ : ℝ) : ℂ) * z) ((congrArg (· * _) e1).trans h1)
  · have h1 := GlobalTheory.T.schur_orthogonality_dim_pairing_eq_inner D G Pl0 T A Ks R F hB hPr (tupT μ) (R.jX (tupT μ) (rowForm A F.P0 F.ψ0 (tupT μ) x))
      (R.jX (tupT μ) (rowForm A F.P0 F.ψ0 (tupT μ) y))
    have h3 := GlobalTheory.T.hilbert_inner_rowForms_eq_level_class_sum D G Pl0 T A Ks R F hB false (tupT μ) x y
    have e1 : ((((∏ τ, (Module.finrank ℂ (R.MX.H τ) : ℝ)) / (1 : ℝ) : ℝ) : ℂ)) =
        (((∏ τ, (Module.finrank ℂ (R.MX.H τ) : ℝ)) : ℝ) : ℂ) :=
      congrArg (fun r : ℝ => (r : ℂ)) (div_one (∏ τ, (Module.finrank ℂ (R.MX.H τ) : ℝ)))
    refine Eq.trans ?_ h3
    show (((RealDat.nP F false)⁻¹ : ℝ) : ℂ) * ((((∏ τ, (Module.finrank ℂ (R.MX.H τ) : ℝ)) / (1 : ℝ) : ℝ) : ℂ) *
        ipMT R.MX (R.νX (tupT μ)) (R.fdX (tupT μ))
          (R.cX.toMap R.prX ((R.HX (tupT μ)).e (R.jX (tupT μ) (rowForm A F.P0 F.ψ0 (tupT μ) x))))
          (R.cX.toMap R.prX ((R.HX (tupT μ)).e (R.jX (tupT μ) (rowForm A F.P0 F.ψ0 (tupT μ) y))))) = _
    exact congrArg (fun z : ℂ => (((RealDat.nP F false)⁻¹ : ℝ) : ℂ) * z) ((congrArg (· * _) e1).trans h1)
  · have h5 := GlobalTheory.T.hilbert_inner_liftForms_eq_base_level_hermitian D G Pl0 T A Ks R F hB i (tupT μ) x y
    refine Eq.trans ?_ h5
    show (((RealDat.nP F false)⁻¹ : ℝ) : ℂ) * ipVia (R.extV i (tupT μ))
      (R.extV i (tupT μ) (R.jV i (tupT μ) (liftForm A F.P0 F.ψ0 i (tupT μ) x)))
      (R.extV i (tupT μ) (R.jV i (tupT μ) (liftForm A F.P0 F.ψ0 i (tupT μ) y))) = _
    exact congrArg (fun z : ℂ => (((RealDat.nP F false)⁻¹ : ℝ) : ℂ) * z) (ipVia_self _ (hinj i (tupT μ)) _ _)

end GlobalTheory.TopNorm

end
