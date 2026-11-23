import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAFFStableAdjIntCut
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAFFStableAdjCont
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BigCellInversePair
import Formalism.HermitianCurvature.HermitianCurvatureProofs.FiniteSumLocalExpansion
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentLevelZeroEqOne
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbitalIntegralAeConvergenceContinuity
import Formalism.FormalDegreeBessel.FormalDegreeRatio.BesselUnitaryEquivHolds

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt MeasureTheory

namespace Formalism.FourierDecayAlt.P.CutMP.JA.FFS.AC

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

theorem sgs_of_invP (p : B.SS k r) (hp1 : IsUnit (Matrix.of p.1.1 : B.Mat k r).det)
    (hp2 : IsUnit (Matrix.of p.1.2 : B.Mat k r).det) (hp3 : IsUnit (Matrix.of p.2.1 : B.Mat k r).det)
    (hp4 : IsUnit (Matrix.of p.2.2 : B.Mat k r).det) (x : B.Mat k r) :
    B.sgs p (B.sgs (Formalism.FourierDecayAlt.P.BigCellInversePair.invP p) x) = x := by
  set h : B.Mat k r := Matrix.of p.1.1
  set n : B.Mat k r := Matrix.of p.1.2
  set h' : B.Mat k r := Matrix.of p.2.1
  set n' : B.Mat k r := Matrix.of p.2.2
  have e1 : (Matrix.of (Formalism.FourierDecayAlt.P.BigCellInversePair.invP p).1.1 : B.Mat k r) = h⁻¹ := rfl
  have e2 : (Matrix.of (Formalism.FourierDecayAlt.P.BigCellInversePair.invP p).1.2 : B.Mat k r) = h⁻¹ * n⁻¹ * h := rfl
  have e3 : (Matrix.of (Formalism.FourierDecayAlt.P.BigCellInversePair.invP p).2.1 : B.Mat k r) = h'⁻¹ := rfl
  have e4 : (Matrix.of (Formalism.FourierDecayAlt.P.BigCellInversePair.invP p).2.2 : B.Mat k r) = h'⁻¹ * n'⁻¹ * h' := rfl
  unfold B.sgs
  rw [e1, e2, e3, e4]
  show h⁻¹ * n⁻¹ * (h⁻¹⁻¹ * (h⁻¹ * n⁻¹ * h)⁻¹ * x * (h'⁻¹ * n'⁻¹ * h') * h'⁻¹) * n' * h' = x
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hp1,
    Matrix.nonsing_inv_nonsing_inv _ hp2]
  simp only [Matrix.mul_assoc]
  simp only [Matrix.mul_nonsing_inv_cancel_left _ _ hp1, Matrix.nonsing_inv_mul_cancel_left _ _ hp1,
    Matrix.nonsing_inv_mul_cancel_left _ _ hp2, Matrix.mul_nonsing_inv_cancel_left _ _ hp3,
    Matrix.nonsing_inv_mul_cancel_left _ _ hp4, Matrix.nonsing_inv_mul _ hp3, Matrix.mul_one]

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem hs_uni (D : B.RealPlaceData k r Wp Wq) {h h' : B.Mat k r} (hh : h ∈ UWset k r D.z) (hh' : h' ∈ UWset k r D.z')
    (A C : Wq →L[ℂ] Wp) :
    B.hsInner ((D.π h).comp (A.comp (D.π' h'⁻¹))) C =
      B.hsInner A ((D.π h⁻¹).comp (C.comp (D.π' h'⁻¹⁻¹))) := by
  have hi := Formalism.FourierDecayAlt.P.BigCellInversePair.uw_inv hh
  have hi' := Formalism.FourierDecayAlt.P.BigCellInversePair.uw_inv hh'
  have hii' := Formalism.FourierDecayAlt.P.BigCellInversePair.uw_inv hi'
  have e1 : (D.π h).comp (D.π h⁻¹) = 1 := by
    rw [← D.π_rep.2 h hh h⁻¹ hi, (Formalism.FourierDecayAlt.P.FiniteSumLocalExpansion.gv_inv hh.1).1, D.π_rep.1]
  have e2 : (D.π' h'⁻¹⁻¹).comp (D.π' h'⁻¹) = 1 := by
    rw [← D.π'_rep.2 _ hii' _ hi', (Formalism.FourierDecayAlt.P.FiniteSumLocalExpansion.gv_inv hi'.1).2, D.π'_rep.1]
  have e1v : ∀ w, D.π h (D.π h⁻¹ w) = w := fun w => by
    have := congrArg (fun T : Wp →L[ℂ] Wp => T w) e1
    simpa using this
  have e2v : ∀ w, D.π' h'⁻¹⁻¹ (D.π' h'⁻¹ w) = w := fun w => by
    have := congrArg (fun T : Wq →L[ℂ] Wq => T w) e2
    simpa using this
  set Z : Wq →L[ℂ] Wp := (D.π h⁻¹).comp (C.comp (D.π' h'⁻¹⁻¹))
  have hC : C = (D.π h).comp (Z.comp (D.π' h'⁻¹)) := by
    ext v
    simp only [Z, ContinuousLinearMap.comp_apply, e2v, e1v]
  calc B.hsInner ((D.π h).comp (A.comp (D.π' h'⁻¹))) C
      = B.hsInner ((D.π h).comp (A.comp (D.π' h'⁻¹))) ((D.π h).comp (Z.comp (D.π' h'⁻¹))) := by rw [← hC]
    _ = B.hsInner (A.comp (D.π' h'⁻¹)) (Z.comp (D.π' h'⁻¹)) :=
        Formalism.FourierDecayAlt.P.PBI.hsInner_comp_left _ (D.π_unitary h hh) _ _
    _ = B.hsInner A Z := Formalism.FourierDecayAlt.P.PBI.hsInner_comp_right _ (D.π'_unitary _ hi') _ _

omit [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] in
theorem sgsM_eq_comp (q : B.SS k r) : Formalism.FourierDecayAlt.P.B7.sgsM q =
    lmulM (k := k) (r := r) (Matrix.of q.1.2 * Matrix.of q.1.1 : B.Mat k r)⁻¹ ∘
      B.rmulF (Matrix.of q.2.2 * Matrix.of q.2.1 : B.Mat k r) := by
  funext x
  have e : B.sgs q (Matrix.of x) = (Matrix.of q.1.2 * Matrix.of q.1.1 : B.Mat k r)⁻¹ *
      (Matrix.of x * (Matrix.of q.2.2 * Matrix.of q.2.1 : B.Mat k r)) := by
    rw [Formalism.FourierDecayAlt.P.B5.sgs_eq, Matrix.mul_assoc]
  exact e

omit [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] in
theorem measurable_rmulF (C : B.Mat k r) : Measurable (B.rmulF C) := by
  have : Continuous (B.rmulF C) := (continuous_id.matrix_mul continuous_const : Continuous fun x : B.Mat k r => x * C)
  exact this.measurable

omit [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] in
theorem measurable_section_inverse (q : B.SS k r) : Measurable (Formalism.FourierDecayAlt.P.B7.sgsM q) := by
  rw [sgsM_eq_comp]
  exact (Formalism.QuantumDeterminants.BesselUnitaryEquiv.continuous_lmulM _).measurable.comp (measurable_rmulF _)

theorem map_sgs (D : B.RealPlaceData k r Wp Wq) {q : B.SS k r} (hq : D.inSS q) :
    D.μG.map (Formalism.FourierDecayAlt.P.B7.sgsM q) = D.μG := by
  have hA := Formalism.FourierDecayAlt.P.NFRadRedLocSec.uh_inv_mem (Formalism.FourierDecayAlt.P.B5.inSS_left D hq)
  have hC := Formalism.FourierDecayAlt.P.B5.inSS_right D hq
  have hmr := measurable_rmulF (k := k) (r := r) (Matrix.of q.2.2 * Matrix.of q.2.1 : B.Mat k r)
  rw [sgsM_eq_comp, ← Measure.map_map (Formalism.QuantumDeterminants.BesselUnitaryEquiv.continuous_lmulM _).measurable hmr, D.haarG.right _ hC,
    D.haarG.left _ hA]

end Formalism.FourierDecayAlt.P.CutMP.JA.FFS.AC

namespace Formalism.FourierDecayAlt.P.CutMP.JA.FFS.AC

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

theorem sgsM_left (p : B.SS k r) (hp1 : IsUnit (Matrix.of p.1.1 : B.Mat k r).det)
    (hp2 : IsUnit (Matrix.of p.1.2 : B.Mat k r).det) (hp3 : IsUnit (Matrix.of p.2.1 : B.Mat k r).det)
    (hp4 : IsUnit (Matrix.of p.2.2 : B.Mat k r).det) (x : Mt k r) :
    Formalism.FourierDecayAlt.P.B7.sgsM p (Formalism.FourierDecayAlt.P.B7.sgsM (Formalism.FourierDecayAlt.P.BigCellInversePair.invP p) x) = x := by
  have := sgs_of_invP p hp1 hp2 hp3 hp4 (Matrix.of x)
  exact this

theorem sgsM_right (p : B.SS k r) (hp1 : IsUnit (Matrix.of p.1.1 : B.Mat k r).det)
    (hp2 : IsUnit (Matrix.of p.1.2 : B.Mat k r).det) (hp3 : IsUnit (Matrix.of p.2.1 : B.Mat k r).det)
    (hp4 : IsUnit (Matrix.of p.2.2 : B.Mat k r).det) (x : Mt k r) :
    Formalism.FourierDecayAlt.P.B7.sgsM (Formalism.FourierDecayAlt.P.BigCellInversePair.invP p) (Formalism.FourierDecayAlt.P.B7.sgsM p x) = x := by
  have := Formalism.FourierDecayAlt.P.BigCellInversePair.sgs_invP p hp1 hp2 hp3 hp4 (Matrix.of x)
  exact this

noncomputable def sgsE (p : B.SS k r) (hp1 : IsUnit (Matrix.of p.1.1 : B.Mat k r).det)
    (hp2 : IsUnit (Matrix.of p.1.2 : B.Mat k r).det) (hp3 : IsUnit (Matrix.of p.2.1 : B.Mat k r).det)
    (hp4 : IsUnit (Matrix.of p.2.2 : B.Mat k r).det) : Mt k r ≃ᵐ Mt k r where
  toFun := Formalism.FourierDecayAlt.P.B7.sgsM (Formalism.FourierDecayAlt.P.BigCellInversePair.invP p)
  invFun := Formalism.FourierDecayAlt.P.B7.sgsM p
  left_inv := sgsM_left p hp1 hp2 hp3 hp4
  right_inv := sgsM_right p hp1 hp2 hp3 hp4
  measurable_toFun := measurable_section_inverse _
  measurable_invFun := measurable_section_inverse _

theorem sgsE_coe (p : B.SS k r) (hp1 hp2 hp3 hp4) :
    ⇑(sgsE (k := k) (r := r) p hp1 hp2 hp3 hp4) = Formalism.FourierDecayAlt.P.B7.sgsM (Formalism.FourierDecayAlt.P.BigCellInversePair.invP p) := rfl

end Formalism.FourierDecayAlt.P.CutMP.JA.FFS.AC

namespace Formalism.FourierDecayAlt.P.CutMP.JA.FFS

open Formalism.FourierDecayAlt.P.CutMP.JA.FFS.AC

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem unitary_rho_holds : RhoUni := by
  intro k r Wp Wq _ _ _ _ _ _ D p hp
  refine ⟨Formalism.FourierDecayAlt.P.BigCellInversePair.invP p, Formalism.FourierDecayAlt.P.BigCellInversePair.invP_inSS D hp, fun X Y => ?_⟩
  have hq := Formalism.FourierDecayAlt.P.BigCellInversePair.invP_inSS D hp
  have u1 := WeylGroupFacts.isUnit_of_uh hp.1.1
  have u2 := WeylGroupFacts.isUnit_of_uh hp.2.1.1
  have u3 := WeylGroupFacts.isUnit_of_uh hp.2.2.1.1
  have u4 := WeylGroupFacts.isUnit_of_uh hp.2.2.2.1
  have hmp : MeasurePreserving (sgsE p u1 u2 u3 u4) D.μG D.μG :=
    ⟨(sgsE p u1 u2 u3 u4).measurable, by rw [sgsE_coe]; exact map_sgs D hq⟩
  rw [← hmp.integral_comp' (fun y : Mt k r => B.hsInner (B.rho D p X (Matrix.of y)) (Y (Matrix.of y)))]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  show B.hsInner (B.rho D p X (B.sgs (Formalism.FourierDecayAlt.P.BigCellInversePair.invP p) (Matrix.of x)))
      (Y (B.sgs (Formalism.FourierDecayAlt.P.BigCellInversePair.invP p) (Matrix.of x))) =
    B.hsInner (X (Matrix.of x)) (B.rho D (Formalism.FourierDecayAlt.P.BigCellInversePair.invP p) Y (Matrix.of x))
  unfold B.rho
  rw [sgs_of_invP p u1 u2 u3 u4]
  exact hs_uni D hp.1 hp.2.2.1 _ _

end Formalism.FourierDecayAlt.P.CutMP.JA.FFS
