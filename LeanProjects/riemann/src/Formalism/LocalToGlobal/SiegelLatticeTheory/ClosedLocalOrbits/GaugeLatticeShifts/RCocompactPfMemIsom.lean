import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RCocompactPfMemSteps
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NilradicalLatticeZMemSpan

noncomputable section

open scoped Classical
open Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp
open Formalism.L2.SG.Pf.UnipB Formalism.L2.SG.Pf.Unip

namespace Formalism.L2.SG.TermOp.Vanish

private theorem crd_toLin_map_eq_mulVec_crd {D : D7} (X : HidaSetting D) (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E)
    (y : (VS D).V) : X.crd (Matrix.toLin X.bas X.bas (M.map X.ιE) y) = M *ᵥ X.crd y := by
  have h := LinearMap.toMatrix_mulVec_repr X.bas X.bas (Matrix.toLin X.bas X.bas (M.map X.ιE)) y
  rw [LinearMap.toMatrix_toLin] at h
  funext i
  simp only [Formalism.L2.SG.HidaSetting.HidaSetting.crd, Formalism.L2.SG.HidaSetting.crdOf, ← h, Matrix.mulVec, dotProduct,
    Matrix.map_apply, map_sum, map_mul, RingEquiv.symm_apply_apply]

theorem memIsomOf_holds : MemIsomOf := by
  intro D X g hg
  let A : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E := (g : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E)
  let B : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E :=
    ((g⁻¹ : GL (Fin X.B.I.n) X.B.I.E) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E)
  have hinj : ∀ y y' : (VS D).V, X.crd y = X.crd y' → y = y' := by
    intro y y' h
    apply X.bas.repr.injective
    ext i
    have := congrFun h i
    simpa [Formalism.L2.SG.HidaSetting.HidaSetting.crd, Formalism.L2.SG.HidaSetting.crdOf] using this
  let n : (VS D).V ≃ₗ[D.host.E] (VS D).V :=
    LinearEquiv.ofLinear (Matrix.toLin X.bas X.bas (A.map X.ιE)) (Matrix.toLin X.bas X.bas (B.map X.ιE))
      (LinearMap.ext fun y => hinj _ _ (by
        rw [LinearMap.comp_apply, crd_toLin_map_eq_mulVec_crd, crd_toLin_map_eq_mulVec_crd, Matrix.mulVec_mulVec]
        simp [A, B]))
      (LinearMap.ext fun y => hinj _ _ (by
        rw [LinearMap.comp_apply, crd_toLin_map_eq_mulVec_crd, crd_toLin_map_eq_mulVec_crd, Matrix.mulVec_mulVec]
        simp [A, B]))
  have hn : ∀ y, X.crd (n y) = A *ᵥ X.crd y := fun y => crd_toLin_map_eq_mulVec_crd X A y
  refine ⟨n, ?_, hn⟩
  intro x y
  rw [← Formalism.L2.SG.PoincareInHH.Cut.hform_crd X (n x) (n y), ← Formalism.L2.SG.PoincareInHH.Cut.hform_crd X x y,
    hn, hn, Formalism.L2.SG.PoincareInHH.Cut.hform_mulVec _ _ _ hg]

end Formalism.L2.SG.TermOp.Vanish
