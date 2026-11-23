import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NOfibCut
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RealFramesCharacters
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.HermitianZZEqNeg
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RealHermitianForms
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.HermitianSumFrames

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Matrix

namespace Formalism.L2.SG.Pf.NcReal.JX.NOf

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.Pf.NcReal.JX Formalism.L2.SG.TermOp

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Pl

variable {D : D7} (X : HidaSetting D)

theorem umat_rv {x : X.B.I.GA} {n : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hRL : RatLink X x n) (v : InfinitePlace X.B.I.F)
    (y : (VS D).V) : uMat (x.1 v) *ᵥ rv X.B.I v (X.crd y) = rv X.B.I v (X.crd (n y)) := by
  obtain ⟨M, -, hv, -, hcrd⟩ := hRL
  rw [hv v, Formalism.L2.SG.Pf.rv_mulVec, ← hcrd]

theorem inv_map_emb {m : ℕ} {K L : Type*} [Field K] [Field L] (f : K →+* L) (A : Matrix (Fin m) (Fin m) K) :
    (A.map f)⁻¹ = A⁻¹.map f := by
  have h1 : (A.map f).det = f A.det := (f.map_det A).symm
  have h2 : (A.map f).adjugate = A.adjugate.map f := (f.map_adjugate A).symm
  rw [Matrix.inv_def, Matrix.inv_def, h1, h2, Ring.inverse_eq_inv', Ring.inverse_eq_inv', ← map_inv₀]
  ext i j
  simp [Matrix.smul_apply]

theorem hJ_span_ef (v : InfinitePlace X.B.I.F) (α β : Fin D.R.rS → D.host.E) (w : Fin X.B.I.n → ℂ)
    (he : ∀ c, hJ (X.B.I.ε v) (rv X.B.I v (X.crd (X.eX c))) w = 0)
    (hf : ∀ c, hJ (X.B.I.ε v) (rv X.B.I v (X.crd (X.fY c))) w = 0) :
    hJ (X.B.I.ε v) (rv X.B.I v (X.crd (∑ c, α c • X.eX c + ∑ c, β c • X.fY c))) w = 0 := by
  rw [Formalism.L2.SG.NormCut.crd_add', Formalism.L2.SG.NormCut.crd_sum', Formalism.L2.SG.NormCut.crd_sum']
  simp only [Formalism.L2.SG.NormCut.crd_smul']
  rw [← Formalism.L2.SG.Pf.Vanish2.rvHom_apply, map_add, Formalism.L2.SG.Pf.Vanish2.rvHom_apply,
    Formalism.L2.SG.Pf.Vanish2.rvHom_apply, Formalism.L2.SG.RealObj.RealFramesCharacters.rv_sum, Formalism.L2.SG.RealObj.RealFramesCharacters.rv_sum,
    Formalism.L2.SG.RealObj.InfCut.ProductExactness.hJ_add_l, Formalism.L2.SG.RealObj.HermitianSumRootCoordinateFrames.hJ_sum_left,
    Formalism.L2.SG.RealObj.HermitianSumRootCoordinateFrames.hJ_sum_left]
  simp only [he, hf, mul_zero, Finset.sum_const_zero, add_zero]

end Pl

section Main

theorem dictionary_place_holds : DictPlace := by
  intro D X u x n hRL hNF
  set ψ : InfinitePlace X.B.I.F → D.host.E →+* ℂ := fun v => embS D (X.pl v) with hψ
  have hxM : ∀ v, LsNc5.xMat X v x.1 = (Xq X n).map (ψ v) := fun v => by
    ext b a
    simp only [LsNc5.xMat, LsNc5.fV, LsNc5.eV, Matrix.map_apply]
    rw [show X.eR a = X.crd (X.eX a) from rfl, umat_rv X hRL v, show X.fR b = X.crd (X.fY b) from rfl,
      Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries.hJ_rvX]
    rfl
  have haM : ∀ v, LsNc5.aMat X v x.1 = (Aq X n).map (ψ v) := fun v => by
    ext b a
    simp only [LsNc5.aMat, LsNc5.fV, Matrix.map_apply]
    rw [show X.fR a = X.crd (X.fY a) from rfl, umat_rv X hRL v, show X.fR b = X.crd (X.fY b) from rfl,
      Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries.hJ_rvX]
    rfl
  have hmM : ∀ v, LsNc5.mMat X v x.1 = (Mq X n).map (ψ v) := fun v => by
    unfold LsNc5.mMat Mq
    rw [hxM, haM, inv_map_emb, Matrix.map_mul]

  have hrow : ∀ v b (w : Fin X.B.I.n → ℂ), (∀ c, hJ (X.B.I.ε v) (rv X.B.I v (X.crd (X.eX c))) w = 0) →
      (∀ c, hJ (X.B.I.ε v) (rv X.B.I v (X.crd (X.fY c))) w = 0) →
      hJ (X.B.I.ε v) (LsNc5.fV X v b) (uMat (x.1 v) *ᵥ w) = hJ (X.B.I.ε v) (rv X.B.I v (X.crd (xq X n b))) w := by
    intro v b w he hf
    have h1 := Formalism.L2.SG.RealObj.InfCut.RealHermitianForms.hJ_inv_r (X.B.I.ε v) (x.1 v)⁻¹ (LsNc5.fV X v b) w
    rw [inv_inv] at h1
    rw [h1]
    have h2 : uMat (x.1 v)⁻¹ *ᵥ LsNc5.fV X v b = rv X.B.I v (X.crd (n.symm (X.fY b))) :=
      umat_rv X (Formalism.L2.SG.TermOp.Vanish.ratLink_inv X hRL) v (X.fY b)
    rw [h2]
    have hy : n.symm (X.fY b) = xq X n b + (∑ c, (VS D).hT (X.fY c) (n.symm (X.fY b)) • X.eX c +
        ∑ c, (VS D).hT (X.eX c) (n.symm (X.fY b)) • X.fY c) := by
      simp only [xq, pW]; abel
    rw [hy, Formalism.L2.SG.NormCut.crd_add', ← Formalism.L2.SG.Pf.Vanish2.rvHom_apply, map_add,
      Formalism.L2.SG.Pf.Vanish2.rvHom_apply, Formalism.L2.SG.Pf.Vanish2.rvHom_apply, Formalism.L2.SG.RealObj.InfCut.ProductExactness.hJ_add_l,
      hJ_span_ef X v _ _ w he hf, add_zero]
  funext p
  rcases p with ((p | b) | (p | a))
  · funext v
    show LsNc5.xMat X v x.1 p.1.1 p.1.2 = embS D (X.pl v) (Xq X n p.1.1 p.1.2)
    rw [hxM]; rfl
  · funext v j
    show (if h : j.val < D.R.k then LsNc5.phiMat X u v x.1 b ⟨j.val, h⟩ else LsNc5.yVec X u v x.1 b) =
      rowV X u (xq X n b) v j
    unfold rowV
    split_ifs with h
    · exact hrow v b _ (fun c => ((X.wfr_perp u v ⟨j.val, h⟩).1 c).1) (fun c => ((X.wfr_perp u v ⟨j.val, h⟩).1 c).2)
    · refine hrow v b _ (fun c => ?_) (fun c => ?_)
      · show hJ (X.B.I.ε v) (rv X.B.I v (X.crd (X.eX c))) (rv X.B.I v (X.crd (X.zu u))) = 0
        rw [Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries.hJ_rvX, (X.zu_orth u c).1, map_zero]
      · show hJ (X.B.I.ε v) (rv X.B.I v (X.crd (X.fY c))) (rv X.B.I v (X.crd (X.zu u))) = 0
        rw [Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries.hJ_rvX, (X.zu_orth u c).2, map_zero]
  · funext v
    show (LsNc5.mMat X v x.1 p.1.1 p.1.2 - star (LsNc5.mMat X v x.1 p.1.2 p.1.1)) / 2 =
      (embS D (X.pl v) (Mq X n p.1.1 p.1.2) - star (embS D (X.pl v) (Mq X n p.1.2 p.1.1))) / 2
    rw [hmM]; rfl
  · funext v
    show (LsNc5.mMat X v x.1 a a).im = (embS D (X.pl v) (Mq X n a a)).im
    rw [hmM]; rfl

end Main

end Formalism.L2.SG.Pf.NcReal.JX.NOf
