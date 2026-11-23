import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.FormPairAlgebra.PairGSteps
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.FormPairAlgebra.GsLinSpec
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.FormPairAlgebra.MulVecSingleApply
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.FormPairAlgebra.ProjPSurjective
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitaryThetaVanishing.StepsL
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.FormInverseCounting.LiftRepMem

noncomputable section

open Formalism.L2.SG.LocalCountModules.LocCntCommon Formalism.L2.SG.LocalCountModules.LocCnt0LAlg Formalism.L2.SG.LocalCountModules.UnramifiedPairingLinear

namespace Formalism.L2.SG.LocalCountModules.UnramifiedPairingAlgebraic

variable {E : Type} [CommRing E] (O : Subring E) {r : ℕ}

theorem kap_mul_det (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) O) (hu : IsUnit (Z.map O.subtype).det) :
    kap O Z * (Z.map O.subtype).det = ((Z.map O.subtype).submatrix Fin.castSucc Fin.castSucc).det := by
  unfold kap
  rw [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, mul_comm (Ring.inverse _), mul_assoc,
    Ring.inverse_mul_cancel _ hu, mul_one, Matrix.adjugate_fin_succ_eq_det_submatrix]
  simp [Fin.succAbove_last, ← two_mul, pow_mul]

theorem kap_eq (Z₁ Z₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) O) (hu₁ : IsUnit (Z₁.map O.subtype).det)
    (hu₂ : IsUnit (Z₂.map O.subtype).det)
    (hrel : ((Z₁.map O.subtype).submatrix Fin.castSucc Fin.castSucc).det * (Z₂.map O.subtype).det =
      ((Z₂.map O.subtype).submatrix Fin.castSucc Fin.castSucc).det * (Z₁.map O.subtype).det) :
    kap O Z₂ = kap O Z₁ := by
  have h1 := kap_mul_det O Z₁ hu₁
  have h2 := kap_mul_det O Z₂ hu₂
  rw [← h1, ← h2] at hrel
  apply (hu₁.mul hu₂).mul_right_cancel
  linear_combination -hrel

theorem stepPairG_of_fwd_bwd (hf : FwdEx) (hb : BwdEx) : StepPairG := by
  intro E _ O cj hcj hO r T T' hT hT' hcT hcT' Z₁ Z₂ hu₁ hu₂ hrel hG₁ hG₂
  let t : O := ⟨T, hT⟩
  let t' : O := ⟨T', hT'⟩
  have hk : kap O Z₂ = kap O Z₁ := kap_eq O Z₁ Z₂ hu₁ hu₂ hrel
  have hη₂ : EtaNZD O cj Z₂ (t : E) (t' : E) := fun u h => eta_nzd O cj hcj Z₂ hu₂ T T' hG₂ u h
  have hf' := hf E O cj hcj hO r t t' hcT hcT' Z₁ Z₂ hu₁ hu₂ hk hG₁ hG₂
  have hb' := hb E O cj hcj hO r t t' hcT hcT' Z₁ Z₂ hu₁ hu₂ hk hG₁ hG₂
  choose F hF using hf'
  choose B hBmem hB using hb'
  have lamP : ∀ (p : PairSet O cj hO Z₁ Z₂) (m : MbMod Z₁),
      lamLQ O Z₂ hu₂ (p.1.1 m) = lamLQ O Z₁ hu₁ m := by
    intro p m
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ m
    obtain ⟨y₂, hy₂⟩ := Submodule.Quotient.mk_surjective _ (p.1.1 (Submodule.Quotient.mk y))
    rw [← hy₂]
    exact lam_keep O hu₁ hu₂ p.1.1.toLinearMap p.2.1.1 y y₂ hy₂.symm
  have lamSP : ∀ (p : PairSet O cj hO Z₁ Z₂) (m : MbMod (cjT O cj hO Z₁)),
      lamSQ O cj hO Z₂ hu₂ (p.1.2 m) = lamSQ O cj hO Z₁ hu₁ m := by
    intro p m
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ m
    obtain ⟨y₂, hy₂⟩ := Submodule.Quotient.mk_surjective _ (p.1.2 (Submodule.Quotient.mk y))
    rw [← hy₂]
    exact p.2.2.1 y y₂ hy₂.symm
  refine Nat.card_congr
    { toFun := fun θ => F θ.1 θ.2
      invFun := fun p => ⟨B p, hBmem p⟩
      left_inv := ?_
      right_inv := ?_ }
  · rintro ⟨θ, hθ⟩
    apply Subtype.ext
    apply LinearEquiv.ext
    intro d
    obtain ⟨Y, rfl⟩ := Submodule.Quotient.mk_surjective _ d
    show B (F θ hθ) (Submodule.Quotient.mk Y) = θ (Submodule.Quotient.mk Y)
    rw [elim_eta O Y, mk_elim O cj hO Z₁ t t', map_add, map_add, (hB _).1, (hB _).2, (hF θ hθ).1,
      (hF θ hθ).2]
  · intro p
    set q := F (B p) (hBmem p)
    have hq := hF (B p) (hBmem p)
    apply Subtype.ext
    refine Prod.ext (LinearEquiv.ext fun m => ?_) (LinearEquiv.ext fun m => ?_)
    · refine uniqL O cj hO Z₂ hu₂ t t' hη₂ _ _ ?_ ?_
      · show iL O cj hO Z₂ t t' (q.1.1 m) = iL O cj hO Z₂ t t' (p.1.1 m)
        rw [← hq.1, (hB p).1]
      · show lamLQ O Z₂ hu₂ (q.1.1 m) = lamLQ O Z₂ hu₂ (p.1.1 m)
        rw [lamP, lamP]
    · refine uniqR O cj hO Z₂ hu₂ t t' hη₂ _ _ ?_ ?_
      · show iR O cj hO Z₂ t t' (q.1.2 m) = iR O cj hO Z₂ t t' (p.1.2 m)
        rw [← hq.2, (hB p).2]
      · show lamSQ O cj hO Z₂ hu₂ (q.1.2 m) = lamSQ O cj hO Z₂ hu₂ (p.1.2 m)
        rw [lamSP, lamSP]

theorem algAll_of (h : StepPairG) : Formalism.L2.SG.LocalCountModules.UnitaryGroupMassFormula.ThetaMbeU.AlgAll := by
  intro E _ O cj hcj hO r T T' hT hT' hcT hcT' Z₁ Z₂ hu₁ hu₂ hrel hG₁ hG₂
  rw [h E O cj hcj hO r T T' hT hT' hcT hcT' Z₁ Z₂ hu₁ hu₂ hrel hG₁ hG₂]
  exact Nat.card_congr (Equiv.ofBijective _
    ⟨stepInj E O cj hcj hO r Z₁ Z₂ hu₁ hu₂, stepAdjG E O cj hcj hO r Z₁ Z₂ hu₁ hu₂⟩)

end Formalism.L2.SG.LocalCountModules.UnramifiedPairingAlgebraic
