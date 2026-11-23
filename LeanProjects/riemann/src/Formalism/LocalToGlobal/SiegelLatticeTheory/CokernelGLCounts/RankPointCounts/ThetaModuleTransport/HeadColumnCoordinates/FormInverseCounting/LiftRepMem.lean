import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.FormInverseCounting.SumMapCompSub

noncomputable section

open Formalism.L2.SG.LocalCountModules.LocCntCommon

namespace Formalism.L2.SG.LocalCountModules.LocCnt0LAlg

variable {E : Type} [CommRing E] (O : Subring E) (cj : E →+* E) {r : ℕ}

theorem supp_inl (Y : Ix r → O) (h : ∀ a : Fin r, Y (Sum.inl a.castSucc) = 0) :
    (fun j => Y (Sum.inl j)) = Y (Sum.inl (Fin.last r)) • Pi.single (Fin.last r) 1 := by
  funext j
  induction j using Fin.lastCases with
  | last => simp
  | cast a => simp [h a, Pi.single_eq_of_ne (Fin.castSucc_lt_last a).ne]

theorem supp_inr (Y : Ix r → O) (h : ∀ a : Fin r, Y (Sum.inr a.castSucc) = 0) :
    (fun j => Y (Sum.inr j)) = Y (Sum.inr (Fin.last r)) • Pi.single (Fin.last r) 1 := by
  funext j
  induction j using Fin.lastCases with
  | last => simp
  | cast a => simp [h a, Pi.single_eq_of_ne (Fin.castSucc_lt_last a).ne]

theorem elim_eta (Y : Ix r → O) : Y = Sum.elim (fun j => Y (Sum.inl j)) (fun j => Y (Sum.inr j)) := by
  funext i
  cases i <;> rfl

theorem lift_e_mem {Z Z' : Matrix (Fin (r + 1)) (Fin (r + 1)) O} (f : MbMod Z →ₗ[O] MbMod Z')
    (he : f (eCl Z) = eCl Z') (s : O) :
    liftOf O f (s • Pi.single (Fin.last r) 1) - s • Pi.single (Fin.last r) 1 ∈ headCols Z' := by
  rw [← Submodule.Quotient.eq, liftOf_spec, Submodule.Quotient.mk_smul, Submodule.Quotient.mk_smul, map_smul]
  exact congrArg (s • ·) he

theorem lift_rep_mem {Z Z' : Matrix (Fin (r + 1)) (Fin (r + 1)) O} (f : MbMod Z ≃ₗ[O] MbMod Z')
    (y : Fin (r + 1) → O) (y₂ : Fin (r + 1) → O)
    (hy : (Submodule.Quotient.mk y : MbMod Z) = f.symm (Submodule.Quotient.mk y₂)) :
    liftOf O f.toLinearMap y - y₂ ∈ headCols Z' := by
  rw [← Submodule.Quotient.eq, liftOf_spec, hy, LinearEquiv.coe_toLinearMap, LinearEquiv.apply_symm_apply]

end Formalism.L2.SG.LocalCountModules.LocCnt0LAlg
