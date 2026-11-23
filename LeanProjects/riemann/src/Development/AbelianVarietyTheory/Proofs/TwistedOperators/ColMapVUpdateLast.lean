import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowShiftTheta
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompAtMtOfMemGfC

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.LastVertexInv

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.LastColumnMove

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

theorem fockComp_mul_right (B : VertexFrames G) (t : T) (j : ℕ) (hj : (Pair.top t j : Pair T).InRange D.R.m)
    {f : WO (G.pS (.top t j)) (G.pT (.top t j)) → ℂ} (hf : IsThetaFunO W.ψ _ _ f)
    (a : FinPt G (.top j)) (b h : FinPt G (.top (j + 1))) :
    fockComp W B (.top t j) f a (b * h) = fockComp W B (.top t j) (W.om (.top t j) (G.toPair (.top t j) 1 h.1) f) a b := by
  unfold fockComp
  congr 1
  funext k
  unfold jetTab kerFin GridData.Weil.ker thetaKO
  have e1 : G.toPair (.top t j) (a : GA D (G.V (Pair.top t j : Pair T).small)) ((b * h : FinPt G (.top (j + 1))) : GA D _) =
      G.toPair (.top t j) a b * G.toPair (.top t j) 1 h.1 := by
    simp [GridData.toPair, Prod.ext_iff]
  have e2 : G.toPair (.top t j) 1 h.1 = ((1 : GA D _), h.1) := rfl
  rw [e1, map_mul, Module.End.mul_apply, e2]
  unfold fockIn
  rw [GlobalTheory.OrientedHeis.om_fin_pureTensorO W.ψ _ _ _ _ (W.om _) (W.om_is _ hj) W.θ W.θ_is 1 (one_mem _) h.1 h.2 _ _ _ _ f _ hf]

theorem update_top_eq {a b : ℕ} (h : a = b) (x : ∀ j, FinPt G (.top j)) (v : FinPt G (.top a)) :
    Function.update x a v b = h ▸ v := by
  subst h; simp

theorem cast_mul_top {a b : ℕ} (h : a = b) (x : ∀ j, FinPt G (.top j)) (p : FinPt G (.top a)) :
    (h ▸ (x a * p) : FinPt G (.top b)) = x b * (h ▸ p : FinPt G (.top b)) := by
  subst h; rfl

theorem cast_conj_top {a b : ℕ} (h : a = b) (u : ∀ X : Node, FinPt G X) (p : FinPt G (.top a)) :
    (h ▸ ((u (.top a))⁻¹ * p * u (.top a)) : FinPt G (.top b)) = (u (.top b))⁻¹ * (h ▸ p : FinPt G (.top b)) * u (.top b) := by
  subst h; rfl

end GlobalTheory.LastColumnMove

namespace GlobalTheory.LastColumnMove

theorem colMapV_update_last : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T} (fs : ∀ j : Fin D.R.m, WO (G.pS (.top t j)) (G.pT (.top t j)) → ℂ) (x : ∀ j, FinPt G (.top j)) (g : FinPt G (.top D.R.m)),
    IsThetaFunO W.ψ (G.pS (.top t (lastIx D))) (G.pT (.top t (lastIx D))) (fs (lastIx D)) →
    colMapV S fs (Function.update x D.R.m (x D.R.m * g)) = colMapV S (Function.update fs (lastIx D) (colShift S t g (fs (lastIx D)))) x := by
  intro D T L sc G W U S t fs x g hf
  unfold colMapV
  refine congrArg (fun k => LinearMap.comp (chainTo (V := fun j => VV ℂ (wt G (.top j))) k D.R.m) _) ?_
  funext j
  by_cases hjm : j < D.R.m
  · rw [dif_pos hjm, dif_pos hjm]
    by_cases hj1 : j + 1 < D.R.m
    · have h1 : j ≠ D.R.m := by omega
      have h2 : j + 1 ≠ D.R.m := by omega
      have h3 : (⟨j, hjm⟩ : Fin D.R.m) ≠ lastIx D := by
        intro h; have := congrArg Fin.val h; simp [lastIx] at this; omega
      rw [Function.update_of_ne h1, Function.update_of_ne h2, Function.update_of_ne h3]
    · obtain rfl : j = (lastIx D : ℕ) := by simp [lastIx]; omega
      have h1 : ((lastIx D : ℕ)) ≠ D.R.m := by have := lastIx_succ D; omega
      rw [Function.update_of_ne h1, update_top_eq (lastIx_succ D), cast_mul_top (lastIx_succ D)]
      have e : ∀ a p v : FinPt G (.top ((lastIx D : ℕ) + 1)), a * p * v = a * v * (v⁻¹ * p * v) := by
        intro a p v; group
      rw [e, ← cast_conj_top (lastIx_succ D) S.N.u]
      have hf' : IsThetaFunO W.ψ _ _ (fs ⟨(lastIx D : ℕ), hjm⟩) := hf
      rw [fockComp_mul_right _ t _ (inRange_top t (lastIx D)) hf',
        show Function.update fs (lastIx D) (colShift S t g (fs (lastIx D))) ⟨(lastIx D : ℕ), hjm⟩ =
          colShift S t g (fs (lastIx D)) from Function.update_self _ _ _]
      rfl
  · rw [dif_neg hjm, dif_neg hjm]

end GlobalTheory.LastColumnMove
