import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowShiftTheta
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockCompMulFin

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.LastVertexInv

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.FirstRowVertex

open GlobalTheory.LastVertexInv

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

def firstIx (D : D7) : Fin D.R.m := ⟨0, by have := D.R.two_le_m; omega⟩

def rowShift0 (S : GridChoice W U) (k : FinPt G (.grid 0 D.R.m)) :
    (WO (G.pS (.chi (firstIx D) D.R.m : Pair T)) (G.pT (.chi (firstIx D) D.R.m : Pair T)) → ℂ) →ₗ[ℂ]
      (WO (G.pS (.chi (firstIx D) D.R.m : Pair T)) (G.pT (.chi (firstIx D) D.R.m : Pair T)) → ℂ) :=
  W.om (.chi (firstIx D) D.R.m) (G.toPair (.chi (firstIx D) D.R.m)
    ((S.N.u (.grid 0 D.R.m))⁻¹ * k * S.N.u (.grid 0 D.R.m)).1 1)

theorem rowShift0_theta (S : GridChoice W U) (k : FinPt G (.grid 0 D.R.m))
    {f : WO (G.pS (.chi (firstIx D) D.R.m : Pair T)) (G.pT (.chi (firstIx D) D.R.m : Pair T)) → ℂ}
    (h : IsThetaFunO W.ψ _ _ f) : IsThetaFunO W.ψ _ _ (rowShift0 S k f) :=
  (W.om_is _ (inRange_chi (firstIx D))).om_pres _ _ h

def movedRow (S : GridChoice W U) (k : FinPt G (.grid 0 D.R.m))
    (gs : ∀ i : Fin D.R.m, WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T)) → ℂ) :
    ∀ i : Fin D.R.m, WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T)) → ℂ :=
  Function.update gs (firstIx D) (rowShift0 S k (gs (firstIx D)))

theorem rowMapV_update_zero (S : GridChoice W U)
    (gs : ∀ i : Fin D.R.m, WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T)) → ℂ)
    (y : ∀ i, FinPt G (.grid i D.R.m)) (k : FinPt G (.grid 0 D.R.m))
    (hg : IsThetaFunO W.ψ (G.pS (.chi (firstIx D) D.R.m : Pair T)) (G.pT (.chi (firstIx D) D.R.m : Pair T)) (gs (firstIx D))) :
    rowMapV S gs (Function.update y 0 (y 0 * k)) = rowMapV S (movedRow S k gs) y := by
  unfold rowMapV movedRow
  refine congrArg (fun F => LinearMap.comp (chainTo (V := fun i => VV ℂ (wt G (.grid i D.R.m))) F D.R.m) _) ?_
  funext i
  by_cases hi : i < D.R.m
  · simp only [dif_pos hi]
    rcases Nat.eq_zero_or_pos i with h0 | hpos
    · subst h0
      simp only [Function.update_self, Function.update_of_ne (show (0 + 1 : ℕ) ≠ 0 by omega)]
      have hu : Function.update gs (firstIx D) (rowShift0 S k (gs (firstIx D))) ⟨0, hi⟩ = rowShift0 S k (gs (firstIx D)) :=
        Function.update_self _ _ _
      have hm : y 0 * k * S.N.u (.grid 0 D.R.m) =
          (y 0 * S.N.u (.grid 0 D.R.m)) * ((S.N.u (.grid 0 D.R.m))⁻¹ * k * S.N.u (.grid 0 D.R.m)) := by group
      rw [hu, hm]
      exact congrArg _ (GlobalTheory.KerTrans.fockComp_mul_fin W S.N.frC (inRange_chi (firstIx D)) _ hg _ _ _)
    · have h2 : (⟨i, hi⟩ : Fin D.R.m) ≠ firstIx D := by
        intro h; have := congrArg Fin.val h; simp [firstIx] at this; omega
      have hu : Function.update gs (firstIx D) (rowShift0 S k (gs (firstIx D))) ⟨i, hi⟩ = gs ⟨i, hi⟩ :=
        Function.update_of_ne h2 _ _
      have hy1 : Function.update y 0 (y 0 * k) i = y i := Function.update_of_ne (by omega) _ _
      have hy2 : Function.update y 0 (y 0 * k) (i + 1) = y (i + 1) := Function.update_of_ne (by omega) _ _
      rw [hu, hy1, hy2]
  · simp only [dif_neg hi]

theorem prod_update_smul {ι : Type} [Fintype ι] [DecidableEq ι] {X : ι → Type} (F : ∀ i, X i → ℂ) (i₀ : ι) (h : X i₀ → ℂ)
    (c : ℂ) (ys : ∀ i, X i) :
    ∏ i, Function.update F i₀ (c • h) i (ys i) = c * ∏ i, Function.update F i₀ h i (ys i) := by
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i₀), ← Finset.mul_prod_erase _ _ (Finset.mem_univ i₀)]
  simp only [Function.update_self, Pi.smul_apply, smul_eq_mul, mul_assoc]
  congr 2
  refine Finset.prod_congr rfl fun i hi => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hi), Function.update_of_ne (Finset.ne_of_mem_erase hi)]

end GlobalTheory.FirstRowVertex

end
