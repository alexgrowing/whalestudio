import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.SchurCoreA
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.HermitianCombinationZ

noncomputable section

open scoped Classical InnerProductSpace
open MeasureTheory NumberField Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
  Formalism.L2.SG.TermOp Formalism.L2.SG.Full

namespace PI.SchurPlaces

open Formalism.L2.SG.KappaOffDiagonal PI.SchurPlaces.LeviLA

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem frameAt (X : HidaSetting D) (u : D.what₂.Word) (v : InfinitePlace X.B.I.F) :
    Frame (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (fun a => rv X.B.I v (X.fR a)) (rv X.B.I v (X.zR u))
      (X.wfr u v) where
  ee a b := by
    simp only [HidaSetting.eR]; rw [Formalism.L2.SG.PoincareInHH.Cut.hJ_crd, X.ee, map_zero]
  ef a b := by
    simp only [HidaSetting.eR, HidaSetting.fR]; rw [Formalism.L2.SG.PoincareInHH.Cut.hJ_crd, X.ef]; split_ifs <;> simp
  ff a b := by
    simp only [HidaSetting.fR]; rw [Formalism.L2.SG.PoincareInHH.Cut.hJ_crd, X.ff, map_zero]
  ez a := by
    simp only [HidaSetting.eR, HidaSetting.zR]; rw [Formalism.L2.SG.PoincareInHH.Cut.hJ_crd, (X.zu_orth u a).1, map_zero]
  fz a := by
    simp only [HidaSetting.fR, HidaSetting.zR]; rw [Formalism.L2.SG.PoincareInHH.Cut.hJ_crd, (X.zu_orth u a).2, map_zero]
  ew a b := ((X.wfr_perp u v b).1 a).1
  fw a b := ((X.wfr_perp u v b).1 a).2
  zw b := (X.wfr_perp u v b).2
  ww := X.wfr_on u v
  zz := by
    simp only [HidaSetting.zR]
    rw [Formalism.L2.SG.PoincareInHH.Cut.hJ_crd, X.zu_norm, map_neg, map_natCast]
    exact neg_ne_zero.2 (Nat.cast_ne_zero.2 (D.mem u).A.T_prime.ne_zero)
  card := by
    have h1 := X.n_eq; have h2 := D.R.r_eq; have h3 := D.R.rS_two; omega

theorem wfrSpan : WfrSpan := by
  intro D X u v y hef hz
  exact perp_efz (frameAt X u v) y hef hz

theorem leviTens : LeviTens := by
  intro D X u h hh x
  have hS : ∀ v, InS (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u)) (uMat (h v)) := hh
  choose V hVu hVe hVf hVz hVw hVN using fun v =>
    levi_place (frameAt X u v) ((h v : Formalism.REAL.UJ (X.B.I.ε v)) : (Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ)ˣ)
      (h v).2 (hS v)
  let s0 : X.B.I.Ginf := fun v => ⟨V v, hVu v⟩
  have hs0 : ∀ v, uMat (s0 v) = (V v : Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ) := fun v => rfl
  have hn : ∀ v, uMat ((s0⁻¹ * h) v) =
      (((V v)⁻¹ : (Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ)ˣ) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ) *
        uMat (h v) := fun v => rfl
  have hs0S : s0 ∈ X.SinfU u := by
    intro v
    refine ⟨fun a => ?_, ?_⟩
    · rw [hs0, sub_mulVec, one_mulVec, hVe v a, sub_self]; exact zero_mem _
    · rw [hs0, sub_mulVec, one_mulVec, hVz v, sub_self]; exact zero_mem _
  have hnN : s0⁻¹ * h ∈ X.NinfU u := fun v => by rw [show uMat ((s0⁻¹ * h) v) = _ from hn v]; exact hVN v
  have hnS : s0⁻¹ * h ∈ X.SinfU u := fun v => (hnN v).1
  have hsplit : h = s0 * (s0⁻¹ * h) := by rw [mul_inv_cancel_left]
  have hpi : X.piU u h = X.piU u s0 := by
    rw [hsplit, (X.piU_rep u).2.1 s0 hs0S _ hnS, (X.piU_rep u).2.2.2.1 _ hnN, mul_one]
  have hs0H : s0 ∈ Hset X.B.I (Set.range (fun a => crdOf X.B.I X.ιE X.bas (X.eX a)) ∪
      Set.range (fun a => crdOf X.B.I X.ιE X.bas (X.fY a)) ∪ {crdOf X.B.I X.ιE X.bas (X.zu u)}) := by
    intro v p hp
    rw [hs0]
    rcases hp with (⟨a, rfl⟩ | ⟨a, rfl⟩) | hp
    · exact hVe v a
    · exact hVf v a
    · rw [Set.mem_singleton_iff] at hp; subst hp; exact hVz v
  have hmat : ∀ v, matW X.B.I (X.wfr u v) v s0 = matW X.B.I (X.wfr u v) v h := fun v => by
    ext a b; exact hVw v a b
  rw [hpi, X.tensU_equiv u s0 hs0H x]
  simp only [hmat]

end PI.SchurPlaces
