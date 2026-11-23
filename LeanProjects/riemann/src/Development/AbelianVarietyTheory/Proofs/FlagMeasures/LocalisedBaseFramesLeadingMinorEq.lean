import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocFacts
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc Formalism.L2.SG.TermDef GlobalTheory.LocOver
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocMinor

theorem leadMinor_atBase : ∀ (D : D7) (Z : LocDat D) (p : PlF D) {T T' : D.host.E} (F : LFlag (VS D) D.R.rS T)
    (F' : LFlag (VS D) D.R.rS T') (Tn T'n : ℕ) (P : Formalism.MainNotions.S.LocNG.FPair (locH Z p) D.R.rS),
    AtBase Z p F F' Tn T'n P → ∀ l : ℕ, P.Dm l =
      (∏ a : Fin (D.R.rS + 1), if a.val < l then (Z.M p).L.cj (frFac Z.δ p a) * frFac Z.δ p a else 1) *
        (D.s.atP p).ιE (Formalism.MainNotions.S.Dl F.fl F'.fl l) := by
  intro D Z p T T' F F' Tn T'n P hP l
  obtain ⟨hA, hB, -, -⟩ := hP
  have hent : ∀ a b, (locH Z p).Zhat P.A.f P.B.f a b =
      (Z.M p).L.cj (frFac Z.δ p a) * (frFac Z.δ p b *
        (D.s.atP p).ιE (Formalism.MainNotions.S.Zhat F.fl F'.fl a b)) := by
    intro a b
    rw [hA, hB]
    show LocFacts₂ Z.M p (frFac Z.δ p b • baseChange₂ D p (frame F' b)) (frFac Z.δ p a • baseChange₂ D p (frame F a)) = _
    rw [Formalism.L2.SG.Pf.LocFacts.localForm_smul_left₂, Formalism.L2.SG.Pf.LocFacts.localForm_smul_right, baseChangeAt_form Z.M p (Z.hcj p)]
    simp only [Formalism.MainNotions.S.Zhat, frame]
    ring
  show (locH Z p).Dl P.A.f P.B.f l = _
  unfold Loc.HermSp.Dl Formalism.MainNotions.S.Dl Formalism.MainNotions.S.leadMinorE
  split_ifs with hl
  · rw [RingHom.map_det]
    have hM : ((locH Z p).Zhat P.A.f P.B.f).submatrix (Fin.castLE hl) (Fin.castLE hl) =
        Matrix.of fun i j => (Z.M p).L.cj (frFac Z.δ p (Fin.castLE hl i)) * (frFac Z.δ p (Fin.castLE hl j) *
          (((Formalism.MainNotions.S.Zhat F.fl F'.fl).submatrix (Fin.castLE hl) (Fin.castLE hl)).map (D.s.atP p).ιE) i j) := by
      ext i j
      simp only [Matrix.submatrix_apply, Matrix.of_apply, Matrix.map_apply, hent]
    have e1 := Matrix.det_mul_column (fun i : Fin l => (Z.M p).L.cj (frFac Z.δ p (Fin.castLE hl i)))
      (Matrix.of fun i j => frFac Z.δ p (Fin.castLE hl j) *
          (((Formalism.MainNotions.S.Zhat F.fl F'.fl).submatrix (Fin.castLE hl) (Fin.castLE hl)).map (D.s.atP p).ιE) i j)
    have e2 := Matrix.det_mul_row (fun j : Fin l => frFac Z.δ p (Fin.castLE hl j))
      (((Formalism.MainNotions.S.Zhat F.fl F'.fl).submatrix (Fin.castLE hl) (Fin.castLE hl)).map (D.s.atP p).ιE)
    simp only [Matrix.of_apply] at e1
    rw [RingHom.mapMatrix_apply, hM, e1, e2, ← mul_assoc, ← Finset.prod_mul_distrib]
    congr 1
    set g : ℕ → (D.s.atP p).Ep := fun k => if h : k < D.R.rS + 1 then
      (Z.M p).L.cj (frFac Z.δ p ⟨k, h⟩) * frFac Z.δ p ⟨k, h⟩ else 1 with hg
    have h1 : (∏ a : Fin (D.R.rS + 1), if a.val < l then (Z.M p).L.cj (frFac Z.δ p a) * frFac Z.δ p a else 1)
        = ∏ k ∈ Finset.range (D.R.rS + 1), if k < l then g k else 1 := by
      rw [← Fin.prod_univ_eq_prod_range (fun k => if k < l then g k else 1)]
      refine Finset.prod_congr rfl fun a _ => ?_
      show _ = (if a.val < l then g a.val else 1)
      rw [hg]; dsimp only; rw [dif_pos a.isLt]
    have h2 : (∏ i : Fin l, (Z.M p).L.cj (frFac Z.δ p (Fin.castLE hl i)) * frFac Z.δ p (Fin.castLE hl i))
        = ∏ k ∈ Finset.range l, g k := by
      rw [← Fin.prod_univ_eq_prod_range g]
      refine Finset.prod_congr rfl fun i _ => ?_
      have : i.val < D.R.rS + 1 := lt_of_lt_of_le i.isLt hl
      show _ = g i.val
      rw [hg]; dsimp only; rw [dif_pos this]; rfl
    rw [h1, h2, ← Finset.prod_filter]
    congr 1
    ext k
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  · simp

end GlobalTheory.LocMinor
