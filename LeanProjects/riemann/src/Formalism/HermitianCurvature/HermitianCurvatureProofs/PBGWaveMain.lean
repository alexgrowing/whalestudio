import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBGSlice
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBGLet

open Matrix Finset
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBG

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

theorem letter_level_zero_eq {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (z z' : Fin (2 * r + k + 1) → ℂ)
    (hj : 0 ≤ r) (l : C.Letter) (e : Fin 2) (G : B.Mat k r → E) :
    D.vLet k r z z' 0 hj l e G = if e = 0 then G else fun _ => 0 := by
  funext g
  by_cases he : e = 0
  · subst he
    have hD0 : Dmin k r z z' g 0 = 1 := by simp [Dmin]
    rcases l with ⟨b, Y⟩
    cases b <;>
      simp [D.vLet, C3.AAop, C3.AAvop, qminorOp, Matrix.det_isEmpty, Finset.univ_unique] <;>
      rw [if_pos (show StrictMono _ from fun a => a.elim0)] <;> simp [hD0]
  · have he1 : e = 1 := by omega
    subst he1
    simp [D.vLet]

theorem slicePolyAll : SlicePolyAll := by
  intro Wp Wq _ _ _ _ _ _ P p F hF j hj h hh w' b δ e
  by_cases hj0 : j = 0
  · subst hj0
    refine ⟨fun _ => if e = 0 then KB.slv p.T F 0 hj w' h hh.2 else 0, rfl, fun l => ?_, fun t => ?_⟩
    · by_cases he : e = 0
      · simp only [he, if_true]
        exact nice_vec_of_cpt (p.T.bs 0) (fun a => Formalism.FourierDecayAlt.P.slice_compact_support_coefficient Wp Wq P p F 0 hj w' h hh hF a)
      · simp only [he, if_false]
        exact ⟨0, fun a => Formalism.FourierDecayAlt.P.JCx2.mn_nice_zero⟩
    · intro a g hg
      show D.castF _ (D.sliceAt P.k P.r p.T.base.z p.T.base.z'
        (D.vLet P.k P.r p.T.base.z p.T.base.z' 0 hj (b, t + δ) e
          (D.uwG P.k P.r p.T.base.z p.T.base.z' F 0 hj w' a)) h) g = _
      rw [letter_level_zero_eq]
      by_cases he : e = 0
      · simp [he, Finset.sum_apply, Fin.sum_univ_succ, KB.slv]
      · simp [he, sliceAt_zero, Finset.sum_apply, D.castF]
  · refine slicePoly_of_pt p.T F hF j hj (by omega) h hh w' b δ e (fun a g hg hD => ?_)
    obtain ⟨c, hcl, hc⟩ := uwG_letter_poly p.T.base.z p.T.base.z' j hj hF.1 w' a g hg hD b e
    obtain ⟨c', hc'l, hsh⟩ := poly_shift j c (δ : ℂ)
    refine ⟨c', hc'l.trans hcl, fun t => ?_⟩
    show D.vLet P.k P.r p.T.base.z p.T.base.z' j hj (b, t + δ) e (D.uwG P.k P.r p.T.base.z p.T.base.z' F j hj w' a) g = _
    rw [hc (t + δ), ← hsh (t : ℂ)]
    push_cast
    rfl

theorem _root_.Formalism.FourierDecayAlt.P.degree_of_plane_wave : KB.DegWave := degWave_of slicePolyAll

end Formalism.FourierDecayAlt.P.PBG
