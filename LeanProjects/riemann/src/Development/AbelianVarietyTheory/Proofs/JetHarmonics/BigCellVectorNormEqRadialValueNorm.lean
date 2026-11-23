import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.BasicLiftAll
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutLemB
import Formalism.HermitianCurvature.HermitianCurvatureProofs.WCellMemOmPlus
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NFRadRedS
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

namespace GlobalTheory.HatNF

theorem vec_bigPt_eq_radial : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (c : Fin (P.r + 1) → ℂ), (∀ l, c l ≠ 0) → 0 < TBB.Gp p (TBB.bigPt P.r c) → ∃ x ∈ Q.DomR P.k P.r p.T.base.z p.T.base.z', gR P p.T.base x.1 x.2 = TBB.Gp p (TBB.bigPt P.r c) ∧ dR P p.T.base x.1 x.2 = ‖∏ l, c l‖ ∧ ∃ lam : ℝ, 0 < lam ∧ ∀ (H : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Φ : Q.RadSp P.k P.r p.T.base.z p.T.base.z' p.T.base.π p.T.base.π'), Top.IsRadOf P p.T.base Φ H → ‖B.hsVec (p.V H (TBB.bigPt P.r c))‖ = lam * nv Φ x := by
  intro Wp Wq _ _ _ _ _ _ P p c hc hG
  have hζ : Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z' < Complex.normSq (c (Fin.last P.r)) :=
    Formalism.FourierDecayAlt.P.PBM.zeta_big _ c hG
  have hc' : ∀ a : Fin P.r, c a.castSucc ≠ 0 := fun a => hc _
  have hz := Formalism.FourierDecayAlt.P.NFRadRedA.zeta_muZ p.T.base.z_mem p.T.base.z'_mem p.T.base.sec hζ
  have hx : ((fun a : Fin P.r => c a.castSucc), NF.muZ P.k P.r p.T.base.μsec (c (Fin.last P.r))) ∈
      Q.DomR P.k P.r p.T.base.z p.T.base.z' :=
    Formalism.FourierDecayAlt.P.NFRadRedA.mem_domR p.T.base.z_mem p.T.base.z'_mem p.T.base.sec
      (q := ((fun a : Fin P.r => c a.castSucc), c (Fin.last P.r))) ⟨hc', hζ⟩
  refine ⟨_, hx, ?_, ?_, ?_⟩
  · show Complex.normSq (∏ a : Fin P.r, c a.castSucc) *
        (Complex.normSq (Q.zetaL P.k P.r p.T.base.z p.T.base.z' (Fin.last P.r)
          (NF.muZ P.k P.r p.T.base.μsec (c (Fin.last P.r)))) - Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z') =
        D.ptG (Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z') P.r (Formalism.FourierDecayAlt.P.PBJ.bigPt c)
    unfold D.ptG
    rw [hz, Formalism.FourierDecayAlt.P.PBM.ptMatN_bigPt_head, Formalism.FourierDecayAlt.P.PBJ.Dens.ptMatN_bigPt, Formalism.FourierDecayAlt.P.PBM.hMat_one,
      Matrix.det_diagonal, Matrix.det_diagonal, Fin.prod_univ_castSucc c, Complex.normSq_mul]
    ring
  · show ‖(∏ a : Fin P.r, c a.castSucc) * Q.zetaL P.k P.r p.T.base.z p.T.base.z' (Fin.last P.r)
          (NF.muZ P.k P.r p.T.base.μsec (c (Fin.last P.r)))‖ = _
    rw [hz, Fin.prod_univ_castSucc c]
  · have hpos : 0 < ∏ a : Fin P.r,
        (if a.val < (Fin.last P.r).val then ‖c a.castSucc‖ ^ (Mdim P.k P.r a - 1) else 1 : ℝ) := by
      refine Finset.prod_pos fun a _ => ?_
      split_ifs
      · exact pow_pos (norm_pos_iff.2 (hc' a)) _
      · exact one_pos
    refine ⟨_, inv_pos.2 hpos, fun H Φ hΦ => ?_⟩
    rw [Formalism.FourierDecayAlt.P.CutBP.hsVec_norm_V_bigPt p H c hc hG]
    unfold nv
    rw [hΦ _ hx]
    unfold Q.resG
    rw [Formalism.FourierDecayAlt.P.TBBx2.Tri.hsVec_smul, norm_smul, Complex.norm_real, Real.norm_of_nonneg hpos.le,
      inv_mul_cancel_left₀ hpos.ne']
    have e : Q.wCell P.k P.r (Fin.last P.r) (fun a : Fin P.r => c a.castSucc) *
        NF.muZ P.k P.r p.T.base.μsec (c (Fin.last P.r)) =
        bigCell P.k P.r (fun a : Fin P.r => c a.castSucc) (p.T.base.μsec (c (Fin.last P.r))) := by
      unfold NF.muZ
      rw [Formalism.FourierDecayAlt.P5.Rad.wCell_last_eq, ← (Formalism.FourierDecayAlt.P.bruhat_big_cell_factorization _ _ _ _).1]
    rw [e]

end GlobalTheory.HatNF
