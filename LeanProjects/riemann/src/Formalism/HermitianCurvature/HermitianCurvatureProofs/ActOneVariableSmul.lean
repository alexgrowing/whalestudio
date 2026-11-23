import Formalism.HermitianCurvature.HermitianCurvatureProofs.BasePointMemDomain
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HeadJ
import Formalism.HermitianCurvature.HermitianCurvatureProofs.MemLevelZeroOfMemGroup
import Formalism.HermitianCurvature.HermitianCurvatureProofs.WCellMemOmPlus

open Matrix MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBP

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P.LevelPointCoordinates

theorem act_one_variable_smul {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {S : Type} [Fintype S] [DecidableEq S]
    (M : Wd.SlopeTestRemainingChoices S (Pr (V1 E))) (s : ℂ) (x : Wd.Ix S → V1 E) :
    act1 M (fun b => s • x b) = fun e => s • act1 M x e := by
  funext e
  simp only [act1, map_smul, Finset.smul_sum]

theorem kapM_eq (P : M.Par) (j : ℕ) : kapM (P.r - j) P.k = kapJ P j := by
  unfold kapM kapJ
  push_cast
  ring

theorem headPic_of (hJ : HeadJ) : HeadPic := by
  intro Wp Wq _ _ _ _ _ _ P p F j hj w h hh X μ L st Φ hD hF hw hΦ t ht e y hy
  have ht0 : t ≠ 0 := (ht.1 (1, t) (List.mem_append_right _ (List.mem_singleton_self _))).2
  have hn : 1 + (P.r - (j + 1)) = P.r - j := by omega
  have hc : y.1 ∈ OmX (P.r - (j + 1)) := hy.1
  have hdom := fun τ (hτ : τ ≠ 0) => base_point_mem_domain hn (PBH.levTower_bs_z_eq_castV_liftVec p.T j hj) (PBH.levTower_bs_z'_eq_castV_liftVec p.T j hj) hy hτ
  have hL : IsActualLevel X L := hD.2.2.1

  set gg : ℝ := ∏ a : Fin (P.r - (j + 1)),
    (if a.val < (Fin.last (P.r - (j + 1))).val then ‖y.1 a‖ ^ (Mdim P.k (P.r - (j + 1)) a - 1) else 1) with hgg
  have hgg0 : gg ≠ 0 := Finset.prod_ne_zero_iff.2 fun a _ => by
    split_ifs
    · exact pow_ne_zero _ (norm_ne_zero_iff.2 (hc a))
    · exact one_ne_zero
  set γ := wCell P.k (P.r - (j + 1)) (Fin.last _) y.1 * y.2 with hγdef
  have hγ : γ ∈ B.GV P.k (P.r - (j + 1)) := Formalism.FourierDecayAlt.P.PBF.wCell_mul_GV hc hy.2.1
  have hΩ : γ ∈ Q.OmPlus P.k (P.r - (j + 1)) (p.T.bs (j + 1)).z (p.T.bs (j + 1)).z' :=
    Formalism.FourierDecayAlt.P5.Rad.wCell_mem_omPlus (p.T.bs (j + 1)).z_mem (p.T.bs (j + 1)).z'_mem hy.1 hy.2.1 hy.2.2

  let Rd := rdL (k := P.k) (π := (p.T.bs j).π) (π' := (p.T.bs j).π') hn y hdom
  let φ : Wd.Ix (Fin w.length) → V1 (Wq →L[ℂ] Wp) := fun b => (((gg⁻¹ : ℝ)) : ℂ) • Rd (Φ b)
  have hφ : ∀ b τ, τ ≠ 0 → (φ b).1 τ =
      B.JF (p.T.bs j) (KB.slv p.T F j (by omega) w h hh.2 b) (mLev P j hj τ γ) := by
    intro b τ hτ
    have hr := pic_read (k := P.k) hn (PBH.levTower_bs_z_eq_castV_liftVec p.T j hj) (PBH.levTower_bs_z'_eq_castV_liftVec p.T j hj)
      (Subtype.val (Φ b)) (B.JF (p.T.bs j) (KB.slv p.T F j (by omega) w h hh.2 b)) (hΦ b) hτ y hy
    have hraw := raw_eq hn y hdom (Φ b) hτ
    change (((gg⁻¹ : ℝ)) : ℂ) • (Rd (Φ b)).1 τ = _
    have hpos : ‖τ‖ ^ (2 * (P.r - j) + P.k) ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.2 hτ)
    have hR : (Rd (Φ b)).1 τ = Q.resG P.k (P.r - (j + 1)) (Fin.last _)
        (fun γ' => B.JF (p.T.bs j) (KB.slv p.T F j (by omega) w h hh.2 b)
          (D.castM hn (U.mMap P.k 1 (P.r - (j + 1)) (Matrix.of fun _ _ => τ) γ'))) y.1 y.2 := by
      have h2 := hraw.symm.trans hr
      have h3 := congrArg (fun v => (((‖τ‖ ^ (2 * (P.r - j) + P.k))⁻¹ : ℝ) : ℂ) • v) h2
      simp only [smul_smul, ← Complex.ofReal_mul, inv_mul_cancel₀ hpos, Complex.ofReal_one, one_smul] at h3
      exact h3
    rw [hR]
    unfold resG
    rw [smul_smul, ← Complex.ofReal_mul, inv_mul_cancel₀ hgg0, Complex.ofReal_one, one_smul]
    rfl
  have hRφ : (fun b => Rd (Φ b)) = fun b => ((gg : ℝ) : ℂ) • φ b := by
    funext b
    simp only [φ, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hgg0, Complex.ofReal_one, one_smul]
  have hJe := hJ Wp Wq P p F j hj w h hh γ hF hw hγ hΩ φ hφ t ht e

  have hraw := raw_eq hn y hdom (P5.act (P5.bTl L ⟨0, by change 0 < P.r - j; omega⟩ (D.positionted w)) Φ e) ht0
  have hact := rd_act hn y hc hdom X hL (D.positionted w) Φ e
  refine hraw.trans ?_
  change ((‖t‖ ^ (2 * (P.r - j) + P.k) : ℝ) : ℂ) • (Rd (P5.act _ Φ e)).1 t = _
  rw [hact, hRφ]
  unfold oneBT
  rw [act_one_variable_smul, kapM_eq]
  change ((‖t‖ ^ (2 * (P.r - j) + P.k) : ℝ) : ℂ) • (((gg : ℝ) : ℂ) • (oneBT (kapJ P j) (D.positionted w) φ e).1 t) = _
  rw [← hJe]
  congr 1

end Formalism.FourierDecayAlt.P.PBP

namespace Formalism.FourierDecayAlt.P

theorem pb_radHead_of_headJ (hJ : LevelPointCoordinates.HeadJ) : KB.RadHead := pb_radHead_of_headPic (PBP.headPic_of hJ)

end Formalism.FourierDecayAlt.P
