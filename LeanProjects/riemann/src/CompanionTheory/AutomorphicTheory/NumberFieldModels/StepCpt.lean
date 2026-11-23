import CompanionTheory.AutomorphicTheory.NumberFieldModels.HsVecProjLe
import CompanionTheory.AutomorphicTheory.NumberFieldModels.ModelPt
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFCoreN
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFHatProdKBStmt

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutBP Formalism.FourierDecayAlt.P.CutMP.Gauge

namespace Formalism.MainStatements.NFTie

noncomputable section

def StepCpt : Prop :=
  ∃ C₁ : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (w : List C.Letter), KB.CutWord P p.l0 w → ∀ (a : Wd.Ix (Fin w.length)) (N : ℕ), w.length ≤ N → ∀ s : ℕ,
    ∃ (m : ℕ) (Th : Fin m → B.DiffOp P.k P.r Wp Wq) (K : ℝ), 0 ≤ K ∧ (∀ t, NFOpOK C₁ p N (Th t)) ∧
      ∀ F : B.Mat P.k P.r → (Wq →L[ℂ] Wp), KB.CptCoef p.T.base F →
      ∀ (ρ : M.Ty P) (c : Fin (P.r + 1) → ℂ), D.IsLocPt (TBB.bigPt P.r c) (P.r + 1) → 0 < TBB.Gp p (TBB.bigPt P.r c) →
        Top.dH P p.l0 (TBB.TTp p) w (TBB.bigPt P.r c) a ρ ^ 2 *
            ‖B.hsVec (p.V (p.Θ.Θ w a fun g => ((Gf P.k P.r p.T.base.z p.T.base.z' g ^ s : ℝ) : ℂ) • F g)
              (TBB.bigPt P.r c))‖ ^ 2 ≤
          K * TBB.Gp p (TBB.bigPt P.r c) ^ (2 * s) * TBB.Gp p (TBB.bigPt P.r c) ^ (-(w.length : ℤ)) *
            ∑ t, ‖B.hsVec (p.V (B.opApply (Th t) F) (TBB.bigPt P.r c))‖ ^ 2

section pt

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem tt_eq (p : KB.Pl P Wp Wq) : P.TT = TBB.TTp p := by
  unfold M.Par.TT TBB.TTp
  rw [p.hP.2.2.2.1, p.hP.2.2.2.2.1]

theorem det_bigPt (r : ℕ) (c : Fin (r + 1) → ℂ) :
    (D.ptMatN (TBB.bigPt r c) (r + 1)).det = (∏ l : Fin r, c l.castSucc) * c (Fin.last r) := by
  show (D.ptMatN (PBJ.bigPt c) (r + 1)).det = _
  rw [PBJ.Dens.ptMatN_bigPt, PBM.hMat_one, Matrix.det_diagonal, Fin.prod_univ_castSucc]

theorem gp_eq (p : KB.Pl P Wp Wq) (c : Fin (P.r + 1) → ℂ) (q : MA.Qp P.r P.TT)
    (hq : q.1 = ((fun l => c l.castSucc), c (Fin.last P.r))) : TBB.Gp p (TBB.bigPt P.r c) = MA.Gq P q := by
  show D.ptG (TBB.TTp p) P.r (TBB.bigPt P.r c) = _
  unfold D.ptG MA.Gq
  rw [det_bigPt]
  have h : D.ptMatN (TBB.bigPt P.r c) P.r = _ := PBM.ptMatN_bigPt_head c
  rw [h, Matrix.det_diagonal, hq, Complex.normSq_mul, map_prod, ← tt_eq p]
  ring

theorem sxV (p : KB.Pl P Wp Wq) (H : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (c : Fin (P.r + 1) → ℂ) (hd : ∀ a, c a ≠ 0)
    (hG : 0 < TBB.Gp p (TBB.bigPt P.r c)) (q : MA.Qp P.r P.TT)
    (hq : q.1 = ((fun l => c l.castSucc), c (Fin.last P.r))) :
    (∏ l : Fin P.r, Complex.normSq (c l.castSucc)) *
        (Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) (TBB.bigPt P.r c)) *
          Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) (TBB.bigPt P.r c)) * ‖B.hsVec (p.V H (TBB.bigPt P.r c))‖ ^ 2) =
      MA.wq P.k q.1 P.TT * ‖B.hsVec (B.JF p.T.base H (B.gq p.T.base q.1))‖ ^ 2 := by
  have hTT := tt_eq p
  have hζ : P.TT < Complex.normSq q.1.2 := q.2.2
  have hζ' : Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z' ≤ Complex.normSq (c (Fin.last P.r)) := by
    have : q.1.2 = c (Fin.last P.r) := by rw [hq]
    rw [← this]
    exact le_trans (le_of_eq hTT.symm) hζ.le
  have hn' : TBB.nPt P.k P.r (TBB.TTp p) (TBB.bigPt P.r c) =
      bcWeight P.k P.r (Tz P.k P.r p.T.base.z) (Tz P.k P.r p.T.base.z') ((fun j => c j.castSucc), c (Fin.last P.r)) :=
    nPt_bigPt P.k P.r (Tz P.k P.r p.T.base.z) (Tz P.k P.r p.T.base.z') c hζ'
  rw [hsVec_norm_V_bigPt p H c hd hG, hn', Real.mul_self_sqrt (bcWeight_nonneg0 _ _ _ _ _)]
  have hwq : MA.wq P.k q.1 P.TT = (∏ l : Fin P.r, Complex.normSq (c l.castSucc)) *
      bcWeight P.k P.r (Tz P.k P.r p.T.base.z) (Tz P.k P.r p.T.base.z') ((fun j => c j.castSucc), c (Fin.last P.r)) := by
    rw [hq, hTT]
    exact nf_wq_eq P.k P.r _ _ _ hζ'
  have hgq : B.gq p.T.base q.1 = bigCell P.k P.r (fun i => c i.castSucc) (p.T.base.μsec (c (Fin.last P.r))) := by
    unfold B.gq; rw [hq]
  rw [hwq, hgq]
  ring

theorem dH_sq_le (p : KB.Pl P Wp Wq) (w : List C.Letter) (a : Wd.Ix (Fin w.length)) (ρ : M.Ty P)
    (c : Fin (P.r + 1) → ℂ) (hG : 0 < TBB.Gp p (TBB.bigPt P.r c)) :
    Top.dH P p.l0 (TBB.TTp p) w (TBB.bigPt P.r c) a ρ ^ 2 ≤
      (∑ ρ' : M.Ty P, |(Top.cW P p.l0 w a ρ').re|) *
        (Complex.normSq ((∏ l : Fin P.r, c l.castSucc) * c (Fin.last P.r)) / TBB.Gp p (TBB.bigPt P.r c)) ^ w.length := by
  have hW : Top.wPt (TBB.TTp p) P.r (TBB.bigPt P.r c) =
      Complex.normSq ((∏ l : Fin P.r, c l.castSucc) * c (Fin.last P.r)) / TBB.Gp p (TBB.bigPt P.r c) := by
    unfold Top.wPt; rw [det_bigPt]; rfl
  unfold Top.dH
  rw [hW, Real.sq_sqrt']
  set W := (Complex.normSq ((∏ l : Fin P.r, c l.castSucc) * c (Fin.last P.r)) / TBB.Gp p (TBB.bigPt P.r c)) ^ w.length
  have hW0 : 0 ≤ W := pow_nonneg (div_nonneg (Complex.normSq_nonneg _) hG.le) _
  have h1 : |(Top.cW P p.l0 w a ρ).re| ≤ ∑ ρ' : M.Ty P, |(Top.cW P p.l0 w a ρ').re| :=
    Finset.single_le_sum (f := fun ρ' => |(Top.cW P p.l0 w a ρ').re|) (fun _ _ => abs_nonneg _) (Finset.mem_univ ρ)
  have h2 := le_abs_self (Top.cW P p.l0 w a ρ).re
  refine max_le ?_ (mul_nonneg (le_trans (abs_nonneg _) h1) hW0)
  rw [mul_comm]
  exact mul_le_mul_of_nonneg_right (le_trans h2 h1) hW0

theorem cpt_Gpow (p : KB.Pl P Wp Wq) (s : ℕ) {F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)} (hF : KB.CptCoef p.T.base F) :
    KB.CptCoef p.T.base fun g => ((Gf P.k P.r p.T.base.z p.T.base.z' g ^ s : ℝ) : ℂ) • F g := by
  obtain ⟨h1, ⟨R, hR⟩, ε, hε, h3⟩ := hF
  refine ⟨ckOn_Gpow_smul _ _ s h1, ⟨R, fun g hg h => hR g hg fun h0 => h (by simp only [h0, smul_zero])⟩,
    ε, hε, fun g hg h => h3 g hg fun h0 => h (by simp only [h0, smul_zero])⟩

end pt

end

end Formalism.MainStatements.NFTie
