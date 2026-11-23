import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutHB2
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ExistsCompactCutoffCoefficient
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SliceInductionLevel
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBGLet
import Formalism.HermitianCurvature.HermitianCurvatureProofs.VLetZeroNear
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ComponentFamilySettingOfSettingBis
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BigCellVanishingOfCommute

open Matrix MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutHB

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.LevelPointCoordinates Formalism.FourierDecayAlt.P.PBQ

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def CutOffStep : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (F)
    (j : ℕ) (hj : j + 1 ≤ P.r) (w : List C.Letter) (h : C.LPt) (hh : D.IsLocPt h j)
    (γ : B.Mat P.k (P.r - (j + 1))),
    γ ∈ B.GV P.k (P.r - (j + 1)) →
    γ ∈ Q.OmPlus P.k (P.r - (j + 1)) (p.T.bs (j + 1)).z (p.T.bs (j + 1)).z' →
    ∀ (t : ℂ) (ht : D.IsLocPt (h ++ [(1, t)]) (j + 1)) (e : Wd.Ix (Fin w.length))
      (Fc : B.Mat P.k P.r → (Wq →L[ℂ] Wp)), KB.CptCoef p.T.base Fc →
      (∀ g, Dmin P.k P.r p.T.base.z p.T.base.z' g ⟨j + 1, by omega⟩ = (U.hMat (D.ptPerm h) (D.ptDiag h)).det * t →
        Fc g = D.uwG P.k P.r p.T.base.z p.T.base.z' F (j + 1) hj w e g) →
      B.JF (p.T.bs (j + 1)) (KB.slv p.T F (j + 1) hj w (h ++ [(1, t)]) ht.2 e) γ =
        B.JF (p.T.bs j) (KB.slv p.T Fc j (by omega) [] h hh.2 (fun a => a.elim0)) (mLev P j hj t γ)

def CutOffExists : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (F)
    (j : ℕ) (hj : j + 1 ≤ P.r) (w : List C.Letter) (h : C.LPt) (hh : D.IsLocPt h j),
    KB.CptCoef p.T.base F →
    ∀ (t : ℂ) (ht : D.IsLocPt (h ++ [(1, t)]) (j + 1)) (e : Wd.Ix (Fin w.length)),
      ∃ Fc : B.Mat P.k P.r → (Wq →L[ℂ] Wp), KB.CptCoef p.T.base Fc ∧
        ∀ g, Dmin P.k P.r p.T.base.z p.T.base.z' g ⟨j + 1, by omega⟩ = (U.hMat (D.ptPerm h) (D.ptDiag h)).det * t →
          Fc g = D.uwG P.k P.r p.T.base.z p.T.base.z' F (j + 1) hj w e g

section proofs

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem det_hMat_app (h : C.LPt) (t : ℂ) :
    (U.hMat (D.ptPerm (h ++ [(1, t)])) (D.ptDiag (h ++ [(1, t)]))).det =
      (U.hMat (D.ptPerm h) (D.ptDiag h)).det * t := by
  rw [Formalism.FourierDecayAlt.P.PBI.det_hMat_pt, Formalism.FourierDecayAlt.P.PBI.det_hMat_pt h]
  have hsz : D.ptSize (h ++ [(1, t)]) = D.ptSize h + 1 := by
    simp [D.ptSize]
  rw [hsz, (Formalism.FourierDecayAlt.P.PBD.det_ptMatN_app t h (D.ptSize h) rfl).1, mul_comm]

theorem uwG_zero_of_G {k r : ℕ} (z z' : Fin (2 * r + k + 1) → ℂ) (F : B.Mat k r → (Wq →L[ℂ] Wp)) (ε : ℝ)
    (hε : ∀ g ∈ B.GV k r, F g ≠ 0 → ε ≤ Gf k r z z' g) (i : ℕ) (hi : i ≤ r) :
    ∀ (w : List C.Letter) (e : Wd.Ix (Fin w.length)), ∀ g ∈ B.GV k r,
      D.uwG k r z z' F i hi w e g ≠ 0 → ε ≤ Gf k r z z' g
  | [], _, g, hg, hne => hε g hg hne
  | l :: w, e, g, hg, hne => by
    by_contra hlt
    push Not at hlt
    apply hne
    show D.vLet k r z z' i hi l (e 0) (D.uwG k r z z' F i hi w fun a => e a.succ) g = 0
    refine Formalism.FourierDecayAlt.P.PBG.vLet_zero_near z z' i hi l (e 0) _ (V := {x | Gf k r z z' x < ε})
      (isOpen_lt (Formalism.FourierDecayAlt.P.DifferentialOperatorClasses.gf_cont k r z z') continuous_const) (fun x hx hxG => ?_) g hlt hg
    by_contra h0
    exact absurd (uwG_zero_of_G z z' F ε hε i hi w _ x hxG h0) (not_le.2 hx)

def cutW {P : M.Par} (Bs : B.RealPlaceData P.k P.r Wp Wq) (χ : ℂ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (i : ℕ)
    (hi : i ≤ P.r) (w : List C.Letter) (e : Wd.Ix (Fin w.length)) : B.Mat P.k P.r → (Wq →L[ℂ] Wp) :=
  fun g => χ (Dmin P.k P.r Bs.z Bs.z' g ⟨i, by omega⟩) • D.uwG P.k P.r Bs.z Bs.z' F i hi w e g

theorem cutW_exists {P : M.Par} (Bs : B.RealPlaceData P.k P.r Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp))
    (hF : KB.CptCoef Bs F) (i : ℕ) (hi : i ≤ P.r) (w : List C.Letter) (e : Wd.Ix (Fin w.length)) (a : ℂ)
    (ha : a ≠ 0) :
    ∃ Fc : B.Mat P.k P.r → (Wq →L[ℂ] Wp), KB.CptCoef Bs Fc ∧
      ∀ g, Dmin P.k P.r Bs.z Bs.z' g ⟨i, by omega⟩ = a → Fc g = D.uwG P.k P.r Bs.z Bs.z' F i hi w e g := by
  obtain ⟨hck, ⟨R, hR⟩, ε, hε, hεG⟩ := hF
  have hn : 0 < ‖a‖ := norm_pos_iff.mpr ha
  let b : ContDiffBump a := ⟨‖a‖ / 4, ‖a‖ / 2, by positivity, by linarith⟩
  have hD : ContDiff ℝ (⊤ : ℕ∞) (fun g : B.Mat P.k P.r => Dmin P.k P.r Bs.z Bs.z' g ⟨i, by omega⟩) :=
    Formalism.FourierDecayAlt.P.JCx1.contDiff_Dmin Bs.z Bs.z' _
  have hbD : ContDiff ℝ (⊤ : ℕ∞) (fun g : B.Mat P.k P.r => b (Dmin P.k P.r Bs.z Bs.z' g ⟨i, by omega⟩)) :=
    b.contDiff.comp hD
  have hne : ∀ g, cutW Bs b F i hi w e g ≠ 0 → D.uwG P.k P.r Bs.z Bs.z' F i hi w e g ≠ 0 := by
    intro g hg h0
    apply hg
    simp [cutW, h0]
  refine ⟨cutW Bs b F i hi w e, ⟨?_, ⟨R, fun g hg h1 => Formalism.FourierDecayAlt.P.PBG.uwG_supp Bs.z Bs.z' F R hR i hi w e g hg
      (hne g h1)⟩, ε, hε, fun g hg h1 => uwG_zero_of_G Bs.z Bs.z' F ε hεG i hi w e g hg (hne g h1)⟩, ?_⟩
  · intro g₀ hg₀
    by_cases h0 : Dmin P.k P.r Bs.z Bs.z' g₀ ⟨i, by omega⟩ = 0
    · refine ⟨{g | ‖Dmin P.k P.r Bs.z Bs.z' g ⟨i, by omega⟩‖ < ‖a‖ / 2}, fun _ => 0,
        isOpen_lt (continuous_norm.comp hD.continuous) continuous_const, by simp [h0]; positivity,
        contDiffOn_const, fun g hg _ => ?_⟩
      have hb0 : b (Dmin P.k P.r Bs.z Bs.z' g ⟨i, by omega⟩) = 0 := by
        apply Function.notMem_support.1
        rw [b.support_eq, Metric.mem_ball, dist_eq_norm]
        intro hlt
        have h1 : ‖a‖ ≤ ‖Dmin P.k P.r Bs.z Bs.z' g ⟨i, by omega⟩ - a‖ + ‖Dmin P.k P.r Bs.z Bs.z' g ⟨i, by omega⟩‖ := by
          have := norm_sub_le (Dmin P.k P.r Bs.z Bs.z' g ⟨i, by omega⟩) (Dmin P.k P.r Bs.z Bs.z' g ⟨i, by omega⟩ - a)
          simp at this
          linarith
        have h2 : b.rOut = ‖a‖ / 2 := rfl
        have h3 : ‖Dmin P.k P.r Bs.z Bs.z' g ⟨i, by omega⟩‖ < ‖a‖ / 2 := hg
        linarith
      simp [cutW, hb0]
    · obtain ⟨U, f', hU, hgU, hf', hE⟩ :=
        Formalism.FourierDecayAlt.P.PBG.uwG_mem Bs.z Bs.z' i hi hck w e g₀ h0 hg₀
      refine ⟨U, fun g => b (Dmin P.k P.r Bs.z Bs.z' g ⟨i, by omega⟩) • f' g, hU, hgU,
        (hbD.contDiffOn.of_le le_rfl).smul hf', fun g hg hgG => ?_⟩
      simp only [cutW]
      rw [hE g hg hgG]
  · intro g hg
    simp only [cutW]
    rw [hg, b.one_of_mem_closedBall (Metric.mem_closedBall_self b.rIn_pos.le), one_smul]

end proofs

theorem truncation_off_exists_formula : CutOffExists := by
  intro Wp Wq _ _ _ _ _ _ P p F j hj w h hh hF t ht e
  have ht0 : t ≠ 0 := (ht.1 (1, t) (List.mem_append_right _ (List.mem_singleton_self _))).2
  have hH : (U.hMat (D.ptPerm h) (D.ptDiag h)).det ≠ 0 := by
    rw [Formalism.FourierDecayAlt.P.PBI.det_hMat_pt, hh.2]
    exact Formalism.FourierDecayAlt.P.PBI.det_ptMatN_ne h j hh
  exact cutW_exists p.T.base F hF (j + 1) hj w e _ (mul_ne_zero hH ht0)

theorem truncation_off_induction : CutOffStep := by
  intro Wp Wq _ _ _ _ _ _ P p F j hj w h hh γ hγ hΩ t ht e Fc hFc hag
  have hs : KB.slv p.T F (j + 1) hj w (h ++ [(1, t)]) ht.2 e =
      KB.slv p.T Fc (j + 1) hj [] (h ++ [(1, t)]) ht.2 (fun a => a.elim0) := by
    unfold KB.slv
    congr 1
    apply Formalism.FourierDecayAlt.P.PBI.sliceAt_congr_Dr _ _ _ (by rw [ht.2]; exact hj)
    intro x hx
    symm
    show Fc x = _
    apply hag
    have e1 : (⟨j + 1, by omega⟩ : Fin (P.r + 2)) = ⟨D.ptSize (h ++ [(1, t)]), by rw [ht.2]; omega⟩ :=
      Fin.ext ht.2.symm
    rw [e1, hx, det_hMat_app]
  rw [hs, Formalism.FourierDecayAlt.P.slice_induction_level Wp Wq P p Fc j hj h t hh ht hFc γ hγ hΩ]
  rfl

end Formalism.FourierDecayAlt.P.CutHB
