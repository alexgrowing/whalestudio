import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGermParts
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelFormsJointContinuity

namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory
open scoped ComplexConjugate ENNReal

noncomputable section

def RRBelowCpt : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)), KB.CptCoef p.T.base F →
    ∀ (i : ℕ), i ≤ P.r → ∀ (w : List C.Letter), KB.CutWord P p.l0 w → ∀ (h h' : C.LPt) (m : ℕ), 1 ≤ m →
      D.ptSize h + m = i → D.ptSize h' + m = i →
      ContinuousOn (fun cc : ℂ × ℂ => p.RR F i w (h ++ [(m, cc.1)]) (h' ++ [(m, cc.2)]))
        (({0}ᶜ : Set ℂ) ×ˢ ({0}ᶜ : Set ℂ))

section place

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem nPt_app_cont (TT : ℝ) (h : C.LPt) (s : ℕ) :
    ContinuousOn (fun z : ℂ => TBB.nPt P.k P.r TT (h ++ [(s, z)])) {0}ᶜ := by
  have h1 := Formalism.FourierDecayAlt.P.LastBlockContinuity.continuousOn_weight_product P.k P.r (fun _ _ => 1) (fun _ _ => one_pos) s h 1
  have hmap : Set.MapsTo (fun z : ℂ => ((Complex.normSq z - TT : ℝ), z)) {0}ᶜ (Set.univ ×ˢ {0}ᶜ) :=
    fun z hz => ⟨Set.mem_univ _, hz⟩
  have h2 := h1.comp (Continuous.continuousOn (by fun_prop)) hmap
  refine h2.congr fun z _ => ?_
  simp only [Function.comp, TBB.nPt]
  congr 1
  simp [D.ptGG, D.ptLast]

theorem diag_cont {f : ℂ × ℂ → ℂ} (hf : ContinuousOn f (({0}ᶜ : Set ℂ) ×ˢ ({0}ᶜ : Set ℂ))) :
    ContinuousOn (fun z : ℂ => f (z, z)) {0}ᶜ :=
  hf.comp (Continuous.continuousOn (by fun_prop)) fun _ hz => ⟨hz, hz⟩

theorem ew_cont_of_rr (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (i : ℕ)
    (w : List C.Letter) (h : C.LPt) (s : ℕ)
    (hRR : ContinuousOn (fun cc : ℂ × ℂ => p.RR F i w (h ++ [(s, cc.1)]) (h ++ [(s, cc.2)]))
      (({0}ᶜ : Set ℂ) ×ˢ ({0}ᶜ : Set ℂ))) :
    ContinuousOn (fun z : ℂ => TBB.Ew p nn F i w (h ++ [(s, z)])) {0}ᶜ := by
  have hn := nPt_app_cont (P := P) (TBB.TTp p) h s
  have hw : ContinuousOn (fun z : ℂ => ((Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) (h ++ [(s, z)])) *
      Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) (h ++ [(s, z)])) / TBB.normC nn w : ℝ) : ℂ)) {0}ᶜ :=
    Complex.continuous_ofReal.comp_continuousOn
      (((Real.continuous_sqrt.comp_continuousOn hn).mul (Real.continuous_sqrt.comp_continuousOn hn)).div_const _)
  have hr := diag_cont hRR
  exact Complex.continuous_re.comp_continuousOn (hw.mul hr)

end place

theorem germContAll_of (hR : RRBelowCpt) : GermContAll := by
  intro Wp Wq _ _ _ _ _ _ P p nn F Y K N Cb hCb hF _ b s hb hs hbs h hh w hw _
  have hsz : D.ptSize h + s = b + s - 1 := by rw [hh.2]; omega
  refine ew_cont_of_rr p nn F (b + s - 1) w h s ?_
  rcases Nat.lt_or_ge (b + s - 1) (P.r + 1) with hlt | hge
  · exact hR Wp Wq P p F hF (b + s - 1) (by omega) w hw.1 h h s (by omega) hsz hsz
  · have he : b + s - 1 = P.r + 1 := by omega
    rw [he] at hsz ⊢
    exact Formalism.FourierDecayAlt.P.LastBlockContinuity.rrTop_cont P p F hF Cb hCb w hw.1 h h s (by omega) hsz hsz

end

end Formalism.FourierDecayAlt.P.CutBP
