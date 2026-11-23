import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFTopForm
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutLemB
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutDomCutInt
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TriangleInequalityAtPlace
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DensityConstantOfParts

namespace Formalism.FourierDecayAlt.P.CutBP.TDM

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory

noncomputable section

def TypeNormMeas : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (Y : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (A : ℝ), JF.TransportedAlt P.k P.r A 0 → B.InCC A 0 Y → ∀ ρ : M.Ty P,
      AEStronglyMeasurable (fun c : Fin (P.r + 1) → ℂ =>
        ‖B.hsVec ((p.TP.E ρ).comp (p.V Y (TBB.bigPt P.r c)))‖) volume

def VecVGPos : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (Y Y' : B.Mat P.k P.r → (Wq →L[ℂ] Wp)),
    (∀ g ∈ B.GV P.k P.r, 0 < Gf P.k P.r p.T.base.z p.T.base.z' g → Y g = Y' g) → ∀ a : C.LPt, p.V Y a = p.V Y' a

def DopCC : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (X : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter) (Cb : ℝ),
    KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → KB.CptCoef p.T.base X → KB.CutWord P p.l0 w →
    ∀ e : Wd.Ix (Fin w.length), ∃ Y : B.Mat P.k P.r → (Wq →L[ℂ] Wp),
      (∀ g ∈ B.GV P.k P.r, 0 < Gf P.k P.r p.T.base.z p.T.base.z' g → Y g = p.Θ.Θ w e X g) ∧
        ∀ A : ℝ, B.InCC A 0 Y

def ScalarMeas : Prop :=
  ∀ (k r : ℕ) (TT : ℝ), Measurable (fun c : Fin (r + 1) → ℂ => TBB.nPt k r TT (TBB.bigPt r c)) ∧
    Measurable (fun c : Fin (r + 1) → ℂ => Top.wPt TT r (TBB.bigPt r c))

def EmptyMeas : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (X : B.Mat P.k P.r → (Wq →L[ℂ] Wp)), KB.CptCoef p.T.base X → AEStronglyMeasurable (topD p X []) volume

theorem ae_all_ne (r : ℕ) : ∀ᵐ c : Fin (r + 1) → ℂ, ∀ i, c i ≠ 0 := by
  rw [ae_all_iff]
  intro i
  have h : volume ((fun c : Fin (r + 1) → ℂ => c i) ⁻¹' {0}) = 0 := by
    rw [volume_pi]
    exact Measure.pi_eval_preimage_null _ (measure_singleton 0)
  have e : {a : Fin (r + 1) → ℂ | ¬a i ≠ 0} = (fun c : Fin (r + 1) → ℂ => c i) ⁻¹' {0} := by
    ext a; simp
  exact ae_iff.2 (by rw [e]; exact h)

theorem topDMeasCpt_of_parts (h1 : TypeNormMeas) (h2 : VecVGPos) (h3 : DopCC) (h4 : ScalarMeas) (h5 : EmptyMeas) :
    TopDMeasCpt := by
  intro Wp Wq _ _ _ _ _ _ P p X w Cb hD hX hw
  by_cases hw0 : w = []
  · subst hw0; exact h5 Wp Wq P p X hX
  choose Y hYe hYc using h3 Wp Wq P p X w Cb hD hX hw
  set TT : ℝ := Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z' with hTT
  set A : ℝ := 9 * ((P.r : ℝ) + 1) * (((2 * P.r + P.k + 1 : ℕ) : ℝ) ^ 2 + 1) with hA
  have hThr : JF.TransportedAlt P.k P.r A 0 := by
    unfold JF.TransportedAlt
    have hr : (0 : ℝ) < 9 * ((P.r : ℝ) + 1) := by positivity
    rw [Nat.cast_zero, mul_zero, sub_zero, lt_div_iff₀ hr, hA]
    nlinarith
  have hV : ∀ e a, p.V (p.Θ.Θ w e X) a = p.V (Y e) a := fun e a =>
    h2 Wp Wq P p _ _ (fun g hg hG => (hYe e g hg hG).symm) a
  obtain ⟨hn, hW⟩ := h4 P.k P.r TT
  set g : (Fin (P.r + 1) → ℂ) → ℝ := fun c =>
    ((((Real.sqrt (TBB.nPt P.k P.r TT (TBB.bigPt P.r c)) * Real.sqrt (TBB.nPt P.k P.r TT (TBB.bigPt P.r c)) /
        TBB.normC (fun _ => 1) w : ℝ) : ℂ) *
      ∑ e : Wd.Ix (Fin w.length), ∑ ρ : M.Ty P,
        ((Top.dH P p.l0 TT w (TBB.bigPt P.r c) e ρ * Top.dH P p.l0 TT w (TBB.bigPt P.r c) e ρ : ℝ) : ℂ) *
          (((‖B.hsVec ((p.TP.E ρ).comp (p.V (Y e) (TBB.bigPt P.r c)))‖ ^ 2 : ℝ)) : ℂ))).re with hg
  have hgm : AEStronglyMeasurable g volume := by
    have hdH : ∀ e ρ, Measurable (fun c : Fin (P.r + 1) → ℂ => Top.dH P p.l0 TT w (TBB.bigPt P.r c) e ρ) := by
      intro e ρ
      unfold Top.dH
      exact ((hW.pow_const _).mul_const _).sqrt
    have hterm : ∀ e ρ, AEStronglyMeasurable (fun c : Fin (P.r + 1) → ℂ =>
        ((Top.dH P p.l0 TT w (TBB.bigPt P.r c) e ρ * Top.dH P p.l0 TT w (TBB.bigPt P.r c) e ρ : ℝ) : ℂ) *
          (((‖B.hsVec ((p.TP.E ρ).comp (p.V (Y e) (TBB.bigPt P.r c)))‖ ^ 2 : ℝ)) : ℂ)) volume := by
      intro e ρ
      have h1' : AEStronglyMeasurable (fun c : Fin (P.r + 1) → ℂ =>
          ‖B.hsVec ((p.TP.E ρ).comp (p.V (Y e) (TBB.bigPt P.r c)))‖ ^ 2) volume :=
        (h1 Wp Wq P p (Y e) A hThr (hYc e A) ρ).pow 2
      have h2' : AEStronglyMeasurable (fun c : Fin (P.r + 1) → ℂ =>
          (((‖B.hsVec ((p.TP.E ρ).comp (p.V (Y e) (TBB.bigPt P.r c)))‖ ^ 2 : ℝ)) : ℂ)) volume :=
        Complex.continuous_ofReal.comp_aestronglyMeasurable h1'
      have h3' : AEStronglyMeasurable (fun c : Fin (P.r + 1) → ℂ =>
          ((Top.dH P p.l0 TT w (TBB.bigPt P.r c) e ρ * Top.dH P p.l0 TT w (TBB.bigPt P.r c) e ρ : ℝ) : ℂ)) volume :=
        (Complex.measurable_ofReal.comp ((hdH e ρ).mul (hdH e ρ))).aestronglyMeasurable
      exact h3'.mul h2'
    have hsum : AEStronglyMeasurable (fun c : Fin (P.r + 1) → ℂ => ∑ e : Wd.Ix (Fin w.length), ∑ ρ : M.Ty P,
        ((Top.dH P p.l0 TT w (TBB.bigPt P.r c) e ρ * Top.dH P p.l0 TT w (TBB.bigPt P.r c) e ρ : ℝ) : ℂ) *
          (((‖B.hsVec ((p.TP.E ρ).comp (p.V (Y e) (TBB.bigPt P.r c)))‖ ^ 2 : ℝ)) : ℂ)) volume :=
      Finset.aestronglyMeasurable_fun_sum _ fun e _ => Finset.aestronglyMeasurable_fun_sum _ fun ρ _ => hterm e ρ
    have hpre : AEStronglyMeasurable (fun c : Fin (P.r + 1) → ℂ =>
        (((Real.sqrt (TBB.nPt P.k P.r TT (TBB.bigPt P.r c)) * Real.sqrt (TBB.nPt P.k P.r TT (TBB.bigPt P.r c)) /
          TBB.normC (fun _ => 1) w : ℝ) : ℂ))) volume :=
      (Complex.measurable_ofReal.comp (((hn.sqrt.mul hn.sqrt).div_const _))).aestronglyMeasurable
    exact Complex.continuous_re.comp_aestronglyMeasurable (hpre.mul hsum)
  refine hgm.congr ?_
  filter_upwards [ae_all_ne P.r] with c hc
  have hl : D.IsLocPt (TBB.bigPt P.r c) (P.r + 1) := Formalism.FourierDecayAlt.P.PBJ.Dens.isLocPt_bigPt c hc
  show g c = topD p X w c
  unfold topD TBB.Ew TBB.NP KB.Pl.RR D.RRplace
  rw [dif_pos ⟨hl, hl⟩, dif_neg (by omega), if_pos rfl, if_neg hw0]
  unfold Top.topOf
  simp only [hg]
  congr 3
  funext e
  refine Finset.sum_congr rfl fun ρ _ => ?_
  rw [Formalism.FourierDecayAlt.P.TBBx2.Tri.hsInner_self]
  show _ = _ * (((‖B.hsVec ((p.TP.E ρ).comp (p.V (p.Θ.Θ w e X) (TBB.bigPt P.r c)))‖ ^ 2 : ℝ)) : ℂ)
  rw [hV e]

end

end Formalism.FourierDecayAlt.P.CutBP.TDM
