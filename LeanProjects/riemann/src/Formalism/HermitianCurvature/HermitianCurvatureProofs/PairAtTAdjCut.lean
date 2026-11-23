import Formalism.HermitianCurvature.HermitianCurvatureProofs.ExistsFderivChiBound
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormalFormOrderZeroOfParts

open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate InnerProductSpace ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P5.HerB

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.HerA

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section Core

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp]
  [FiniteDimensional ℂ Wq] {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

theorem pairAt_cut_core (μ : Measure (Mt k r)) (Φ Ψ : RadSp k r z z' π π') (c : Fin r → ℂ)
    (A A' Bo B' : Module.End ℂ (RadSp k r z z' π π')) (W : ℕ → Module.End ℂ (RadSp k r z z' π π'))
    (hW : ∀ n, NF.IsMulZ (W n) (chin n)) (d d' : ℕ → ℂ → ℂ) (M : ℝ)
    (hdc : ∀ n, Continuous (d n)) (hd'c : ∀ n, Continuous (d' n))
    (hd : ∀ n w, ‖d n w‖ ≤ M) (hd' : ∀ n w, ‖d' n w‖ ≤ M)
    (hdl : ∀ w, ∀ᶠ n in atTop, d n w = 0 ∧ d' n w = 0)
    (hA : ∀ n g, (A (W n Φ) : Fn k r (Wq →L[ℂ] Wp)) c g =
      chin n (zetaL k r z z' (Fin.last r) g) • (A Φ : Fn k r (Wq →L[ℂ] Wp)) c g +
        d n (zetaL k r z z' (Fin.last r) g) • (Bo Φ : Fn k r (Wq →L[ℂ] Wp)) c g)
    (hA' : ∀ n g, (A' (W n Ψ) : Fn k r (Wq →L[ℂ] Wp)) c g =
      chin n (zetaL k r z z' (Fin.last r) g) • (A' Ψ : Fn k r (Wq →L[ℂ] Wp)) c g +
        d' n (zetaL k r z z' (Fin.last r) g) • (B' Ψ : Fn k r (Wq →L[ℂ] Wp)) c g)
    (h1 : Integrable (fun x : Mt k r => B.hsInner ((A Φ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of x))
      ((Ψ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of x))) μ)
    (h2 : Integrable (fun x : Mt k r => B.hsInner ((Φ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of x))
      ((A' Ψ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of x))) μ)
    (h3 : Integrable (fun x : Mt k r => B.hsInner ((Bo Φ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of x))
      ((Ψ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of x))) μ)
    (h4 : Integrable (fun x : Mt k r => B.hsInner ((Φ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of x))
      ((B' Ψ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of x))) μ)
    (hcpt : ∀ n, pairAt μ (A (W n Φ)) (W n Ψ) c = pairAt μ (W n Φ) (A' (W n Ψ)) c) :
    pairAt μ (A Φ) Ψ c = pairAt μ Φ (A' Ψ) c := by
  have hζ : Continuous (fun x : Mt k r => zetaL k r z z' (Fin.last r) (Matrix.of x)) :=
    (Formalism.FourierDecayAlt.P.Qx5.zetaL_contDiff k r z z' (Fin.last r)).continuous.comp
      (continuous_snd.comp (cslice_continuous c))
  unfold pairAt
  refine pair_lim (μ := μ) (fun x => (Φ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of x))
    (fun x => (Ψ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of x)) (fun x => (A Φ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of x))
    (fun x => (Bo Φ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of x))
    (fun x => (A' Ψ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of x))
    (fun x => (B' Ψ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of x))
    (fun n x => chin n (zetaL k r z z' (Fin.last r) (Matrix.of x)))
    (fun n x => d n (zetaL k r z z' (Fin.last r) (Matrix.of x)))
    (fun n x => d' n (zetaL k r z z' (Fin.last r) (Matrix.of x))) M
    (fun n => ((chin_contDiff n).continuous.comp hζ).aestronglyMeasurable)
    (fun n => ((hdc n).comp hζ).aestronglyMeasurable) (fun n => ((hd'c n).comp hζ).aestronglyMeasurable)
    (fun n x => norm_chin_le n _) (fun n x => hd n _) (fun n x => hd' n _) (fun x => ?_) h1 h2 h3 h4 (fun n => ?_)
  · filter_upwards [eventually_lt (zetaL k r z z' (Fin.last r) (Matrix.of x)),
      hdl (zetaL k r z z' (Fin.last r) (Matrix.of x))] with n hn hn'
    exact ⟨(chin_eventually_one n _ hn).eq_of_nhds, hn'.1, hn'.2⟩
  · have h := hcpt n
    unfold pairAt at h
    simp only [hA, hA', Formalism.FourierDecayAlt.P.NFx4.mulZ_apply (hW n)] at h
    exact h

end Core

section Top

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem pairAt_t_adj_cut (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (hP : IsPlace P z z' π π') (X : ActualOps P.k P.r z z' π π')
    (μ : Measure (Mt P.k P.r)) (hμ : B.IsHaarOn (Glev P.k P.r (Fin.last P.r)) μ)
    (Φ Ψ : RadSp P.k P.r z z' π π') (c : Fin P.r → ℂ) (hc : c ∈ OmX P.r) (ε : ℝ) (hε : 0 < ε)
    (hΦ0 : ∀ g ∈ Glev P.k P.r (Fin.last P.r), GGl P.k P.r z z' g < ε → (Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) c g = 0)
    (hΨ0 : ∀ g ∈ Glev P.k P.r (Fin.last P.r), GGl P.k P.r z z' g < ε → (Ψ : Fn P.k P.r (Wq →L[ℂ] Wp)) c g = 0)
    (Y : ℂ) (a b : Fin 2) (hab : a ≠ 0 ∨ b ≠ 0)
    (h1 : Integrable (fun x : Mt P.k P.r => B.hsInner ((X.t Y a b Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) c (Matrix.of x))
      ((Ψ : Fn P.k P.r (Wq →L[ℂ] Wp)) c (Matrix.of x))) μ)
    (h2 : Integrable (fun x : Mt P.k P.r => B.hsInner ((Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) c (Matrix.of x))
      ((X.t (star Y) b a Ψ : Fn P.k P.r (Wq →L[ℂ] Wp)) c (Matrix.of x))) μ)
    (h3 : Integrable (fun x : Mt P.k P.r => B.hsInner ((X.t Y 1 1 Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) c (Matrix.of x))
      ((Ψ : Fn P.k P.r (Wq →L[ℂ] Wp)) c (Matrix.of x))) μ)
    (h4 : Integrable (fun x : Mt P.k P.r => B.hsInner ((Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) c (Matrix.of x))
      ((X.t (star Y) 1 1 Ψ : Fn P.k P.r (Wq →L[ℂ] Wp)) c (Matrix.of x))) μ) :
    pairAt μ (X.t Y a b Φ) Ψ c = pairAt μ Φ (X.t (star Y) b a Ψ) c := by
  have hP0 := hP
  obtain ⟨hOK, hz, hz', hTz, hTz', -, -⟩ := hP
  have hT : 0 < Tz P.k P.r z := hTz ▸ hOK.T_pos
  have hT' : 0 < Tz P.k P.r z' := hTz' ▸ hOK.T'_pos
  obtain ⟨C, hC⟩ := exists_fderiv_chi_bound
  have hCd : ∀ n w, ‖NF.dZ (chin n) w‖ ≤ C := fun n w => (norm_dZ_le _ w).trans (norm_fderiv_chin_le hC n w)
  have hCdb : ∀ n w, ‖NF.dZb (chin n) w‖ ≤ C := fun n w => (norm_dZb_le _ w).trans (norm_fderiv_chin_le hC n w)
  let W : ℕ → Module.End ℂ (RadSp P.k P.r z z' π π') := fun n =>
    Formalism.FourierDecayAlt.P.NFx4.mulZEnd (π := π) (π' := π') ((chin_contDiff n).contDiffOn)
  let W1 : ℕ → Module.End ℂ (RadSp P.k P.r z z' π π') := fun n =>
    Formalism.FourierDecayAlt.P.NFx4.mulZEnd (π := π) (π' := π') ((dZ_contDiff (chin_contDiff n)).contDiffOn)
  let W2 : ℕ → Module.End ℂ (RadSp P.k P.r z z' π π') := fun n =>
    Formalism.FourierDecayAlt.P.NFx4.mulZEnd (π := π) (π' := π') ((dZb_contDiff (chin_contDiff n)).contDiffOn)
  have hW : ∀ n, NF.IsMulZ (W n) (chin n) := fun n => Formalism.FourierDecayAlt.P.NFx4.isMulZ_mulZEnd _
  have hW1 : ∀ n, NF.IsMulZ (W1 n) (NF.dZ (chin n)) := fun n => Formalism.FourierDecayAlt.P.NFx4.isMulZ_mulZEnd _
  have hW2 : ∀ n, NF.IsMulZ (W2 n) (NF.dZb (chin n)) := fun n => Formalism.FourierDecayAlt.P.NFx4.isMulZ_mulZEnd _
  have hAZ := fun n (Y' : ℂ) => Formalism.FourierDecayAlt.P.actual_zeta_smooth_alt Wp Wq P z z' π π'
    hP0 X (chin n) ((chin_contDiff n).contDiffOn)
    (W n) (W1 n) (W2 n) (hW n) (hW1 n) (hW2 n) Y'
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  have hK : ∀ n : ℕ, ∃ K : Set (Mx P.k P.r), IsCompact K ∧ K ⊆ {g | 0 < GGl P.k P.r z z' g} ∧
      ∀ g ∈ Glev P.k P.r (Fin.last P.r), g ∉ K →
        (W n Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) c g = 0 ∧ (W n Ψ : Fn P.k P.r (Wq →L[ℂ] Wp)) c g = 0 := by
    intro n
    refine ⟨_, isCompact_zeta_le z z' hz hz' hT hT' ε (2 * ((n : ℝ) + 1)),
      fun g hg => lt_of_lt_of_le hε hg.2.1, fun g hg hgK => ?_⟩
    rw [Formalism.FourierDecayAlt.P.NFx4.mulZ_apply (hW n), Formalism.FourierDecayAlt.P.NFx4.mulZ_apply (hW n)]
    by_cases hG : ε ≤ GGl P.k P.r z z' g
    · have hζ : 2 * ((n : ℝ) + 1) ≤ ‖zetaL P.k P.r z z' (Fin.last P.r) g‖ := by
        by_contra h
        push_neg at h
        exact hgK ⟨hg, hG, h.le⟩
      simp only [chin_zero n _ hζ, zero_smul, and_self]
    · push_neg at hG
      simp only [hΦ0 g hg hG, hΨ0 g hg hG, smul_zero, and_self]
  have hcpt : ∀ (a' b' : Fin 2) (n : ℕ), pairAt μ (X.t Y a' b' (W n Φ)) (W n Ψ) c =
      pairAt μ (W n Φ) (X.t (star Y) b' a' (W n Ψ)) c := fun a' b' n => by
    obtain ⟨K, hKc, hKG, hK0⟩ := hK n
    exact pairAt_t_adj_cpt' P z z' π π' hP0 X μ hμ (W n Φ) (W n Ψ) c hc ⟨K, hKc, hKG, hK0⟩ Y a' b'
  have ParameterUpperBound : ∀ (Y' : ℂ) (Θ : RadSp P.k P.r z z' π π') (n : ℕ) (g : Mx P.k P.r),
      (X.t Y' 1 0 (W n Θ) : Fn P.k P.r (Wq →L[ℂ] Wp)) c g =
        chin n (zetaL P.k P.r z z' (Fin.last P.r) g) • (X.t Y' 1 0 Θ : Fn P.k P.r (Wq →L[ℂ] Wp)) c g +
          (-NF.dZ (chin n) (zetaL P.k P.r z z' (Fin.last P.r) g)) •
            (X.t Y' 1 1 Θ : Fn P.k P.r (Wq →L[ℂ] Wp)) c g := by
    intro Y' Θ n g
    have e := congrArg (fun T : Module.End ℂ (RadSp P.k P.r z z' π π') =>
      ((T Θ : RadSp P.k P.r z z' π π') : Fn P.k P.r (Wq →L[ℂ] Wp)) c g) (hAZ n Y').1
    simp only [Module.End.mul_apply, LinearMap.sub_apply, Submodule.coe_sub, Pi.sub_apply,
      Formalism.FourierDecayAlt.P.NFx4.mulZ_apply (hW n), Formalism.FourierDecayAlt.P.NFx4.mulZ_apply (hW1 n)] at e
    rw [e, neg_smul, sub_eq_add_neg]
  have liftZP_unit : ∀ (Y' : ℂ) (Θ : RadSp P.k P.r z z' π π') (n : ℕ) (g : Mx P.k P.r),
      (X.t Y' 1 1 (W n Θ) : Fn P.k P.r (Wq →L[ℂ] Wp)) c g =
        chin n (zetaL P.k P.r z z' (Fin.last P.r) g) • (X.t Y' 1 1 Θ : Fn P.k P.r (Wq →L[ℂ] Wp)) c g +
          (0 : ℂ) • (X.t Y' 1 1 Θ : Fn P.k P.r (Wq →L[ℂ] Wp)) c g := by
    intro Y' Θ n g
    have e := congrArg (fun T : Module.End ℂ (RadSp P.k P.r z z' π π') =>
      ((T Θ : RadSp P.k P.r z z' π π') : Fn P.k P.r (Wq →L[ℂ] Wp)) c g) (hAZ n Y').2.1
    simp only [Module.End.mul_apply, Formalism.FourierDecayAlt.P.NFx4.mulZ_apply (hW n)] at e
    rw [e, zero_smul, add_zero]
  have L01 : ∀ (Y' : ℂ) (Θ : RadSp P.k P.r z z' π π') (n : ℕ) (g : Mx P.k P.r),
      (X.t Y' 0 1 (W n Θ) : Fn P.k P.r (Wq →L[ℂ] Wp)) c g =
        chin n (zetaL P.k P.r z z' (Fin.last P.r) g) • (X.t Y' 0 1 Θ : Fn P.k P.r (Wq →L[ℂ] Wp)) c g +
          NF.dZb (chin n) (zetaL P.k P.r z z' (Fin.last P.r) g) •
            (X.t Y' 1 1 Θ : Fn P.k P.r (Wq →L[ℂ] Wp)) c g := by
    intro Y' Θ n g
    have e := congrArg (fun T : Module.End ℂ (RadSp P.k P.r z z' π π') =>
      ((T Θ : RadSp P.k P.r z z' π π') : Fn P.k P.r (Wq →L[ℂ] Wp)) c g) (hAZ n Y').2.2
    simp only [Module.End.mul_apply, LinearMap.add_apply, Submodule.coe_add, Pi.add_apply,
      Formalism.FourierDecayAlt.P.NFx4.mulZ_apply (hW n), Formalism.FourierDecayAlt.P.NFx4.mulZ_apply (hW2 n)] at e
    rw [e]
  have hdl : ∀ w : ℂ, ∀ᶠ n : ℕ in atTop, -NF.dZ (chin n) w = 0 ∧ NF.dZb (chin n) w = 0 := fun w => by
    filter_upwards [eventually_lt w] with n hn
    exact ⟨by rw [dZ_chin_zero n w hn, neg_zero], dZb_chin_zero n w hn⟩
  have hcases : ∀ a b : Fin 2, a ≠ 0 ∨ b ≠ 0 → (a = 1 ∧ b = 0) ∨ (a = 1 ∧ b = 1) ∨ (a = 0 ∧ b = 1) := by decide
  rcases hcases a b hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact pairAt_cut_core μ Φ Ψ c (X.t Y 1 0) (X.t (star Y) 0 1) (X.t Y 1 1) (X.t (star Y) 1 1) W hW
      (fun n w => -NF.dZ (chin n) w) (fun n w => NF.dZb (chin n) w) C
      (fun n => (dZ_contDiff (chin_contDiff n)).continuous.neg) (fun n => (dZb_contDiff (chin_contDiff n)).continuous)
      (fun n w => by rw [norm_neg]; exact hCd n w) hCdb hdl (fun n g => ParameterUpperBound Y Φ n g) (fun n g => L01 (star Y) Ψ n g)
      h1 h2 h3 h4 (hcpt 1 0)
  · exact pairAt_cut_core μ Φ Ψ c (X.t Y 1 1) (X.t (star Y) 1 1) (X.t Y 1 1) (X.t (star Y) 1 1) W hW
      (fun _ _ => 0) (fun _ _ => 0) C (fun _ => continuous_const) (fun _ => continuous_const)
      (fun _ _ => by rw [norm_zero]; exact hC0) (fun _ _ => by rw [norm_zero]; exact hC0)
      (fun _ => Eventually.of_forall fun _ => ⟨rfl, rfl⟩) (fun n g => liftZP_unit Y Φ n g) (fun n g => liftZP_unit (star Y) Ψ n g)
      h1 h2 h3 h4 (hcpt 1 1)
  · exact pairAt_cut_core μ Φ Ψ c (X.t Y 0 1) (X.t (star Y) 1 0) (X.t Y 1 1) (X.t (star Y) 1 1) W hW
      (fun n w => NF.dZb (chin n) w) (fun n w => -NF.dZ (chin n) w) C
      (fun n => (dZb_contDiff (chin_contDiff n)).continuous) (fun n => (dZ_contDiff (chin_contDiff n)).continuous.neg)
      hCdb (fun n w => by rw [norm_neg]; exact hCd n w) (fun w => (hdl w).mono fun n hn => ⟨hn.2, hn.1⟩)
      (fun n g => L01 Y Φ n g) (fun n g => ParameterUpperBound (star Y) Ψ n g) h1 h2 h3 h4 (hcpt 0 1)

end Top

end Formalism.FourierDecayAlt.P5.HerB
