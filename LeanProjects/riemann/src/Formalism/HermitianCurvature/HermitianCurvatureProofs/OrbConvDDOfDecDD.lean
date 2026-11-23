import Formalism.HermitianCurvature.HermitianCurvatureProofs.CkOnZeroOfContOn

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace

namespace Formalism.FourierDecayAlt.P.S3dx4

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData

theorem ag_nonneg (k r : ℕ) : 0 ≤ AG k r := by unfold AG; positivity

theorem gap4 {k r : ℕ} {h : ℝ} (hG : GapOK k r h) :
    9 * ((r : ℝ) + 1) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 + 3 * AG k r + 3 ≤ aOf r h := hG.2.2.2

theorem thr_of_gapOK {k r : ℕ} {h : ℝ} (hG : GapOK k r h) : JF.TransportedAlt k r (aOf r h) 0 := by
  have h4' := gap4 hG
  have h4 : 9 * ((r : ℝ) + 1) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 < aOf r h := by
    linarith [ag_nonneg k r]
  unfold JF.TransportedAlt
  have hpos : (0 : ℝ) < 9 * ((r : ℝ) + 1) := by positivity
  rw [Nat.cast_zero, mul_zero, sub_zero, lt_div_iff₀ hpos]
  calc ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 * (9 * ((r : ℝ) + 1))
      = 9 * ((r : ℝ) + 1) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 := by ring
    _ < aOf r h := h4

theorem aOf_pos_of_gapOK {k r : ℕ} {h : ℝ} (hG : GapOK k r h) : 0 < aOf r h := by
  have h4 := gap4 hG
  have h5 := ag_nonneg k r
  have : (0 : ℝ) ≤ 9 * ((r : ℝ) + 1) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 := by positivity
  linarith

theorem rho_triv {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (p : B.SS k r)
    (F : B.Mat k r → (ℂ →L[ℂ] ℂ)) (g : B.Mat k r) : B.rho (triv D) p F g = F (B.sgs p g) := by
  ext
  simp [B.rho, triv]

theorem rpow_bound (t C a : ℝ) (ht : 0 ≤ t) (ha : a ≠ 0) : t ^ a * (C * t ^ (-a)) ≤ |C| := by
  rcases ht.lt_or_eq with h | h
  · rw [mul_left_comm, ← Real.rpow_add h, add_neg_cancel, Real.rpow_zero, mul_one]
    exact le_abs_self C
  · subst h
    rw [Real.zero_rpow ha, zero_mul]
    exact abs_nonneg C

theorem orbConvDD_of_decDD (hD : DecDD) : OrbConvDD := by
  intro hIn k r Wp Wq _ _ _ _ _ _ _ _ D ε lam h H _ _ _ σ w0 u u' νq νq' hS hS' x hx y hy
  obtain ⟨C, hC⟩ :=
    hD hIn k r ε lam h H σ w0 Wp D.z Formalism.QuantumDeterminants.cStd u D.π D.μW D.μN D.μG νq hS y hy x hx
  have hG : GapOK k r h := hS.2.2.2.1
  have hσ : PI.UpqRep.IsDSHpk k r ε lam σ := hS.2.1
  have hThr : JF.TransportedAlt k r (aOf r h) 0 := thr_of_gapOK hG
  have ha : aOf r h ≠ 0 := (aOf_pos_of_gapOK hG).ne'
  let f : Mx k r → ℂ := fun g => ⟪x, σ g y⟫_ℂ
  have hfc : ContinuousOn f (B.GV k r) :=
    ContinuousOn.inner continuousOn_const (sigma_contOn hσ y)
  let F : B.Mat k r → (ℂ →L[ℂ] ℂ) := fun g => f g • (1 : ℂ →L[ℂ] ℂ)
  have hCC : B.InCC (aOf r h) 0 F := by
    refine ⟨|C|, ckOn_zero_of_contOn f hfc, ?_⟩
    intro uu vv _ _ hlen g hg
    have hu : uu = [] := List.eq_nil_of_length_eq_zero (by omega)
    have hv : vv = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hu; subst hv
    show B.gN g ^ aOf r h * ‖F g‖ ≤ |C|
    have hF : ‖F g‖ = ‖f g‖ := by simp [F]
    rw [hF]
    have hgN : 0 ≤ B.gN g := Real.sqrt_nonneg _
    calc B.gN g ^ aOf r h * ‖f g‖ ≤ B.gN g ^ aOf r h * (C * B.gN g ^ (-aOf r h)) :=
          mul_le_mul_of_nonneg_left (hC g hg) (Real.rpow_nonneg hgN _)
      _ ≤ |C| := rpow_bound _ _ _ hgN ha
  have hJC := Formalism.FourierDecayAlt.P.bessel_integral_converges k r ℂ ℂ (triv D) (aOf r h) F hThr hCC
  have hJD := Formalism.FourierDecayAlt.P.bessel_integral_domain k r ℂ ℂ (triv D) (aOf r h) 0 F hThr hCC
  have hnorm : ∀ p γ, ‖⟪x, σ (B.sgs p γ) y⟫_ℂ‖ = ‖B.rho (triv D) p F γ‖ := by
    intro p γ
    rw [rho_triv]
    simp [F, f]
  have happ : ∀ p γ, ⟪x, σ (B.sgs p γ) y⟫_ℂ = (ContinuousLinearMap.apply ℂ ℂ (1 : ℂ)) (B.rho (triv D) p F γ) := by
    intro p γ
    rw [rho_triv]
    simp [F, f]
  refine ⟨fun γ hγ => ?_, fun K hK hKO => ?_⟩
  · obtain ⟨b, hb, hbd⟩ := hJC.2 {γ} isCompact_singleton (Set.singleton_subset_iff.mpr hγ)
    have hmeas : AEStronglyMeasurable (fun p => B.rho (triv D) p F γ) D.μSS :=
      hJD.1 [] [] (by simp) (by simp) (by simp) γ hγ
    have hmeas' : AEStronglyMeasurable (fun p => ⟪x, σ (B.sgs p γ) y⟫_ℂ) D.μSS := by
      have := (ContinuousLinearMap.apply ℂ ℂ (1 : ℂ)).continuous.comp_aestronglyMeasurable hmeas
      refine this.congr (Filter.Eventually.of_forall fun p => ?_)
      exact (happ p γ).symm
    refine Integrable.mono' hb hmeas' ?_
    filter_upwards [hbd γ rfl] with p hp
    rw [hnorm]
    exact hp
  · obtain ⟨b, hb, hbd⟩ := hJC.2 K hK hKO
    refine ⟨b, hb, fun γ hγ => ?_⟩
    filter_upwards [hbd γ hγ] with p hp
    rw [hnorm]
    exact hp

end Formalism.FourierDecayAlt.P.S3dx4
