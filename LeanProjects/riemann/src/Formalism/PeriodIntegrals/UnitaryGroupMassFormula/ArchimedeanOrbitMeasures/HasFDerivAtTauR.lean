import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.CayDensExHua

noncomputable section

namespace HcInf

open HcS.BasicNotions Matrix Filter Topology

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

section Deriv

variable {P Q : ℕ}

local notation "Mat" => Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ

def tauR (H X : Mat) : Mat :=
  (1 + 1) - (4 : ℂ) • (((1 + 1) - X) * Ring.inverse (H * ((1 + 1) + X) + ((1 + 1) - X)))

theorem smul_four (Z : Mat) : (4 : ℂ) • Z = (1 + 1 + 1 + 1) * Z := by
  rw [show (4 : ℂ) = 1 + 1 + 1 + 1 by norm_num, add_smul, add_smul, add_smul, one_smul, add_mul, add_mul,
    add_mul, one_mul]

theorem key_alg (H X Y Ni K : Mat)
    (hNi : Ni * (H * ((1 + 1) + X) + ((1 + 1) - X)) = 1) (hK : ((1 + 1) - X) * K = 1) :
    Y + ((1 + 1) - X) * Ni * (H * Y - Y) =
      (1 + 1 + 1 + 1) * (((1 + 1) - X) * Ni * H * K * Y) := by
  set S := (1 + 1 : Mat) - X with hS
  have hX : (1 + 1 : Mat) + X = (1 + 1 + 1 + 1) - S := by
    rw [hS]
    noncomm_ring
  have e1 : S * Ni * (H * ((1 + 1) + X) + S) * K = 1 := by
    rw [mul_assoc S Ni, hNi, mul_one, hK]
  rw [hX] at e1
  have e2 : S * Ni * (H * ((1 + 1 + 1 + 1) - S) + S) * K =
      (1 + 1 + 1 + 1) * (S * Ni * H * K) - S * Ni * H * (S * K) + S * Ni * (S * K) := by
    noncomm_ring
  rw [e2, hK, mul_one, mul_one] at e1
  have e3 : (1 + 1 + 1 + 1) * (S * Ni * H * K) = 1 + S * Ni * H - S * Ni := by
    calc (1 + 1 + 1 + 1) * (S * Ni * H * K)
        = ((1 + 1 + 1 + 1) * (S * Ni * H * K) - S * Ni * H + S * Ni) + S * Ni * H - S * Ni := by abel
      _ = 1 + S * Ni * H - S * Ni := by rw [e1]
  calc Y + S * Ni * (H * Y - Y) = (1 + S * Ni * H - S * Ni) * Y := by noncomm_ring
    _ = (1 + 1 + 1 + 1) * (S * Ni * H * K) * Y := by rw [e3]
    _ = (1 + 1 + 1 + 1) * (S * Ni * H * K * Y) := by noncomm_ring

theorem hasFDerivAt_tauR (H X : Mat) (hN : IsUnit (H * ((1 + 1) + X) + ((1 + 1) - X)).det)
    (hS : IsUnit ((1 + 1) - X).det) :
    HasFDerivAt (tauR H) (ContinuousLinearMap.mulLeftRight ℝ Mat
      ((4 : ℂ) • (((1 + 1) - X) * (H * ((1 + 1) + X) + ((1 + 1) - X))⁻¹ * H * ((1 + 1) - X)⁻¹))
      ((4 : ℂ) • (H * ((1 + 1) + X) + ((1 + 1) - X))⁻¹)) X := by
  obtain ⟨u, hu⟩ := (Matrix.isUnit_iff_isUnit_det _).2 hN
  have hA : HasFDerivAt (fun Z : Mat => (1 + 1) - Z) (-ContinuousLinearMap.id ℝ Mat) X :=
    (hasFDerivAt_id X).const_sub _
  have hB := (((hasFDerivAt_const (1 + 1 : Mat) X).add (hasFDerivAt_id X)).const_mul H).add hA
  have hI : HasFDerivAt Ring.inverse (-ContinuousLinearMap.mulLeftRight ℝ Mat ↑u⁻¹ ↑u⁻¹)
      (H * ((1 + 1) + X) + ((1 + 1) - X)) := by
    rw [← hu]; exact hasFDerivAt_ringInverse u
  have hC := hI.comp X hB
  have hD := ((hA.mul' hC).const_smul (4 : ℂ)).const_sub (1 + 1 : Mat)
  have hE : HasFDerivAt (tauR H) _ X := hD
  have hinv : (↑u⁻¹ : Mat) = (H * ((1 + 1) + X) + ((1 + 1) - X))⁻¹ := by
    rw [Matrix.nonsing_inv_eq_ringInverse, ← hu, Ring.inverse_unit]
  refine hE.congr_fderiv (ContinuousLinearMap.ext fun Y => ?_)
  have hNi := Matrix.nonsing_inv_mul _ hN
  have hK := Matrix.mul_nonsing_inv _ hS
  have k := key_alg H X Y _ _ hNi hK
  change -((4 : ℂ) • (((1 + 1) - X) * (-(Units.val u⁻¹ * (H * (0 + Y) + -Y) * Units.val u⁻¹)) +
      (-Y) * Ring.inverse (H * ((1 + 1) + X) + ((1 + 1) - X)))) =
    (4 : ℂ) • (((1 + 1) - X) * (H * ((1 + 1) + X) + ((1 + 1) - X))⁻¹ * H * ((1 + 1) - X)⁻¹) * Y *
      ((4 : ℂ) • (H * ((1 + 1) + X) + ((1 + 1) - X))⁻¹)
  rw [hinv, ← Matrix.nonsing_inv_eq_ringInverse, smul_four, smul_four, smul_four, zero_add]
  calc _ = (1 + 1 + 1 + 1) * ((Y + ((1 + 1) - X) * (H * ((1 + 1) + X) + ((1 + 1) - X))⁻¹ * (H * Y - Y)) *
          (H * ((1 + 1) + X) + ((1 + 1) - X))⁻¹) := by noncomm_ring
    _ = (1 + 1 + 1 + 1) * (((1 + 1 + 1 + 1) * (((1 + 1) - X) * (H * ((1 + 1) + X) + ((1 + 1) - X))⁻¹ *
          H * ((1 + 1) - X)⁻¹ * Y)) * (H * ((1 + 1) + X) + ((1 + 1) - X))⁻¹) := by rw [k]
    _ = _ := by noncomm_ring

end Deriv

section Sub

variable {P Q : ℕ}

local notation "Mat" => Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ

theorem tauDeriv_at (h : UpqT P Q) (x : lieU P Q) (hx : x ∈ D0 P Q)
    (hn : IsUnit (nH h (x : Mat)).det) :
    ∃ f' : lieU P Q →L[ℝ] lieU P Q,
      (∀ Y : lieU P Q, ((f' Y : lieU P Q) : Mat) = chA h (x : Mat) * (Y : Mat) * chB h (x : Mat)) ∧
      HasFDerivAt (tauL h) f' x := by
  set ι : lieU P Q →L[ℝ] Mat := (lieU P Q).subtypeL with hι
  set L : Mat →L[ℝ] Mat :=
    ContinuousLinearMap.mulLeftRight ℝ Mat (chA h (x : Mat)) (chB h (x : Mat)) with hL
  have hM : HasFDerivAt (tauR (UpqT.mat h)) L (ι x) := hasFDerivAt_tauR (UpqT.mat h) (x : Mat) hn hx
  have c1 : Continuous fun y : lieU P Q => (1 + 1) - ι y := continuous_const.sub ι.continuous
  have c2 : Continuous fun y : lieU P Q => UpqT.mat h * ((1 + 1) + ι y) + ((1 + 1) - ι y) :=
    (continuous_const.mul (continuous_const.add ι.continuous)).add (continuous_const.sub ι.continuous)
  have hev : ∀ᶠ y in 𝓝 x, IsUnit ((1 + 1) - ι y) ∧
      IsUnit (UpqT.mat h * ((1 + 1) + ι y) + ((1 + 1) - ι y)) := by
    filter_upwards [c1.continuousAt.preimage_mem_nhds
        (Units.isOpen.mem_nhds ((Matrix.isUnit_iff_isUnit_det _).2 hx)),
      c2.continuousAt.preimage_mem_nhds
        (Units.isOpen.mem_nhds ((Matrix.isUnit_iff_isUnit_det _).2 hn))] with y h1 h2
    exact ⟨h1, h2⟩
  have heq : (fun y : lieU P Q => ((tauL h y : lieU P Q) : Mat)) =ᶠ[𝓝 x]
      (tauR (UpqT.mat h) ∘ ι) := by
    filter_upwards [hev] with y hy
    have hyD : y ∈ D0 P Q := (Matrix.isUnit_iff_isUnit_det _).1 hy.1
    have hyN : IsUnit (nH h (y : Mat)).det := (Matrix.isUnit_iff_isUnit_det _).1 hy.2
    have hu : IsUnit (UpqT.mat (h * cayF P Q y) + 1).det := by
      have e := hyN
      rw [nH_eq h y hyD, det_mul] at e
      exact isUnit_of_mul_isUnit_left e
    rw [tauL_val h y hyD hu, Matrix.nonsing_inv_eq_ringInverse]
    rfl
  have hF : HasFDerivAt (fun y : lieU P Q => ((tauL h y : lieU P Q) : Mat)) (L.comp ι) x :=
    (HasFDerivAt.comp x hM ι.hasFDerivAt).congr_of_eventuallyEq heq
  have hclosed : IsClosed ((lieU P Q : Set Mat)) := (lieU P Q).closed_of_finiteDimensional
  have hmem : ∀ Y, (L.comp ι) Y ∈ lieU P Q := by
    intro Y
    exact hclosed.mem_of_tendsto (hF.lim_real Y) (Eventually.of_forall fun c =>
      (lieU P Q).smul_mem c ((lieU P Q).sub_mem (tauL h _).2 (tauL h x).2))
  refine ⟨(L.comp ι).codRestrict (lieU P Q) hmem, fun Y => ?_, ?_⟩
  · have hLY : L (ι Y) = chA h (x : Mat) * ι Y * chB h (x : Mat) :=
      ContinuousLinearMap.mulLeftRight_apply _ _ _ _ _
    exact hLY
  · have hF' := hasFDerivAt_iff_isLittleO_nhds_zero.1 hF
    refine hasFDerivAt_iff_isLittleO_nhds_zero.2 ?_
    rw [← Asymptotics.isLittleO_norm_left] at hF' ⊢
    refine hF'.congr_left fun k => ?_
    rfl

end Sub

theorem tau_derivative : TauDeriv := fun _ _ h x hx hn => tauDeriv_at h x hx hn

end HcInf
