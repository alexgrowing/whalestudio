import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.BesselOrbitConvolutions.BesselNonvanishingReduction
import Formalism.HermitianCurvature.HermitianCurvatureProofs.L2NormScaling
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselNeZeroOfCyclicOrbit
import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.SmoothCyclicVectors.SmoothCyc

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal

noncomputable section

namespace CompanionTheory.D.Upq.BesselFunctionalConstruction

open Formalism.FourierDecayAlt.ThreeDimData Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.DDSmoothness

def RankOne : Prop :=
  ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ) (h : ℝ)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Mx k r → (H →L[ℂ] H)) (w0 : H) (Wp : Type) [NormedAddCommGroup Wp]
    [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp]
    (z : Fin (2 * r + k + 1) → ℂ) (u : Fin k → ℝ) (π : Mx k r → (Wp →L[ℂ] Wp))
    (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)),
    Side k r ε lam h σ w0 z Formalism.QuantumDeterminants.cStd u π μW μN μG νq →
    ∃ L : H → Wp, ∀ w ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ,
      ∀ v ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ,
        be z Formalism.QuantumDeterminants.cStd π σ μW μN w v = (innerSL ℂ (L v)).smulRight (L w)

theorem shape_of (hR : RankOne) (hBB : BeBessel) : Shape := by
  intro hIn k r ε lam h H _ _ _ σ w0 Wp _ _ _ _ z u π μW μN μG νq hS ⟨x0, hx0, y0, hy0, hne⟩
  have hsm := DD_smooth hIn.2.2.1 hS.1 hS.2.1 hS.2.2.2.2.1
  obtain ⟨L, hL⟩ := hR k r ε lam h H σ w0 Wp z u π μW μN μG νq hS
  rw [hL x0 (hsm x0 hx0) y0 (hsm y0 hy0)] at hne
  have hLx : L x0 ≠ 0 := fun h0 => hne (by ext ξ; simp [h0])
  have hLy : L y0 ≠ 0 := fun h0 => hne (by ext ξ; simp [h0])
  have hn : ⟪L y0, L y0⟫_ℂ ≠ 0 := inner_self_ne_zero.2 hLy
  have hB := bessel_smul
    (hBB hIn k r ε lam h H σ w0 Wp z _ u π μW μN μG νq hS y0 (Or.inl hy0) (L y0))
    (⟪L y0, L y0⟫_ℂ)⁻¹
  have he : ∀ x ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ,
      (⟪L y0, L y0⟫_ℂ)⁻¹ • be z Formalism.QuantumDeterminants.cStd π σ μW μN x y0 (L y0) = L x := fun x hx => by
    rw [hL x hx y0 (hsm y0 hy0), ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, smul_smul,
      inv_mul_cancel₀ hn, one_smul]
  refine ⟨_, hB, ⟨x0, hx0, by rw [he x0 (hsm x0 hx0)]; exact hLx⟩, fun x hx v hv => ?_⟩
  rw [he x hx, he v (hsm v hv), hL x hx v (hsm v hv)]

theorem bessel_add {k r : ℕ} {H Wp : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] {z : Fin (2 * r + k + 1) → ℂ} {ψ : Mx k r → ℂ}
    {σ : Mx k r → (H →L[ℂ] H)} {π : Mx k r → (Wp →L[ℂ] Wp)} {B B' : H → Wp}
    (hB : PI.BesselMapUniq.IsBesselMapSm (k := k) (r := r) z ψ σ π B)
    (hB' : PI.BesselMapUniq.IsBesselMapSm (k := k) (r := r) z ψ σ π B') :
    PI.BesselMapUniq.IsBesselMapSm (k := k) (r := r) z ψ σ π (fun x => B x + B' x) := by
  obtain ⟨a1, a2, a3, C, Ws, hWs, hC⟩ := hB
  obtain ⟨b1, b2, b3, C', Ws', hWs', hC'⟩ := hB'
  refine ⟨fun v hv w hw => ?_, fun c v hv => ?_, fun g hg m hm v hv => ?_, |C| + |C'|, Ws ++ Ws',
    fun W hW => (List.mem_append.1 hW).elim (hWs W) (hWs' W), fun v hv => ?_⟩
  · simp only [a1 v hv w hw, b1 v hv w hw]; abel
  · simp only [a2 c v hv, b2 c v hv, smul_add]
  · simp only [a3 g hg m hm v hv, b3 g hg m hm v hv, map_add, smul_add]
  · have hnn : ∀ L : List (List (Mx k r)),
        0 ≤ (L.map fun W => ‖PI.UpqRep.dsigW (k := k) (r := r) σ W v‖).sum := fun L =>
      List.sum_nonneg fun t ht => by
        obtain ⟨W, -, rfl⟩ := List.mem_map.1 ht
        exact norm_nonneg _
    rw [List.map_append, List.sum_append]
    have h1 := (hC v hv).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (hnn Ws))
    have h2 := (hC' v hv).trans (mul_le_mul_of_nonneg_right (le_abs_self C') (hnn Ws'))
    have h3 := mul_nonneg (abs_nonneg C) (hnn Ws')
    have h4 := mul_nonneg (abs_nonneg C') (hnn Ws)
    refine (norm_add_le _ _).trans ?_
    nlinarith

theorem kFinForm_of (hBC : BeConv) (hBB : BeBessel) : KFinForm := by
  intro hIn k r ε lam h H _ _ _ σ w0 Wp _ _ _ _ z c u π μW μN μG νq hS l hl _ hid v hv x hx
  have hK := hIn.2.2.1
  have hvs := hK k r ε lam H σ hS.1 hS.2.1 v hv
  obtain ⟨-, -, -, hBC4⟩ := hBC hIn k r ε lam h H σ w0 Wp z c u π μW μN μG νq hS
  ext ξ
  have hB := bessel_add
    (hBB hIn k r ε lam h H σ w0 Wp z c u π μW μN μG νq hS v (Or.inr hv) ξ)
    (bessel_smul hl (-⟪l v, ξ⟫_ℂ))
  have h0 := bessel_ne_zero_of_cyclic_orbit (Sm.smoothCyc_of_kFinSmooth hK) hK k r ε lam H σ w0 Wp z c π hS.1
    hS.2.1 hS.2.2.2.2.1 _ hB (fun y hy => by
      have hadj := (hBC4 y hy v (Or.inr hv)).2
      refine ext_inner_left ℂ fun η => ?_
      have e := ContinuousLinearMap.adjoint_inner_left (be z c π σ μW μN y v) ξ η
      rw [hadj, hid v hvs y hy] at e
      simp only [ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, inner_smul_left,
        inner_conj_symm] at e
      rw [inner_add_right, ← e, inner_smul_right, inner_zero_right]
      ring) x hx
  rw [neg_smul, add_neg_eq_zero] at h0
  rw [h0, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply]

end CompanionTheory.D.Upq.BesselFunctionalConstruction

end
