import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.SquareIntegrable.SSmooth

noncomputable section

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open scoped ValuativeRel

namespace Ad3.SchwartzSpaceL2

theorem top (hpsi : SPsi) (hcen : SCen) (htr : STrans) (hsm : SSmooth) (hbd : SBound) (hne : SNe)
    (hun : SUnr) (hfe : FeGen) : Loc2 := by
  intro F _ _ _ _ _ _ ψ hψ μ₁ μ₂ h₁ h₂
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, hun F ψ hψ μ₁ μ₂ h₁ h₂⟩
  · obtain ⟨φ, hφ, h⟩ := hne F ψ hψ μ₁ μ₂ h₁ h₂
    exact ⟨_, Submodule.subset_span ⟨φ, hφ, rfl⟩, h⟩
  · intro W hW h
    induction hW using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨φ, hφ, rfl⟩ := hx
      obtain ⟨hm, he⟩ := htr F ψ hψ μ₁ μ₂ h₁ h₂ φ hφ h
      have : (fun g => W2 ψ μ₁ μ₂ φ (g * h)) =
          (((μ₂ (GeneralLinearGroup.det h) : ℂˣ) : ℂ) * mp (GeneralLinearGroup.det h) (1 / 2)) •
            W2 ψ μ₁ μ₂ (rt φ h) := by
        funext g; rw [he g]; rfl
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, hm, rfl⟩)
    | zero => exact Submodule.zero_mem _
    | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
    | smul a x _ hx => exact Submodule.smul_mem _ a hx
  · intro W hW x g
    induction hW using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨φ, hφ, rfl⟩ := hw
      exact hpsi F ψ hψ μ₁ μ₂ h₁ h₂ φ hφ x g
    | zero => simp
    | add u v _ _ hu hv => simp only [Pi.add_apply, hu, hv]; ring
    | smul a u _ hu => simp only [Pi.smul_apply, smul_eq_mul, hu]; ring
  · intro W hW a g
    induction hW using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨φ, hφ, rfl⟩ := hw
      exact hcen F ψ hψ μ₁ μ₂ h₁ h₂ φ hφ a g
    | zero => simp
    | add u v _ _ hu hv => simp only [Pi.add_apply, hu, hv]; ring
    | smul b u _ hu => simp only [Pi.smul_apply, smul_eq_mul, hu]; ring
  · intro W hW
    induction hW using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨φ, hφ, rfl⟩ := hw
      exact hsm F ψ hψ μ₁ μ₂ h₁ h₂ φ hφ
    | zero => exact ⟨⊤, fun _ _ _ => rfl⟩
    | add u v _ _ hu hv =>
      obtain ⟨U, hU⟩ := hu
      obtain ⟨V, hV⟩ := hv
      refine ⟨U ⊓ V, fun g w hw => ?_⟩
      simp only [Pi.add_apply, hU g w hw.1, hV g w hw.2]
    | smul b u _ hu =>
      obtain ⟨U, hU⟩ := hu
      exact ⟨U, fun g w hw => by simp only [Pi.smul_apply, hU g w hw]⟩
  · intro W hW ε hε
    induction hW using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨φ, hφ, rfl⟩ := hw
      exact hbd F ψ hψ μ₁ μ₂ h₁ h₂ φ hφ ε hε
    | zero => exact ⟨0, 0, fun a k _ => ⟨by simp, fun h => absurd rfl h⟩⟩
    | add u v _ _ hu hv =>
      obtain ⟨C₁, B₁, hu⟩ := hu
      obtain ⟨C₂, B₂, hv⟩ := hv
      refine ⟨C₁ + C₂, max B₁ B₂, fun a k hk => ⟨?_, fun hne => ?_⟩⟩
      · have h1 := (hu a k hk).1
        have h2 := (hv a k hk).1
        calc ‖(u + v) (dg2 a 1 * k)‖ ≤ ‖u (dg2 a 1 * k)‖ + ‖v (dg2 a 1 * k)‖ := norm_add_le _ _
          _ ≤ _ := by rw [add_mul]; exact add_le_add h1 h2
      · by_cases hu0 : u (dg2 a 1 * k) = 0
        · have : v (dg2 a 1 * k) ≠ 0 := by
            intro h0; apply hne; simp [hu0, h0]
          exact le_max_of_le_right ((hv a k hk).2 this)
        · exact le_max_of_le_left ((hu a k hk).2 hu0)
    | smul b u _ hu =>
      obtain ⟨C, B, hu⟩ := hu
      refine ⟨‖b‖ * C, B, fun a k hk => ⟨?_, fun hne => ?_⟩⟩
      · rw [Pi.smul_apply, smul_eq_mul, norm_mul, mul_assoc]
        exact mul_le_mul_of_nonneg_left (hu a k hk).1 (norm_nonneg _)
      · refine (hu a k hk).2 fun h0 => hne ?_
        simp [h0]
  · intro W hW c hc s hs0 hs1
    suffices H : Integrable (fun a : Fˣ => W (dg2 a 1 * w0) * (((μ₁ a * μ₂ a * c a)⁻¹ : ℂˣ) : ℂ) *
          mp a (1 / 2 - s)) (multHaar F) ∧
        Integrable (fun a : Fˣ => W (dg2 a 1) * ((c a : ℂˣ) : ℂ) * mp a (s - 1 / 2)) (multHaar F) ∧
        ∫ a, W (dg2 a 1 * w0) * (((μ₁ a * μ₂ a * c a)⁻¹ : ℂˣ) : ℂ) * mp a (1 / 2 - s) ∂multHaar F =
          gam ψ (μ₁ * c) s * gam ψ (μ₂ * c) s *
            ∫ a, W (dg2 a 1) * ((c a : ℂˣ) : ℂ) * mp a (s - 1 / 2) ∂multHaar F from H.2.2
    induction hW using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨φ, hφ, rfl⟩ := hw
      exact hfe F ψ hψ μ₁ μ₂ h₁ h₂ φ hφ c hc s hs0 hs1
    | zero => simp
    | add u v _ _ hu hv =>
      obtain ⟨hu1, hu2, hu3⟩ := hu
      obtain ⟨hv1, hv2, hv3⟩ := hv
      simp only [Pi.add_apply, add_mul]
      refine ⟨hu1.add hv1, hu2.add hv2, ?_⟩
      rw [integral_add hu1 hv1, integral_add hu2 hv2, hu3, hv3]
      ring
    | smul b u _ hu =>
      obtain ⟨hu1, hu2, hu3⟩ := hu
      simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]
      simp only [← mul_assoc] at hu1 hu2 hu3 ⊢
      refine ⟨?_, ?_, ?_⟩
      · simpa only [mul_assoc] using hu1.const_mul b
      · simpa only [mul_assoc] using hu2.const_mul b
      · simp only [mul_assoc]
        rw [integral_const_mul, integral_const_mul]
        simp only [← mul_assoc] at hu3 ⊢
        rw [hu3]
        ring

theorem top' (hpsi : SPsi) (hcen : SCen) (htr : STrans) (hsm : SSmooth) (hbd : SBound) (hne : SNe)
    (hun : SUnr) (hdz : SDZ) (hwd : SWd) (hpu : SPure) (hli : SLin) (hta : STate) (hfe : SFe) : Loc2 :=
  top hpsi hcen htr hsm hbd hne hun (hfe hdz hwd hpu hli htr hta)

end Ad3.SchwartzSpaceL2
