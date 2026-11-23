import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.StrSMul
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Imports
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.SmoothVectorFixedByOpenSubgroup
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.LocallyConstantOfKernel

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem lc_of_ker {G H : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group H] (f : G →* H)
    (hf : IsOpen (f.ker : Set G)) : IsLocallyConstant f :=
  _root_.UpperTheory.Reformulated.B.LocallyConstantOfKernel.lc_of_ker f hf

theorem UpperTheory.exists_mem_strS_ne_zero_of_frameOk :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] {F : Frame l k} {C₀ : ℕ}, F.Ok C₀ → ∃ b ∈ F.strS k, b ≠ 0 := by
  intro l _ k _ _ F C₀ h
  have hχ0 : ∀ g : F.G0, (F.Ψ⁻¹ ^ 2 * F.delK k) g = (F.Ψ g)⁻¹ ^ 2 := fun g => by
    have : F.del g = 1 := g.2
    simp [Frame.delK, this]
  have hχ : ∀ g : F.G0, (((F.Ψ⁻¹ ^ 2 * F.delK k) g : kˣ) : k) = ((F.Ψ g : k))⁻¹ ^ 2 := fun g => by
    rw [hχ0]; simp
  have hc : (F.Ψ⁻¹ ^ 2 * F.delK k) F.c = -1 := by
    apply Units.ext
    simp [Frame.delK, h.Ψ_c, h.del_c]
  obtain ⟨x, x1, x2, x3, x4, g₁, x5⟩ := UpperTheory.smooth_vector_fixed_by_open_subgroup h (F.Ψ⁻¹ ^ 2 * F.delK k) hc (fun v => by
    obtain ⟨s, hs⟩ := h.f3 v
    refine ⟨s, fun e => hs ?_⟩
    have e' := (hχ0 (F.loc0 v s)).symm.trans e
    rw [inv_pow, inv_eq_one] at e'
    exact e') h.f4'
  have x0 : x 1 = 0 := by
    have := x2 1 1
    rw [mul_one, map_one] at this
    simpa using this
  have hci : F.c⁻¹ = F.c := inv_eq_of_mul_eq_one_right h.c_sq
  refine ⟨fun g => x g * F.Ψ g, ⟨?_, fun g g' => ?_, fun g => ?_, fun v => ?_⟩, fun e => ?_⟩
  · exact (x1.mul ((lc_of_ker F.Ψ h.Ψ_open).comp Units.val)).comp_continuous continuous_subtype_val
  · have := (F.Ψ g).ne_zero
    simp only [Subgroup.coe_mul, x2, hχ, map_mul, Units.val_mul, smul_eq_mul, Units.val_inv_eq_inv_val]
    field_simp
  · have hs : ((F.star g : F.G0) : F.Γ) = F.c * ((g : F.Γ)⁻¹ * F.c) := by
      rw [← mul_assoc]
      nth_rewrite 2 [← hci]
      rfl
    have h0 := (F.Ψ g).ne_zero
    have e1 := x2 g (g : F.Γ)⁻¹
    rw [mul_inv_cancel, x0, hχ] at e1
    show x (F.star g) * F.Ψ (F.star g) = x g * F.Ψ g
    rw [(star h).2.2.1 g, hs, x2, x2, x3, hc, Units.val_inv_eq_inv_val]
    have e2 : x g = -((F.Ψ g : k)⁻¹ ^ 2 * x (g : F.Γ)⁻¹) := by linear_combination -e1
    rw [e2]
    simp only [Units.val_neg, Units.val_one]
    field_simp
    ring
  · obtain ⟨Y, hY⟩ := x4 v
    refine ⟨-Y, fun s => ?_⟩
    have h0 := (F.Ψ (F.loc v s)).ne_zero
    have e : (((F.Ψ⁻¹ ^ 2 * F.delK k) (F.loc v s) : kˣ) : k) = ((F.Ψ (F.loc v s) : k))⁻¹ ^ 2 := hχ (F.loc0 v s)
    show x (F.loc v s) * F.Ψ (F.loc v s) = _
    rw [hY, e, Units.val_inv_eq_inv_val, smul_eq_mul]
    field_simp
    ring
  · exact mul_ne_zero x5 (F.Ψ g₁).ne_zero (congrFun e g₁)
