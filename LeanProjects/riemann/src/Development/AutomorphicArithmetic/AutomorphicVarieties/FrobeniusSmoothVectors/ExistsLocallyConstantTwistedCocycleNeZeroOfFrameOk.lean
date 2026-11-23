import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.StrSMul
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Imports
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.SmoothVectorFixedByOpenSubgroup
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.LocallyConstantOfKernel

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem lc_of_open_ker {G H : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group H]
    (f : G →* H) (h : IsOpen (f.ker : Set G)) : IsLocallyConstant f :=
  _root_.UpperTheory.Reformulated.B.LocallyConstantOfKernel.lc_of_ker f h

theorem UpperTheory.exists_locallyConstant_twistedCocycle_ne_zero_of_frameOk :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] {F : Frame l k} {C₀ : ℕ}, F.Ok C₀ → ∃ u : F.G0 → k, IsLocallyConstant u ∧ (∀ g h : F.G0, u (g * h) = (F.Ψ h : k) * u g + u h) ∧ (∀ g : F.G0, u (F.star g) = (((F.Ψ g)⁻¹ : kˣ) : k) * u g) ∧ (∀ v, ∃ α : k, ∀ s, u (F.loc0 v s) = ((F.Ψ (F.loc v s) : k) - 1) * α) ∧ u ≠ 0 := by
  intro l _ k _ _ F C₀ h
  have hχ : ∀ g : F.G0, (F.Ψ⁻¹ * F.delK k) (g : F.Γ) = (F.Ψ g)⁻¹ := fun g => by
    have hg : F.del (g : F.Γ) = 1 := g.2
    simp [Frame.delK, hg]
  have hc : (F.Ψ⁻¹ * F.delK k) F.c = -1 := by
    apply Units.ext
    simp [Frame.delK, h.Ψ_c, h.del_c]
  have hl : ∀ v s, F.loc v s = ((F.loc0 v s : F.G0) : F.Γ) := fun _ _ => rfl
  obtain ⟨x, x1, x2, x3, x4, g₁, x5⟩ := UpperTheory.smooth_vector_fixed_by_open_subgroup h (F.Ψ⁻¹ * F.delK k) hc (fun v => by
    obtain ⟨s, hs⟩ := h.f3 v
    refine ⟨s, fun e => hs ?_⟩
    rw [hl, hχ, inv_eq_one] at e
    rw [hl, e, one_pow]) h.f4
  have x0 : x 1 = 0 := by
    have := x2 1 1
    simpa using this
  have hci : F.c⁻¹ = F.c := inv_eq_of_mul_eq_one_right h.c_sq
  refine ⟨fun g => x g * (F.Ψ g : k), ?_, fun g g' => ?_, fun g => ?_, fun v => ?_, fun e => x5 ?_⟩
  · exact (x1.mul ((lc_of_open_ker F.Ψ h.Ψ_open).comp Units.val)).comp_continuous continuous_subtype_val
  · show x ((g : F.Γ) * g') * (F.Ψ ((g : F.Γ) * g') : k) = _
    rw [x2, hχ, map_mul, Units.val_mul, Units.val_inv_eq_inv_val]
    have := (F.Ψ g).ne_zero
    field_simp
  · have hs : ((F.star g : F.G0) : F.Γ) = F.c * ((g : F.Γ)⁻¹ * F.c) := by
      show F.c * (g : F.Γ)⁻¹ * F.c⁻¹ = _
      rw [hci, mul_assoc]
    have h1 : x (g : F.Γ)⁻¹ + (F.Ψ g : k) * x g = 0 := by
      have := x2 (g : F.Γ)⁻¹ g
      rw [inv_mul_cancel, x0, map_inv, hχ, inv_inv] at this
      exact this.symm
    show x (F.star g) * (F.Ψ (F.star g) : k) = _
    rw [(UpperTheory.V.Fr.star h).2.2.1, hs, x2, x2, x3, hc]
    simp only [Units.val_neg, Units.val_one]
    linear_combination (-(((F.Ψ g)⁻¹ : kˣ) : k)) * h1
  · obtain ⟨Y, hY⟩ := x4 v
    refine ⟨-Y, fun s => ?_⟩
    show x (F.loc v s) * (F.Ψ (F.loc v s) : k) = _
    rw [hY, hl, hχ, Units.val_inv_eq_inv_val]
    have := (F.Ψ (F.loc0 v s)).ne_zero
    field_simp
    ring
  · exact (mul_eq_zero.1 (congrFun e g₁)).resolve_right (F.Ψ g₁).ne_zero
