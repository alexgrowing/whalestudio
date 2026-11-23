import Mathlib
import CompanionTheory.AutomorphicTheory.SchurLimitBounds.SchurOrthogonality.URepBasic

namespace CompanionTheory.LimBd.URep

namespace UnitaryRep

open scoped InnerProductSpace ComplexConjugate
open scoped ComplexStarModule
open ContinuousLinearMap Complex

variable {G : Type*} [Group G] [TopologicalSpace G]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {π : UnitaryRep G H} {σ : UnitaryRep G K}

omit [CompleteSpace H] in

lemma nontrivial_endomorphisms [Nontrivial H] : Nontrivial (H →L[ℂ] H) := by
  obtain ⟨v, hv⟩ := exists_ne (0 : H)
  exact ⟨⟨1, 0, fun h => hv (by simpa using congrArg (fun T : H →L[ℂ] H => T v) h)⟩⟩

theorem IsIrreducible.spectrum_subsingleton (hπ : π.IsIrreducible) {A : H →L[ℂ] H}
    (hA : A ∈ π.intertwiners π) (hsa : IsSelfAdjoint A) : (spectrum ℝ A).Subsingleton := by
  have := hπ.1
  have := nontrivial_endomorphisms (H := H)
  intro a ha b hb
  by_contra hab
  wlog hlt : a < b generalizing a b
  · exact this hb ha (Ne.symm hab) (lt_of_le_of_ne (not_lt.mp hlt) (Ne.symm hab))
  set c := (a + b) / 2 with hc
  have hcb : c < b := by rw [hc]; linarith
  have hac : a < c := by rw [hc]; linarith
  let f : ℝ → ℝ := fun x => max (x - c) 0
  let g : ℝ → ℝ := fun x => max (c - x) 0
  have hfc : Continuous f := by fun_prop
  have hgc : Continuous g := by fun_prop
  have hgf : (fun x => g x * f x) = (0 : ℝ → ℝ) := by
    funext x
    rcases le_total x c with h | h
    · simp [f, max_eq_right (sub_nonpos.mpr h)]
    · simp [g, max_eq_right (sub_nonpos.mpr h)]
  have hQP : cfc g A * cfc f A = 0 := by
    rw [← cfc_mul g f A hgc.continuousOn hfc.continuousOn, hgf, cfc_zero]
  have hne : ∀ (φ : ℝ → ℝ), Continuous φ → ∀ x ∈ spectrum ℝ A, φ x ≠ 0 → cfc φ A ≠ 0 := by
    intro φ hφ x hx hφx h
    have hs : spectrum ℝ (cfc φ A) = φ '' spectrum ℝ A := cfc_map_spectrum φ A hsa hφ.continuousOn
    have hmem : φ x ∈ spectrum ℝ (cfc φ A) := hs ▸ ⟨x, hx, rfl⟩
    rw [h, spectrum.zero_eq, Set.mem_singleton_iff] at hmem
    exact hφx hmem
  have hP0 : cfc f A ≠ 0 := hne f hfc b hb (by
    simp only [f]; rw [max_eq_left (by linarith)]; linarith)
  have hQ0 : cfc g A ≠ 0 := hne g hgc a ha (by
    simp only [g]; rw [max_eq_left (by linarith)]; linarith)
  have hPmem : cfc f A ∈ π.intertwiners π :=
    mem_intertwiners_self_iff.mpr fun h => (commute_of_mem_intertwiners hA h).cfc_real f
  set V := (LinearMap.range ((cfc f A : H →L[ℂ] H) : H →ₗ[ℂ] H)).topologicalClosure with hV
  have hinv : π.IsInvariant V := (isInvariant_range hPmem).topologicalClosure
  rcases hπ.2 V (Submodule.isClosed_topologicalClosure _) hinv with hbot | htop
  · apply hP0
    ext v
    have : cfc f A v ∈ V := Submodule.le_topologicalClosure _ ⟨v, rfl⟩
    rw [hbot, Submodule.mem_bot] at this
    simpa using this
  · apply hQ0
    have hle : LinearMap.range ((cfc f A : H →L[ℂ] H) : H →ₗ[ℂ] H) ≤
        LinearMap.ker ((cfc g A : H →L[ℂ] H) : H →ₗ[ℂ] H) := by
      rintro _ ⟨v, rfl⟩
      simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
      have := congrArg (fun T : H →L[ℂ] H => T v) hQP
      simpa using this
    have hcl := Submodule.topologicalClosure_minimal _ hle (cfc g A).isClosed_ker
    rw [← hV, htop] at hcl
    ext v
    have : v ∈ LinearMap.ker ((cfc g A : H →L[ℂ] H) : H →ₗ[ℂ] H) := hcl Submodule.mem_top
    simpa using this

theorem IsIrreducible.exists_eq_algebraMap_of_isSelfAdjoint (hπ : π.IsIrreducible)
    {A : H →L[ℂ] H} (hA : A ∈ π.intertwiners π) (hsa : IsSelfAdjoint A) :
    ∃ c : ℝ, A = algebraMap ℝ (H →L[ℂ] H) c := by
  have := hπ.1
  have := nontrivial_endomorphisms (H := H)
  have hne : (spectrum ℝ A).Nonempty := ContinuousFunctionalCalculus.spectrum_nonempty A hsa
  obtain ⟨c, hc⟩ := hne
  refine ⟨c, ?_⟩
  have hsub := hπ.spectrum_subsingleton hA hsa
  calc A = cfc (fun x : ℝ => x) A := (cfc_id' ℝ A hsa).symm
    _ = cfc (fun _ : ℝ => c) A := cfc_congr fun x hx => hsub hx hc
    _ = algebraMap ℝ _ c := cfc_const c A hsa

theorem IsIrreducible.exists_eq_smul_one (hπ : π.IsIrreducible) {T : H →L[ℂ] H}
    (hT : T ∈ π.intertwiners π) : ∃ c : ℂ, T = c • (1 : H →L[ℂ] H) := by
  have hstar := star_mem_intertwiners hT
  have hre : (ℜ T : H →L[ℂ] H) ∈ π.intertwiners π := by
    rw [realPart_apply_coe]
    exact Submodule.smul_of_tower_mem _ _ (add_mem hT hstar)
  have him : (ℑ T : H →L[ℂ] H) ∈ π.intertwiners π := by
    rw [imaginaryPart_apply_coe]
    exact Submodule.smul_mem _ _ (Submodule.smul_of_tower_mem _ _ (sub_mem hT hstar))
  obtain ⟨a, ha⟩ := hπ.exists_eq_algebraMap_of_isSelfAdjoint hre (ℜ T).2
  obtain ⟨b, hb⟩ := hπ.exists_eq_algebraMap_of_isSelfAdjoint him (ℑ T).2
  refine ⟨a + I * b, ?_⟩
  conv_lhs => rw [← realPart_add_I_smul_imaginaryPart T, ha, hb]
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, ← Complex.coe_smul,
    ← Complex.coe_smul, smul_smul, ← add_smul]

theorem isIrreducible_iff :
    π.IsIrreducible ↔
      Nontrivial H ∧ ∀ T ∈ π.intertwiners π, ∃ c : ℂ, T = c • (1 : H →L[ℂ] H) := by
  refine ⟨fun hπ => ⟨hπ.1, fun T hT => hπ.exists_eq_smul_one hT⟩, fun ⟨hnt, h⟩ => ⟨hnt, ?_⟩⟩
  intro V hcl hinv
  have : CompleteSpace V := hcl.completeSpace_coe
  have hP : V.starProjection ∈ π.intertwiners π :=
    mem_intertwiners_self_iff.mpr fun g => ((isInvariant_iff_commute_starProjection V).mp hinv g).symm
  obtain ⟨c, hc⟩ := h _ hP
  have hPv : ∀ v, V.starProjection v = c • v := fun v => by simp [hc]
  by_cases hc0 : c = 0
  · left
    rw [eq_bot_iff]
    intro v hv
    rw [Submodule.mem_bot, ← Submodule.starProjection_eq_self_iff.mpr hv, hPv, hc0, zero_smul]
  · right
    rw [eq_top_iff]
    intro v _
    have hmem : V.starProjection v ∈ V := V.starProjection_apply_mem v
    rw [hPv] at hmem
    simpa [hc0] using V.smul_mem c⁻¹ hmem

theorem IsIrreducible.isEquivalent_of_mem_intertwiners (hπ : π.IsIrreducible)
    (hσ : σ.IsIrreducible) {T : H →L[ℂ] K} (hT : T ∈ π.intertwiners σ) (hT0 : T ≠ 0) :
    π.IsEquivalent σ := by
  obtain ⟨c, hc⟩ := hπ.exists_eq_smul_one
    (comp_mem_intertwiners (adjoint_mem_intertwiners hT) hT)
  obtain ⟨d, hd⟩ := hσ.exists_eq_smul_one
    (comp_mem_intertwiners hT (adjoint_mem_intertwiners hT))
  have key : ∀ v, (‖T v‖ : ℂ) ^ 2 = c * (‖v‖ : ℂ) ^ 2 := by
    intro v
    have h1 : ⟪v, (adjoint T ∘L T) v⟫_ℂ = ⟪T v, T v⟫_ℂ := by
      rw [comp_apply, adjoint_inner_right]
    rw [hc] at h1
    simp only [smul_apply, one_apply_eq_self, inner_smul_right] at h1
    have e1 : ⟪v, v⟫_ℂ = (‖v‖ : ℂ) ^ 2 := by rw [inner_self_eq_norm_sq_to_K]; rfl
    have e2 : ⟪T v, T v⟫_ℂ = (‖T v‖ : ℂ) ^ 2 := by rw [inner_self_eq_norm_sq_to_K]; rfl
    rw [e1, e2] at h1
    exact h1.symm
  obtain ⟨v₀, hv₀⟩ : ∃ v, T v ≠ 0 := by
    by_contra h
    push Not at h
    exact hT0 (ContinuousLinearMap.ext h)
  have hv₀' : v₀ ≠ 0 := fun h => hv₀ (by rw [h, map_zero])
  set r : ℝ := ‖T v₀‖ / ‖v₀‖ with hr
  have hrpos : 0 < r := div_pos (norm_pos_iff.mpr hv₀) (norm_pos_iff.mpr hv₀')
  have hcr : c = ((r ^ 2 : ℝ) : ℂ) := by
    have h := key v₀
    have hn : (‖v₀‖ : ℂ) ^ 2 ≠ 0 := pow_ne_zero _ (by exact_mod_cast (norm_pos_iff.mpr hv₀').ne')
    rw [hr, div_pow]
    push_cast
    exact eq_div_of_mul_eq hn h.symm
  have hnorm : ∀ v, ‖T v‖ = r * ‖v‖ := by
    intro v
    have h := key v
    rw [hcr] at h
    have h' : ‖T v‖ ^ 2 = (r * ‖v‖) ^ 2 := by
      rw [mul_pow]; exact_mod_cast h
    exact (pow_left_inj₀ (norm_nonneg _) (mul_nonneg hrpos.le (norm_nonneg _)) two_ne_zero).mp h'
  have hc0 : c ≠ 0 := by rw [hcr]; exact_mod_cast (pow_pos hrpos 2).ne'
  have hcd : c = d := by
    have e1 : T ∘L (adjoint T ∘L T) = c • T := by rw [hc]; ext v; simp
    have e2 : (T ∘L adjoint T) ∘L T = d • T := by rw [hd]; ext v; simp
    have e3 : (c - d) • T = 0 := by rw [sub_smul, ← e1, ← e2]; simp [comp_assoc]
    rcases smul_eq_zero.mp e3 with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hT0
  have hsurjT : Function.Surjective T := by
    intro w
    refine ⟨c⁻¹ • adjoint T w, ?_⟩
    have : (T ∘L adjoint T) w = d • w := by rw [hd]; simp
    rw [map_smul, show T (adjoint T w) = d • w from this, smul_smul, ← hcd, inv_mul_cancel₀ hc0,
      one_smul]
  let U : H →L[ℂ] K := ((r⁻¹ : ℝ) : ℂ) • T
  have hU : ∀ v, ‖U v‖ = ‖v‖ := by
    intro v
    simp only [U, smul_apply, norm_smul, Complex.norm_real, Real.norm_eq_abs, hnorm v,
      abs_of_pos (inv_pos.mpr hrpos)]
    rw [← mul_assoc, inv_mul_cancel₀ hrpos.ne', one_mul]
  let Ui : H →ₗᵢ[ℂ] K := { toLinearMap := (U : H →ₗ[ℂ] K), norm_map' := hU }
  have hsurj : Function.Surjective Ui := by
    intro w
    obtain ⟨v, rfl⟩ := hsurjT w
    refine ⟨(r : ℂ) • v, ?_⟩
    show U ((r : ℂ) • v) = T v
    simp only [U, smul_apply, map_smul, smul_smul]
    rw [← Complex.ofReal_mul, mul_inv_cancel₀ hrpos.ne', Complex.ofReal_one, one_smul]
  refine ⟨⟨LinearIsometryEquiv.ofSurjective Ui hsurj, fun g v => ?_⟩⟩
  show U (π g v) = σ g (U v)
  exact (Submodule.smul_mem _ _ hT) g v

theorem IsIrreducible.eq_zero_of_not_isEquivalent (hπ : π.IsIrreducible) (hσ : σ.IsIrreducible)
    (hne : ¬ π.IsEquivalent σ) {T : H →L[ℂ] K} (hT : T ∈ π.intertwiners σ) : T = 0 := by
  by_contra h
  exact hne (hπ.isEquivalent_of_mem_intertwiners hσ hT h)

end UnitaryRep

end CompanionTheory.LimBd.URep
