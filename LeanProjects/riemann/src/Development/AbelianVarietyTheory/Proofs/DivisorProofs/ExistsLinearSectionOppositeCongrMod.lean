import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EquivOfIsometryApply
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LowDat GlobalTheory.LowFilt

namespace GlobalTheory.LowFilt

theorem exists_cell_section : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H) {X : Type} [AddCommGroup X] [Module (𝓞 E) X] [Module.Free ℤ X]
    (y : D.La →ₗ[𝓞 E] X) (n N : ℕ), 0 < n → N ∣ n → ∀ Z Z' : Submodule (𝓞 E) D.La, IsOpp D Z Z' →
    (∀ a, (∃ e, y a = N • e) ↔ ∃ b ∈ perp D Z, ∃ e, a = b + N • e) → (∀ x, ∃ b ∈ Z', ∃ e, y b = x + n • e) →
    ∃ σ : D.La →ₗ[𝓞 E] D.La, (∀ a, σ a ∈ Z') ∧ (∀ b ∈ Z', σ b = b) ∧ (∀ a, ∃ e, y (σ a) = y a + n • e) ∧
      ∀ a, ∃ b ∈ perp D Z, ∃ e, σ a = a + b + N • e := by
  intro E _ _ _ H D X _ _ _ y n N hn hN Z Z' h hker hsurj
  haveI := D.proj
  have hN0 : N ≠ 0 := by
    rintro rfl
    rw [zero_dvd_iff] at hN
    omega
  let mulN : X →ₗ[𝓞 E] X := N • LinearMap.id
  have hinj : Function.Injective mulN := by
    intro u v huv
    have h1 : N • u = N • v := by simpa [mulN] using huv
    have h2 : (N : ℤ) • (u - v) = 0 := by
      rw [smul_sub, natCast_zsmul, natCast_zsmul, h1, sub_self]
    rcases smul_eq_zero.1 h2 with h3 | h3
    · exact absurd (by exact_mod_cast h3) hN0
    · exact sub_eq_zero.1 h3
  let q : D.La →ₗ[𝓞 E] D.La := LinearMap.id - Z'.subtype ∘ₗ h.proj
  have hqa : ∀ a, q a = a - (h.proj a : D.La) := fun a => rfl
  have hq : ∀ a, q a ∈ perp D Z := fun a => by rw [hqa]; exact h.sub_proj_mem a
  have hrange : ∀ a, (y ∘ₗ q) a ∈ LinearMap.range mulN := fun a => by
    obtain ⟨e, he⟩ := (hker (q a)).2 ⟨q a, hq a, 0, by simp⟩
    exact ⟨e, by simp [mulN, he]⟩
  let ε : D.La →ₗ[𝓞 E] X :=
    (LinearEquiv.ofInjective mulN hinj).symm.toLinearMap ∘ₗ (y ∘ₗ q).codRestrict _ hrange
  have hε : ∀ a, N • ε a = y (q a) := by
    intro a
    have h2 := congrArg Subtype.val ((LinearEquiv.ofInjective mulN hinj).apply_symm_apply ⟨(y ∘ₗ q) a, hrange a⟩)
    rw [LinearEquiv.ofInjective_apply] at h2
    exact h2
  let muln : X →ₗ[𝓞 E] X := n • LinearMap.id
  let S : Submodule (𝓞 E) X := LinearMap.range muln
  let g : Z' →ₗ[𝓞 E] X ⧸ S := S.mkQ ∘ₗ y ∘ₗ Z'.subtype
  have hg : Function.Surjective g := by
    intro x
    obtain ⟨x, rfl⟩ := S.mkQ_surjective x
    obtain ⟨b, hb, e, he⟩ := hsurj x
    refine ⟨⟨b, hb⟩, ?_⟩
    simp only [g, LinearMap.comp_apply, Submodule.subtype_apply, Submodule.mkQ_apply, he]
    rw [Submodule.Quotient.eq]
    exact ⟨e, by simp [mulN, muln]⟩
  obtain ⟨s, hs⟩ := Module.projective_lifting_property g (S.mkQ ∘ₗ ε) hg
  have hs' : ∀ a, ∃ e, y (s a) = ε a + n • e := by
    intro a
    have h1 := LinearMap.congr_fun hs a
    simp only [g, LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.subtype_apply] at h1
    rw [Submodule.Quotient.eq] at h1
    obtain ⟨e, he⟩ := h1
    refine ⟨e, ?_⟩
    have he' : n • e = y (s a) - ε a := by simpa [muln] using he
    rw [he']
    abel
  refine ⟨Z'.subtype ∘ₗ h.proj + N • (Z'.subtype ∘ₗ s ∘ₗ q), fun a => ?_, fun b hb => ?_, fun a => ?_, fun a => ?_⟩
  · simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.comp_apply, Submodule.subtype_apply]
    exact add_mem (h.proj a).2 (Z'.nsmul_mem (s (q a)).2 N)
  · have hqb : q b = 0 := by rw [hqa, h.proj_of_mem hb, sub_self]
    simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.comp_apply, Submodule.subtype_apply, hqb,
      map_zero, ZeroMemClass.coe_zero, smul_zero, add_zero]
    exact h.proj_of_mem hb
  · obtain ⟨e, he⟩ := hs' (q a)
    refine ⟨N • e, ?_⟩
    simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.comp_apply, Submodule.subtype_apply, map_add,
      map_nsmul]
    have hy : y (q a) = y a - y (h.proj a) := by rw [hqa, map_sub]
    have hqq : q (q a) = q a := by rw [hqa (q a), h.proj_of_perp (hq a), sub_zero]
    rw [he, smul_add, hε, hqq, hy, smul_comm N n e]
    abel
  · refine ⟨(h.proj a : D.La) - a, ?_, s (q a), ?_⟩
    · have := neg_mem (h.sub_proj_mem a)
      rwa [neg_sub] at this
    · simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.comp_apply, Submodule.subtype_apply]
      abel

end GlobalTheory.LowFilt
