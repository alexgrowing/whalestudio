import Mathlib
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.StrictDominanceCasselman.IsStrictlyDominant
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq

open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel PositivityTheory.Lbc

namespace GlobalTheory.CompanionTheory.CompactAvg

theorem exists_perm_of_reps {G : Type} [Group G] (J H : Subgroup G) {r : ℕ} (x : Fin r → G)
    (hx : ∀ i, x i ∈ J) (hu : ∀ y ∈ J, ∃! i, (x i)⁻¹ * y ∈ H) {j : G} (hj : j ∈ J) :
    ∃ σ : Equiv.Perm (Fin r), ∀ i, (x (σ i))⁻¹ * (j * x i) ∈ H := by
  have h : ∀ i, ∃ k, (x k)⁻¹ * (j * x i) ∈ H := fun i => (hu _ (J.mul_mem hj (hx i))).exists
  choose f hf using h
  have hinj : Function.Injective f := by
    intro a b hab
    have ha := hf a
    have hb := hf b
    rw [← hab] at hb
    have hm : (x a)⁻¹ * x b ∈ H := by
      have h2 := H.mul_mem (H.inv_mem ha) hb
      have e : ((x (f a))⁻¹ * (j * x a))⁻¹ * ((x (f a))⁻¹ * (j * x b)) = (x a)⁻¹ * x b := by group
      rwa [e] at h2
    have h1 : (x b)⁻¹ * x b ∈ H := by simp [H.one_mem]
    exact (hu (x b) (hx b)).unique hm h1
  exact ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.1 hinj), hf⟩

theorem exists_average : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (J : Subgroup G), IsCompact (J : Set G) → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V), IsSmooth π → ∃ E : V →ₗ[ℂ] V, (∀ v, E v ∈ fixed π J) ∧ (∀ v ∈ fixed π J, E v = v) ∧ (∀ l : Module.Dual ℂ V, (∀ x ∈ J, l ∘ₗ π x = l) → l ∘ₗ E = l) ∧ (∀ x ∈ J, E ∘ₗ π x = E) ∧ ∀ (u : V) (H : Subgroup G), H ≤ J → (∀ h ∈ H, π h u = u) → ∀ (r : ℕ) (x : Fin r → G), 0 < r → (∀ i, x i ∈ J) → (∀ y ∈ J, ∃! i, (x i)⁻¹ * y ∈ H) → E u = ((r : ℂ)⁻¹) • ∑ i, π (x i) u := by
  intro G _ _ _ J hJ V _ _ π hπ
  have hsub : ∀ v, v - GlobalTheory.LocGL.idem hπ hJ v ∈ twKer π J 1 := fun v => by
    rw [← GlobalTheory.LocGL.idem_eq_zero_iff hπ hJ, map_sub,
      GlobalTheory.LocGL.idem_of_mem hπ hJ (GlobalTheory.LocGL.idem_mem hπ hJ v), sub_self]
  refine ⟨GlobalTheory.LocGL.idem hπ hJ, GlobalTheory.LocGL.idem_mem hπ hJ, fun v hv => GlobalTheory.LocGL.idem_of_mem hπ hJ hv,
    ?_, ?_, ?_⟩
  · intro l hl
    have hk : twKer π J 1 ≤ LinearMap.ker l := by
      refine Submodule.span_le.2 ?_
      rintro w ⟨n, v, rfl⟩
      have h1 : l (π (n : G) v) = l v := LinearMap.congr_fun (hl n n.2) v
      simp [h1]
    refine LinearMap.ext fun v => ?_
    have h2 := hk (hsub v)
    rw [LinearMap.mem_ker, map_sub, sub_eq_zero] at h2
    exact h2.symm
  · intro x hx
    exact LinearMap.ext fun v => GlobalTheory.LocGL.idem_apply_mem hπ hJ hx v
  · intro u H _ hu r x hr hxJ hex
    have hrc : (r : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hr.ne'
    have hfix : ((r : ℂ)⁻¹ • ∑ i, π (x i) u) ∈ fixed π J := GlobalTheory.Parabolic.mem_fixed.2 fun j hj => by
      obtain ⟨σ, hσ⟩ := exists_perm_of_reps J H x hxJ hex hj
      rw [map_smul, map_sum]
      congr 1
      refine Fintype.sum_equiv σ _ _ fun i => ?_
      have e : j * x i = x (σ i) * ((x (σ i))⁻¹ * (j * x i)) := by group
      rw [← Module.End.mul_apply, ← map_mul, e, map_mul, Module.End.mul_apply, hu _ (hσ i)]
    have h3 : GlobalTheory.LocGL.idem hπ hJ ((r : ℂ)⁻¹ • ∑ i, π (x i) u) = GlobalTheory.LocGL.idem hπ hJ u := by
      rw [map_smul, map_sum, Finset.sum_congr rfl fun i _ => GlobalTheory.LocGL.idem_apply_mem hπ hJ (hxJ i) u,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
        inv_mul_cancel₀ hrc, one_smul]
    rw [← h3, GlobalTheory.LocGL.idem_of_mem hπ hJ hfix]

end GlobalTheory.CompanionTheory.CompactAvg
