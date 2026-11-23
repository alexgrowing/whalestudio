import Mathlib
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.FixedSubgroup
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable

private theorem UpperTheory.Reformulated.B.Gr28.exists_fun
    {G W : Type} [Group G] [AddCommGroup W] [_root_.Module ℂ W]
    (H K : Subgroup G) (σ : Representation ℂ (↥H) W) (w : W)
    (hw : ∀ h : H, (h : G) ∈ K → σ h w = w) :
    ∃ f : G → W, f 1 = w ∧ (∀ (h : H) (g : G), f (h * g) = σ h (f g)) ∧
      ∀ k ∈ K, ∀ g, f (g * k) = f g := by
  classical
  let f : G → W := fun g => if hg : ∃ h : H, (h : G)⁻¹ * g ∈ K then σ hg.choose w else 0
  have pos : ∀ (g : G) (h : H), (h : G)⁻¹ * g ∈ K → f g = σ h w := by
    intro g h hh
    have hg : ∃ h : H, (h : G)⁻¹ * g ∈ K := ⟨h, hh⟩
    have h1 := hg.choose_spec
    have h2 : ((h⁻¹ * hg.choose : H) : G) ∈ K := by
      have := K.mul_mem hh (K.inv_mem h1)
      simpa [mul_assoc] using this
    have h3 := hw _ h2
    have h4 : f g = σ hg.choose w := dif_pos hg
    rw [h4]
    conv_rhs => rw [← h3]
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]
  have neg : ∀ g : G, (¬ ∃ h : H, (h : G)⁻¹ * g ∈ K) → f g = 0 := fun g hg => dif_neg hg
  refine ⟨f, ?_, ?_, ?_⟩
  · rw [pos 1 1 (by simp)]
    simp
  · intro h g
    by_cases hg : ∃ h : H, (h : G)⁻¹ * g ∈ K
    · obtain ⟨a, ha⟩ := hg
      rw [pos g a ha, pos (h * g) (h * a) (by simpa [mul_assoc] using ha), map_mul,
        Module.End.mul_apply]
    · rw [neg g hg, map_zero]
      refine neg _ ?_
      rintro ⟨a, ha⟩
      exact hg ⟨h⁻¹ * a, by simpa [mul_assoc] using ha⟩
  · intro k hk g
    by_cases hg : ∃ h : H, (h : G)⁻¹ * g ∈ K
    · obtain ⟨a, ha⟩ := hg
      rw [pos g a ha, pos (g * k) a (by rw [← mul_assoc]; exact K.mul_mem ha hk)]
    · rw [neg g hg]
      refine neg _ ?_
      rintro ⟨a, ha⟩
      refine hg ⟨a, ?_⟩
      have := K.mul_mem ha (K.inv_mem hk)
      simpa [mul_assoc] using this

theorem UpperTheory.Reformulated.B.Gr28.indVec :
    ∀ {G W : Type} [inst : Group G] [inst_1 : TopologicalSpace G] [inst_2 : IsTopologicalGroup G] [inst_3 : AddCommGroup W]
      [inst_4 : _root_.Module ℂ W] (H K : Subgroup G) (σ : Representation ℂ (↥H) W),
      IsOpen (↑K : Set G) →
        ∀ (w : W),
          (∀ (h : ↥H), (↑h : G) ∈ K → ((σ : ↥H → W →ₗ[ℂ] W) h : W → W) w = w) →
            ∃ (f : ↥(GlobalTheory.PRep.smoothPart (GlobalTheory.PRep.ind H σ))),
              (↑(↑f : ↥(GlobalTheory.PRep.indSpace H σ)) : G → W) (1 : G) = w ∧ f ∈ UpperTheory.Reformulated.B.SubgroupFixedSubmodule.fixd (GlobalTheory.PRep.smInd H σ) K := by
  intro G W _ _ _ _ _ H K σ hK w hw
  obtain ⟨f, h1, h2, h3⟩ := UpperTheory.Reformulated.B.Gr28.exists_fun H K σ w hw
  let F : GlobalTheory.PRep.indSpace H σ := ⟨f, h2⟩
  have hF : ∀ k ∈ K, GlobalTheory.PRep.ind H σ k F = F := by
    intro k hk
    apply Subtype.ext
    funext g
    exact h3 k hk g
  have hs : F ∈ GlobalTheory.PRep.smoothPart (GlobalTheory.PRep.ind H σ) := by
    let T : Subgroup G :=
      { carrier := {g | GlobalTheory.PRep.ind H σ g F = F}
        mul_mem' := by
          intro x y hx hy
          simp only [Set.mem_setOf_eq, map_mul, Module.End.mul_apply] at *
          rw [hy, hx]
        one_mem' := by simp
        inv_mem' := by
          intro x hx
          simp only [Set.mem_setOf_eq] at *
          conv_lhs => rw [← hx]
          rw [← Module.End.mul_apply, ← map_mul]
          simp }
    exact Subgroup.isOpen_mono (H₁ := K) (H₂ := T) hF hK
  refine ⟨⟨F, hs⟩, h1, ?_⟩
  intro k hk
  exact Subtype.ext (hF k hk)
