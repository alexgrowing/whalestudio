import Mathlib

namespace GlobalTheory

theorem transfer_continuous_of_continuousOn : ∀ (R G X : Type) [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup X] [Module R X] [TopologicalSpace X] [IsTopologicalAddGroup X] (ρ : Representation R G X) (H : Subgroup G) [Fintype (G ⧸ H)], IsOpen (H : Set G) → (∀ g, Continuous (ρ g)) → let tr : (G → X) → G → X := fun f g => ∑ q : G ⧸ H, ρ (g • q).out (f ((g • q).out⁻¹ * g * q.out)); ∀ f : G → X, ContinuousOn f H → Continuous (tr f) := by
  intro R G X _ _ _ _ _ _ _ _ ρ H _ hH hρ tr f hf
  show Continuous (fun g => ∑ q : G ⧸ H, ρ (g • q).out (f ((g • q).out⁻¹ * g * q.out)))
  refine continuous_finset_sum _ (fun q _ => ?_)
  refine continuous_iff_continuousAt.2 (fun g₀ => ?_)
  have hsmul : ∀ g : G, g • q = ((g * q.out : G) : G ⧸ H) := by
    intro g
    conv_lhs => rw [← QuotientGroup.out_eq' q]
    rfl
  let ψ : G → G := fun g => (g * q.out)⁻¹ * (g₀ • q).out
  have hψc : Continuous ψ := by fun_prop
  let V : Set G := ψ ⁻¹' (H : Set G)
  have hVo : IsOpen V := hH.preimage hψc
  have key : ∀ g ∈ V, g • q = g₀ • q := by
    intro g hg
    have h1 : ((g * q.out : G) : G ⧸ H) = ((g₀ • q).out : G ⧸ H) := QuotientGroup.eq.2 hg
    rw [hsmul g, h1, QuotientGroup.out_eq']
  have hg₀ : g₀ ∈ V := by
    show (g₀ * q.out)⁻¹ * (g₀ • q).out ∈ H
    apply QuotientGroup.eq.1
    rw [QuotientGroup.out_eq', hsmul]
  have hmem : ∀ g ∈ V, (g₀ • q).out⁻¹ * g * q.out ∈ H := by
    intro g hg
    have h1 := QuotientGroup.eq.1 (show (((g₀ • q).out : G) : G ⧸ H) = ((g * q.out : G) : G ⧸ H) by
      rw [QuotientGroup.out_eq', ← hsmul g, key g hg])
    simpa [mul_assoc] using h1
  have hV : V ∈ nhds g₀ := hVo.mem_nhds hg₀
  have hc : ContinuousAt (fun g => ρ (g₀ • q).out (f ((g₀ • q).out⁻¹ * g * q.out))) g₀ := by
    have hφ : Continuous (fun g : G => (g₀ • q).out⁻¹ * g * q.out) := by fun_prop
    have hw : ContinuousWithinAt (fun g => f ((g₀ • q).out⁻¹ * g * q.out)) V g₀ :=
      ContinuousWithinAt.comp (g := f) (f := fun g : G => (g₀ • q).out⁻¹ * g * q.out) (t := (H : Set G))
        (hf _ (hmem g₀ hg₀)) hφ.continuousWithinAt (fun g hg => hmem g hg)
    exact (hρ _).continuousAt.comp (hw.continuousAt hV)
  refine hc.congr ?_
  filter_upwards [hV] with g hg
  rw [key g hg]

end GlobalTheory
