import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PowIdeal

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE TensorProduct

set_option autoImplicit false

namespace GlobalTheory.CompanionTheory.GE.NonIso

theorem exists_ideal_not_pow_le {X : Scheme.{0}} (J : X.IdealSheafData) (W : J.subscheme.Opens)
    (hW : (W : Set J.subscheme).Nonempty) :
    ∃ J₀ : X.IdealSheafData, (∀ (V : X.affineOpens) (f : Γ(X, V)), f ∈ J₀.ideal V →
      J.subschemeι ⁻¹ᵁ X.basicOpen f ≤ W) ∧ ∀ m, ¬ powIdeal J₀ m ≤ J := by
  have hC : IsClosed (J.subschemeι '' (W : Set J.subscheme)ᶜ) :=
    J.subschemeι.isClosedEmbedding.isClosedMap _ W.isOpen.isClosed_compl
  let C : TopologicalSpace.Closeds X := ⟨_, hC⟩
  have hsupp : ∀ x : X, x ∈ (Scheme.IdealSheafData.vanishingIdeal C).support ↔
      x ∈ J.subschemeι '' (W : Set J.subscheme)ᶜ := by
    intro x
    rw [← SetLike.mem_coe, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  refine ⟨Scheme.IdealSheafData.vanishingIdeal C, ?_, ?_⟩
  · intro V f hf y hy
    have hyV : J.subschemeι y ∈ (V : X.Opens) := X.basicOpen_le f hy
    by_contra hyW
    have h1 : J.subschemeι y ∈ (Scheme.IdealSheafData.vanishingIdeal C).support :=
      (hsupp _).2 ⟨y, hyW, rfl⟩
    rw [Scheme.IdealSheafData.mem_support_iff_of_mem hyV, Scheme.mem_zeroLocus_iff] at h1
    exact h1 f hf hy
  · intro m hm
    obtain ⟨w, hw⟩ := hW
    obtain ⟨V, hV, hxV, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens)
      (show J.subschemeι w ∈ (⊤ : X.Opens) from trivial)
    let V' : X.affineOpens := ⟨V, hV⟩
    have hxV' : J.subschemeι w ∈ (V' : X.Opens) := hxV
    have hnC : J.subschemeι w ∉ (Scheme.IdealSheafData.vanishingIdeal C).support := by
      rw [hsupp]
      rintro ⟨w', hw', he⟩
      exact hw' (J.subschemeι.isClosedEmbedding.injective he ▸ hw)
    rw [Scheme.IdealSheafData.mem_support_iff_of_mem hxV', Scheme.mem_zeroLocus_iff] at hnC
    push_neg at hnC
    obtain ⟨f, hf, hxf⟩ := hnC
    have hfm : f ^ m ∈ J.ideal V' := Scheme.IdealSheafData.le_def.1 hm V' (Ideal.pow_mem_pow hf m)
    have hxJ : J.subschemeι w ∈ J.support := by
      rw [← SetLike.mem_coe, ← J.range_subschemeι]; exact ⟨w, rfl⟩
    rw [Scheme.IdealSheafData.mem_support_iff_of_mem hxV', Scheme.mem_zeroLocus_iff] at hxJ
    refine hxJ (f ^ m) hfm ?_
    rcases Nat.eq_zero_or_pos m with rfl | hm0
    · rw [pow_zero, Scheme.basicOpen_of_isUnit _ isUnit_one]; trivial
    · rwa [Scheme.basicOpen_pow _ _ hm0]

end GlobalTheory.CompanionTheory.GE.NonIso
