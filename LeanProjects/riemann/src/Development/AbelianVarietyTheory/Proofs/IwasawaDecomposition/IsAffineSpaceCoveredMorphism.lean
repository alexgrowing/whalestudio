import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValRSpMapFromSpecStalk

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.FlagBundle

namespace GlobalTheory.FlagBundle

theorem ProjBundle.affCover (F Ω Ω' : Type) [Field F] [Field Ω] [Algebra F Ω] [Field Ω'] [Algebra F Ω']
    (M : RatModel F Ω) (M' : RatModel F Ω') (φ : Ω →ₐ[F] Ω') (f : M'.Z ⟶ M.Z) (J : Type) [Fintype J] [DecidableEq J]
    (EE : M.Lat J) (s : J → Ω') (h : ProjBundle M EE M' φ f s) : AffCover M M' φ f (Fintype.card J - 1) := by
  refine ⟨h.hom, fun z' => ?_⟩
  obtain ⟨U₀, b, hz, hb, hE⟩ := EE.loc (f z')
  obtain ⟨W, hW, hzW, hle⟩ := exists_isAffineOpen_mem_and_subset (U := U₀) hz
  obtain ⟨hc, hch⟩ := h.chart W b hW ⟨_, hzW⟩ fun z hzz => hE z (hle hzz)
  obtain ⟨i, hi⟩ := hc z' hzW
  obtain ⟨U, hU, hUe, hR⟩ := hch i hi.1
  have hcard : Fintype.card {j // j ≠ i} = Fintype.card J - 1 := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]
  let e : Fin (Fintype.card J - 1) ≃ {j // j ≠ i} := (Fintype.equivFinOfCardEq hcard).symm
  have hmem : ∀ y, y ∈ U ↔ f y ∈ W ∧ M'.Div ((b.map φ).mulVec s) i y := fun y =>
    Set.ext_iff.1 hUe y
  refine ⟨U, W, fun k => (b.map φ).mulVec s (e k).1 / (b.map φ).mulVec s i, hU, hW, (hmem z').2 ⟨hzW, hi⟩,
    fun y hy => ((hmem y).1 hy).1, fun P hP => ?_, ?_⟩
  · apply MvPolynomial.rename_injective e e.injective
    rw [map_zero]
    refine (h.gen b hb i).2 _ ?_
    rw [MvPolynomial.eval₂_rename]
    exact hP
  · rw [hR]
    refine le_antisymm (Algebra.adjoin_le ?_) (Algebra.adjoin_mono (Set.union_subset_union_right _ ?_))
    · rintro x (hx | ⟨j, rfl⟩)
      · exact Algebra.subset_adjoin (Or.inl hx)
      · by_cases hj : j = i
        · subst hj
          show _ / _ ∈ _
          rw [div_self hi.1]
          exact one_mem _
        · refine Algebra.subset_adjoin (Or.inr ⟨e.symm ⟨j, hj⟩, ?_⟩)
          simp only [Equiv.apply_symm_apply]
    · rintro _ ⟨k, rfl⟩
      exact ⟨(e k).1, rfl⟩

end GlobalTheory.FlagBundle
