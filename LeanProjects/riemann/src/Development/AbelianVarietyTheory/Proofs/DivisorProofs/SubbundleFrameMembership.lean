import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory
open GlobalTheory.QCoh (freeModule)
open GlobalTheory.Twist (resM)

namespace GlobalTheory.VB

theorem sum_smul_frame_mem_ofStalks_iff : ∀ {X : Scheme.{0}} {F : X.Modules} {U : X.Opens} {N : ℕ} (c : Fin N → Γ(F, U)), VB.IsFrame c → ∀ (S : ∀ x : X, Submodule (X.presheaf.stalk x) (F.presheaf.stalk x :)) (l : ℕ), (∀ (y : X) (hy : y ∈ U), S y = Submodule.span _ {v | ∃ j : Fin N, (j : ℕ) < l ∧ v = F.presheaf.germ U y hy (c j)}) → ∀ {V : X.Opens} (h : V ≤ U) (a : Fin N → Γ(X, V)), (∑ j, a j • resM F h (c j)) ∈ (VB.Sub.ofStalks S).sec V ↔ ∀ j : Fin N, l ≤ (j : ℕ) → a j = 0 := by
  intro X F U N c hc S l hS V h a
  have hg : ∀ (y : X) (hy : y ∈ V), F.presheaf.germ V y hy (∑ j, a j • resM F h (c j)) =
      ∑ j, X.presheaf.germ V y hy (a j) • hc.stalkBasis y (h hy) j := by
    intro y hy
    simp only [map_sum, QCoh.germ_smul, Twist.germ_resM, IsFrame.stalkBasis_apply]
  have hset : ∀ (y : X) (hy : y ∈ U),
      {v | ∃ j : Fin N, (j : ℕ) < l ∧ v = F.presheaf.germ U y hy (c j)} =
        hc.stalkBasis y hy '' {j : Fin N | (j : ℕ) < l} := by
    intro y hy
    ext v
    simp only [Set.mem_setOf_eq, Set.mem_image, IsFrame.stalkBasis_apply]
    exact ⟨fun ⟨j, h1, h2⟩ => ⟨j, h1, h2.symm⟩, fun ⟨j, h1, h2⟩ => ⟨j, h1, h2.symm⟩⟩
  change (∀ (y : X) (hy : y ∈ V), F.presheaf.germ V y hy (∑ j, a j • resM F h (c j)) ∈ S y) ↔ _
  constructor
  · intro H j hj
    refine TopCat.Presheaf.section_ext X.sheaf V _ _ fun y hy => ?_
    have H1 := H y hy
    rw [hg y hy, hS y (h hy), hset y (h hy), Module.Basis.mem_span_image] at H1
    have h0 : (hc.stalkBasis y (h hy)).repr
        (∑ j, X.presheaf.germ V y hy (a j) • hc.stalkBasis y (h hy) j) j = 0 := by
      by_contra hne
      have := H1 (Finset.mem_coe.2 (Finsupp.mem_support_iff.2 hne))
      exact absurd this (not_lt.2 hj)
    rw [congrFun ((hc.stalkBasis y (h hy)).repr_sum_self _) j] at h0
    exact h0.trans (map_zero (X.presheaf.germ V y hy).hom).symm
  · intro H y hy
    rw [hg y hy, hS y (h hy), hset y (h hy)]
    refine Submodule.sum_mem _ fun j _ => ?_
    by_cases hj : (j : ℕ) < l
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, hj, rfl⟩)
    · rw [H j (not_lt.1 hj), map_zero, zero_smul]
      exact Submodule.zero_mem _

end GlobalTheory.VB
