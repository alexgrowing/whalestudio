import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.BaseIdealIdeal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraiseOfIsImmersionProjectiveCompleteNoethStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChowLemmaProjectiveModificationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraisationOfProperModificationNoetherianStepStatement

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FormalAlg

theorem subsingleton_idealSheafData_of_isEmpty (W : Scheme.{0}) [IsEmpty W] :
    Subsingleton W.IdealSheafData := by
  constructor
  intro a b
  apply Scheme.IdealSheafData.ext
  funext U
  exact Subsingleton.elim _ _

theorem alg_of_isEmpty {R : Type} [CommRing R] {W : Scheme.{0}} [IsEmpty W]
    (f : W ⟶ Spec (CommRingCat.of R)) (I : Ideal R) : Alg f I := by
  have := subsingleton_idealSheafData_of_isEmpty W
  intro t _ hp
  exact ⟨t 0, hp 0, fun _ => Subsingleton.elim _ _⟩

theorem alg_of_isSeparated : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), IsAdicComplete I R →
    ∀ (W : Scheme.{0}) (f : W ⟶ Spec (CommRingCat.of R)), IsSeparated f → LocallyOfFiniteType f →
      QuasiCompact f → Alg f I := by
  intro R _ _ I hI W₀ f₀ hsep hlft hqc
  have : IsLocallyNoetherian W₀ := LocallyOfFiniteType.isLocallyNoetherian f₀
  have : CompactSpace W₀ := QuasiCompact.compactSpace_of_compactSpace f₀
  have : AlgebraicGeometry.IsNoetherian W₀ := {}
  suffices H : ∀ Z : TopologicalSpace.Closeds W₀, ∀ (W : Scheme.{0}) (i : W ⟶ W₀), IsClosedImmersion i →
      Set.range i ⊆ (Z : Set W₀) → Alg (i ≫ f₀) I by
    simpa using H ⊤ W₀ (𝟙 _) inferInstance (by simp)
  intro Z
  induction Z using WellFoundedLT.induction with
  | _ Z ih =>
  intro W i hi hZ
  have hsep' : IsSeparated (i ≫ f₀) := inferInstance
  have hlft' : LocallyOfFiniteType (i ≫ f₀) := inferInstance
  have hqc' : QuasiCompact (i ≫ f₀) := inferInstance
  by_cases hW : Nonempty W
  · obtain ⟨W', P, π, q, s, U, hπ, hU, hiso, hs, hq, hcomm⟩ :=
      GlobalTheory.T.chow_lemma_projective_modification R W (i ≫ f₀) hsep' hlft' hqc' hW
    have hA : Alg (π ≫ i ≫ f₀) I := by
      rw [← hcomm]
      exact GlobalTheory.T.algebraise_of_isImmersion_projective_completeNoeth R I hI W' P q s hs hq
    let K := Scheme.IdealSheafData.vanishingIdeal
      (⟨(U : Set W)ᶜ, U.isOpen.isClosed_compl⟩ : TopologicalSpace.Closeds W)
    have hK : ((K.support : Set W)) = (U : Set W)ᶜ := Scheme.IdealSheafData.coe_support_vanishingIdeal _
    refine GlobalTheory.T.algebraisation_of_proper_modification_noetherian_step R I W (i ≫ f₀) hsep' hlft' hqc' W' π U hπ hiso K ?_ hA ?_
    · intro x hx
      by_contra hxU
      apply hx
      rw [← SetLike.mem_coe, hK]
      exact hxU
    · intro k
      let Z' : TopologicalSpace.Closeds W₀ :=
        ⟨i '' (U : Set W)ᶜ, i.isClosedEmbedding.isClosedMap _ U.isOpen.isClosed_compl⟩
      have hlt : Z' < Z := by
        refine lt_of_le_of_ne ?_ ?_
        · rintro y ⟨x, _, rfl⟩
          exact hZ ⟨x, rfl⟩
        · intro heq
          obtain ⟨u, hu⟩ := hU
          have h1 : i u ∈ (Z : Set W₀) := hZ ⟨u, rfl⟩
          rw [← heq] at h1
          obtain ⟨x, hx, hxu⟩ := h1
          exact hx (i.isClosedEmbedding.injective hxu ▸ hu)
      have h2 := ih Z' hlt _ ((K ^ k).subschemeι ≫ i) inferInstance (by
        rintro _ ⟨x, rfl⟩
        refine ⟨(K ^ k).subschemeι x, ?_, rfl⟩
        have hsub : ((K ^ k).support : Set W) ⊆ (U : Set W)ᶜ := by
          rcases Nat.eq_zero_or_pos k with rfl | hk
          · rw [pow_zero, Scheme.IdealSheafData.one_eq_top, Scheme.IdealSheafData.support_top]
            intro y hy
            exact hy.elim
          · rw [Scheme.IdealSheafData.support_pow _ _ hk.ne', hK]
        apply hsub
        rw [← Scheme.IdealSheafData.range_subschemeι]
        exact ⟨x, rfl⟩)
      rwa [Category.assoc] at h2
  · have : IsEmpty W := not_nonempty_iff.1 hW
    exact alg_of_isEmpty _ I

end GlobalTheory.FormalAlg
