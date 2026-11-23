import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PowSubSuccLe
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE

set_option autoImplicit false

namespace GlobalTheory.CompanionTheory.GE.Dich

open TopologicalSpace Scheme.IdealSheafData

theorem isReduced_subscheme_of_radical_eq {X : Scheme.{0}} (J : X.IdealSheafData)
    (h : J.radical = J) : IsReduced J.subscheme := by
  have : ∀ U, IsReduced (J.subschemeCover.openCover.X U) := fun U => by
    refine (affine_isReduced_iff (.of (Γ(X, U.1) ⧸ J.ideal U))).mpr ?_
    refine (Ideal.isRadical_iff_quotient_reduced _).mp ?_
    have e : (J.ideal U).radical = J.ideal U := congr($(h).ideal U)
    exact Ideal.radical_eq_iff.mp e
  exact IsReduced.of_openCover _ J.subschemeCover.openCover

theorem irreducibleSpace_subscheme {X : Scheme.{0}} (J : X.IdealSheafData)
    (h : IsIrreducible (J.support : Set X)) : IrreducibleSpace J.subscheme := by
  have hr : Set.range J.subschemeι = (J.support : Set X) := J.range_subschemeι
  have hirr : IsIrreducible (Set.range J.subschemeι) := hr ▸ h
  have : IrreducibleSpace (Set.range J.subschemeι) :=
    { toPreirreducibleSpace := Subtype.preirreducibleSpace hirr.2
      toNonempty := hirr.1.to_subtype }
  exact J.subschemeι.isEmbedding.toHomeomorph.irreducibleSpace_iff.mpr this

theorem exists_radical_pow_le {X : Scheme.{0}} [IsNoetherian X] (J : X.IdealSheafData) :
    ∃ k : ℕ, J.radical ^ k ≤ J := by
  have hU : ∀ U : X.affineOpens, ∃ k : ℕ, (J.ideal U).radical ^ k ≤ J.ideal U := fun U => by
    haveI : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian U
    exact Ideal.exists_radical_pow_le_of_fg _ (IsNoetherian.noetherian _)
  choose k hk using hU
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun U : X.affineOpens => (U.1 : Set X))
    (fun U => U.1.2) (fun x _ => by
      obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
        X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
      exact Set.mem_iUnion.mpr ⟨⟨U, hU⟩, hxU⟩)
  refine ⟨t.sup k, le_of_iSup_eq_top (fun i : t => i.1) ?_ fun i => ?_⟩
  · refine top_le_iff.mp fun x _ => ?_
    obtain ⟨U, hU, hx⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
    exact Opens.mem_iSup.mpr ⟨⟨U, hU⟩, hx⟩
  · change (J.ideal i.1).radical ^ t.sup k ≤ J.ideal i.1
    exact (Ideal.pow_le_pow_right (Finset.le_sup i.2)).trans (hk i.1)

theorem exists_of_radical_ne {X : Scheme.{0}} [IsNoetherian X] (J : X.IdealSheafData)
    (hJ : J ≠ ⊤) (hr : J.radical ≠ J) :
    ∃ J₁ J₂ : X.IdealSheafData, J < J₁ ∧ J < J₂ ∧ ∀ (U : X.affineOpens) (a b : Γ(X, U)),
      a ∈ J₁.ideal U → b ∈ J₂.ideal U → a * b ∈ J.ideal U := by
  classical
  have hex := exists_radical_pow_le J
  obtain ⟨m, hm₁, hm₂⟩ : ∃ m, J.radical ^ (m + 1) ≤ J ∧ ¬ J.radical ^ m ≤ J := by
    rcases Nat.eq_zero_or_pos (Nat.find hex) with hk | hk
    · have hs := Nat.find_spec hex
      rw [hk, pow_zero] at hs
      exact absurd (top_le_iff.mp hs) hJ
    · refine ⟨Nat.find hex - 1, ?_, Nat.find_min hex (by omega)⟩
      rw [Nat.sub_add_cancel hk]
      exact Nat.find_spec hex
  refine ⟨J.radical, J ⊔ J.radical ^ m, lt_of_le_of_ne J.le_radical hr.symm,
    left_lt_sup.mpr hm₂, fun U a b ha hb => ?_⟩
  have hle : J.radical.ideal U * (J ⊔ J.radical ^ m).ideal U ≤ J.ideal U := by
    change J.radical.ideal U * (J.ideal U ⊔ (J.radical.ideal U) ^ m) ≤ J.ideal U
    rw [Ideal.mul_sup]
    refine sup_le Ideal.mul_le_right ?_
    rw [← pow_succ']
    exact hm₁ U
  exact hle (Ideal.mul_mem_mul ha hb)

theorem exists_of_not_preirreducible {X : Scheme.{0}} (J : X.IdealSheafData)
    (hr : J.radical = J) (hirr : ¬ IsPreirreducible (J.support : Set X)) :
    ∃ J₁ J₂ : X.IdealSheafData, J < J₁ ∧ J < J₂ ∧ ∀ (U : X.affineOpens) (a b : Γ(X, U)),
      a ∈ J₁.ideal U → b ∈ J₂.ideal U → a * b ∈ J.ideal U := by
  rw [isPreirreducible_iff_isClosed_union_isClosed] at hirr
  push_neg at hirr
  obtain ⟨Z₁, Z₂, h₁, h₂, hcov, hn₁, hn₂⟩ := hirr
  let C₁ : Closeds X := J.support ⊓ ⟨Z₁, h₁⟩
  let C₂ : Closeds X := J.support ⊓ ⟨Z₂, h₂⟩
  have hsup : C₁ ⊔ C₂ = J.support := by
    apply le_antisymm (sup_le inf_le_left inf_le_left)
    intro x hx
    rcases hcov hx with h | h
    · exact Or.inl ⟨hx, h⟩
    · exact Or.inr ⟨hx, h⟩
  have hlt : ∀ (C : Closeds X) (Z : Set X), C ≤ J.support → (C : Set X) ⊆ Z →
      ¬ (J.support : Set X) ⊆ Z → J < vanishingIdeal C := by
    intro C Z hC hCZ hn
    refine lt_of_le_not_ge (le_support_iff_le_vanishingIdeal.mp hC) fun hle => hn ?_
    intro x hx
    have hx' : x ∈ ((vanishingIdeal C).support : Set X) := support_antitone hle hx
    rw [coe_support_vanishingIdeal] at hx'
    exact hCZ hx'
  refine ⟨vanishingIdeal C₁, vanishingIdeal C₂, hlt C₁ Z₁ inf_le_left (fun x hx => hx.2) hn₁,
    hlt C₂ Z₂ inf_le_left (fun x hx => hx.2) hn₂, fun U a b ha hb => ?_⟩
  have e : vanishingIdeal C₁ ⊓ vanishingIdeal C₂ = J := by
    rw [← vanishingIdeal_sup, hsup, vanishingIdeal_support, hr]
  have hm : a * b ∈ (vanishingIdeal C₁ ⊓ vanishingIdeal C₂).ideal U :=
    ⟨Ideal.mul_mem_right _ _ ha, Ideal.mul_mem_left _ _ hb⟩
  rwa [e] at hm

theorem isIntegral_or_exists_mul_mem : ∀ {X : Scheme.{0}} [IsNoetherian X] (J : X.IdealSheafData),
    J ≠ ⊤ → IsIntegral J.subscheme ∨ ∃ J₁ J₂ : X.IdealSheafData, J < J₁ ∧ J < J₂ ∧
      ∀ (U : X.affineOpens) (a b : Γ(X, U)), a ∈ J₁.ideal U → b ∈ J₂.ideal U →
        a * b ∈ J.ideal U := by
  intro X _ J hJ
  by_cases hr : J.radical = J
  · by_cases hirr : IsPreirreducible (J.support : Set X)
    · left
      have hne : (J.support : Set X).Nonempty := by
        rw [Set.nonempty_iff_ne_empty]
        intro h
        exact hJ (J.support_eq_bot_iff.mp (SetLike.coe_injective h))
      haveI := isReduced_subscheme_of_radical_eq J hr
      haveI := irreducibleSpace_subscheme J ⟨hne, hirr⟩
      exact isIntegral_of_irreducibleSpace_of_isReduced _
    · exact Or.inr (exists_of_not_preirreducible J hr hirr)
  · exact Or.inr (exists_of_radical_ne J hJ hr)

end GlobalTheory.CompanionTheory.GE.Dich
