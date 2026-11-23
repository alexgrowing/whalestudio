import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsRingHomComplexCompEqOfCountableStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelPrincipalObjectDescendsLargeSubfieldStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsSharpDescends
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsMonHomLift
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaLevelObjectDescendsFgSubfieldStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaLevelPullbackIdCompCancelStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaLevelAbelianSchemePullbackStatement
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.SharpFrom

private theorem countable_closure {K : Type} [Field K] (s : Set K) (hs : s.Countable) :
    Countable (Subfield.closure s) := by
  have hs' : Cardinal.mk s ≤ Cardinal.aleph0 := Cardinal.mk_le_aleph0_iff.2 hs.to_subtype
  rw [← Cardinal.mk_le_aleph0_iff]
  exact (Subfield.cardinalMk_closure_le_max s).trans (max_le hs' le_rfl)

private theorem countable_closure_union {K : Type} [Field K] (K₀ : Subfield K) [Countable K₀] (F : Finset K) :
    Countable (Subfield.closure ((K₀ : Set K) ∪ F)) := by
  have h₀ : (K₀ : Set K).Countable := Set.countable_coe_iff.1 ‹Countable K₀›
  exact countable_closure _ (h₀.union F.countable_toSet)

private theorem countable_of_finiteType (o : Type) [CommRing o] (h : Algebra.FiniteType ℤ o) : Countable o := by
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.1 h
  have hP : Countable (MvPolynomial (Fin n) ℤ) := by
    rw [← Cardinal.mk_le_aleph0_iff]
    exact MvPolynomial.cardinalMk_le_max.trans
      (sup_le (sup_le Cardinal.mk_le_aleph0 Cardinal.mk_le_aleph0) le_rfl)
  exact hf.countable

private theorem sp_comp {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R →+* R') (f' : R' →+* R'') :
    spMap f' ≫ spMap f = spMap (f'.comp f) := by
  simp only [spMap, ← Spec.map_comp]
  rfl

private theorem exists_sp {R R' : Type} [CommRing R] [CommRing R'] (y : Sp R' ⟶ Sp R) : ∃ f : R →+* R', y = spMap f := ⟨Spec.preimage y |>.hom, by simp [spMap]⟩

theorem fromC_sharpClass : Out.Laws → Out.Laws2 → ∀ (h g : ℕ) (W : Matrix (Fin 8) (Fin 8) ℤ) (J : Type) [Finite J] (a : J → Matrix (Fin 8) (Fin 8) ℤ) (w w' : J) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ))), IsE8 W → IsSharpBasis W bas → (W + W.transpose) * a w = W → (W + W.transpose) * a w' = W.transpose → (∀ u v, ∃ j, a j = Matrix.single u v 1) → ∀ (N' : ℕ) (o : Type) [CommRing o] (b : TBase o (N' ^ 2)) (em : o →+* ℂ), ArBase em → ∀ (S : Scheme.{0}) (s : S ⟶ Sp o) (t : TObj g (N' ^ 2) J b s) (c : SiegPre h (N' ^ 2) (b.ζ : o) s), c.Principal → IsSharp W a bas t c → ∀ (K : Type) [Field K] [CharZero K] (x : Sp K ⟶ S), FromC em (SharpClass (b := b) W a bas em) t x := by
  intro _ _ h g W J _ a _ _ bas _ _ _ _ _ N' o _ b em hem S s t c hc hsh K _ _ x
  obtain ⟨hded, hft, hinj⟩ := hem
  have : Countable o := countable_of_finiteType o hft

  obtain ⟨βK, hβK⟩ := exists_sp (x ≫ s)
  obtain ⟨tK, htK⟩ := GlobalTheory.T.exists_thetaLevelAbelianScheme_pullback o g (N' ^ 2) J b S (Sp K) s (spMap βK) x t hβK
  obtain ⟨cK, hcK, hshK⟩ := GlobalTheory.SharpPull.sharp_pull h g (N' ^ 2) W J a bas o b S (Sp K) s (spMap βK) x t tK c
    hβK htK hc hsh

  obtain ⟨K₀, β₀, t₀, hβ₀, hcount, -, ht₀⟩ := GlobalTheory.T.thetaLevel_object_descends_fg_subfield o g (N' ^ 2) J b K βK tK
  subst hβ₀
  have : Countable K₀ := hcount ‹_›
  obtain ⟨F, hF⟩ := GlobalTheory.T.siegel_principal_object_descends_large_subfield h (N' ^ 2) o (b.ζ : o) K K₀ (spMap β₀) (spMap (K₀.subtype.comp β₀)) cK
    (sp_comp _ _).symm hcK

  have hK : K₀ ≤ Subfield.closure ((K₀ : Set K) ∪ F) := fun z hz => Subfield.subset_closure (Or.inl hz)
  have hFK : (F : Set K) ⊆ Subfield.closure ((K₀ : Set K) ∪ F) := fun z hz => Subfield.subset_closure (Or.inr hz)
  obtain ⟨c₁, hc₁, hpb₁⟩ := hF _ hK hFK
  have : Countable (Subfield.closure ((K₀ : Set K) ∪ F)) := countable_closure_union K₀ F
  have move : ∀ s₁ : Sp (Subfield.closure ((K₀ : Set K) ∪ F)) ⟶ Sp o,
      s₁ = spMap ((Subfield.inclusion hK).comp β₀) → ∀ c₁ : SiegPre h (N' ^ 2) (b.ζ : o) s₁, c₁.Principal →
      SiegPB cK c₁ (spMap (Subfield.closure ((K₀ : Set K) ∪ F)).subtype) →
      ∃ c₂ : SiegPre h (N' ^ 2) (b.ζ : o) (spMap ((Subfield.inclusion hK).comp β₀)),
        c₂.Principal ∧ SiegPB cK c₂ (spMap (Subfield.closure ((K₀ : Set K) ∪ F)).subtype) := by
    rintro s₁ rfl c₂ h₁ h₂
    exact ⟨c₂, h₁, h₂⟩
  obtain ⟨c₁', hc₁', hpb₁'⟩ := move _ (sp_comp _ _) c₁ hc₁ hpb₁
  obtain ⟨t₁, ht₁⟩ := GlobalTheory.T.exists_thetaLevelAbelianScheme_pullback o g (N' ^ 2) J b (Sp K₀) (Sp (Subfield.closure ((K₀ : Set K) ∪ F)))
    (spMap β₀) (spMap ((Subfield.inclusion hK).comp β₀)) (spMap (Subfield.inclusion hK)) t₀ (sp_comp _ _)
  have hsub : (Subfield.closure ((K₀ : Set K) ∪ F)).subtype.comp (Subfield.inclusion hK) = K₀.subtype :=
    RingHom.ext fun _ => rfl
  have htK₁ : TMap tK t₁ (spMap (Subfield.closure ((K₀ : Set K) ∪ F)).subtype) := by
    refine ((GlobalTheory.T.thetaLevelPullback_id_comp_cancel o g (N' ^ 2) J b (Sp K₀) _ (Sp K) (spMap β₀) _ (spMap (K₀.subtype.comp β₀))
      t₀ t₁ tK).2 _ _ ht₁).2 ?_
    rw [sp_comp, hsub]
    exact ht₀
  have e₁ : spMap (K₀.subtype.comp β₀) =
      spMap (Subfield.closure ((K₀ : Set K) ∪ F)).subtype ≫ spMap ((Subfield.inclusion hK).comp β₀) := by
    rw [sp_comp]
    exact congrArg spMap (RingHom.ext fun _ => rfl)

  obtain ⟨F₂, β₂, t₂, c₂, e₂, ht₂, hc₂, hsh₂⟩ := GlobalTheory.SharpDescent.isSharp_descends h g (N' ^ 2) W J a bas o b K
    (Subfield.closure ((K₀ : Set K) ∪ F)) ((Subfield.inclusion hK).comp β₀) (spMap (K₀.subtype.comp β₀))
    tK cK t₁ c₁' e₁ htK₁ hpb₁' hc₁' hshK
  have : Countable (Subfield.closure ((Subfield.closure ((K₀ : Set K) ∪ F) : Set K) ∪ F₂)) :=
    countable_closure_union _ F₂

  obtain ⟨-, j, hj⟩ := GlobalTheory.T.exists_ringHom_complex_comp_eq_of_countable_field o em _ β₂ hded hft hinj
  have ej : spMap j ≫ spMap β₂ = spMap em := by rw [sp_comp, hj]
  obtain ⟨tc, htc⟩ := GlobalTheory.T.exists_thetaLevelAbelianScheme_pullback o g (N' ^ 2) J b _ (Sp ℂ) (spMap β₂) (spMap em) (spMap j) t₂ ej
  obtain ⟨cc, hcc, hshc⟩ := GlobalTheory.SharpPull.sharp_pull h g (N' ^ 2) W J a bas o b _ (Sp ℂ) (spMap β₂) (spMap em)
    (spMap j) t₂ tc c₂ ej htc hc₂ hsh₂

  obtain ⟨tx, htx⟩ := GlobalTheory.T.exists_thetaLevelAbelianScheme_pullback o g (N' ^ 2) J b S (Sp K) s (x ≫ s) x t rfl
  have htxK : TMap tx tK (𝟙 _) :=
    ((GlobalTheory.T.thetaLevelPullback_id_comp_cancel o g (N' ^ 2) J b S (Sp K) (Sp K) s _ _ t tK tx).2 x (𝟙 _) htK).2 (by rwa [Category.id_comp])
  have htx₂ : TMap tx t₂ (spMap (Subfield.subtype _)) := by
    have := ((GlobalTheory.T.thetaLevelPullback_id_comp_cancel o g (N' ^ 2) J b _ (Sp K) (Sp K) (spMap β₂) _ (x ≫ s) t₂ tK tx).2 _ (𝟙 _) ht₂).1 htxK
    rwa [Category.id_comp] at this
  exact ⟨_, inferInstance, β₂, Subfield.subtype _, j, t₂, tx, tc, hj, hβK.trans e₂, htx, htx₂, htc, cc, hcc, hshc⟩

end GlobalTheory.SharpFrom
