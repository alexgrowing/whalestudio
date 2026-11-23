import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.KawamataViehweg
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineOpenPreimageOfIsPullback
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord
import Development.AbelianVarietyTheory.Definitions.Divisors.SameDiv
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.SpreadOutMorphismStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothProperModelFinitelyGeneratedSubringStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct

namespace GlobalTheory.LogPair

theorem exists_finiteType_subring_ge_finset {k : Type} [CommRing k] (R₀ : Subring k)
    (h : Algebra.FiniteType ℤ R₀) (F : Finset k) :
    ∃ R : Subring k, R₀ ≤ R ∧ (F : Set k) ⊆ R ∧ Algebra.FiniteType ℤ R := by
  have h0 : (subalgebraOfSubring R₀).FG := (Subalgebra.fg_iff_finiteType _).2 h
  have h1 : (subalgebraOfSubring R₀ ⊔ Algebra.adjoin ℤ (F : Set k)).FG :=
    h0.sup (Subalgebra.fg_adjoin_finset F)
  refine ⟨(subalgebraOfSubring R₀ ⊔ Algebra.adjoin ℤ (F : Set k)).toSubring, ?_, ?_,
    (Subalgebra.fg_iff_finiteType _).1 h1⟩
  · intro x hx
    exact (le_sup_left : subalgebraOfSubring R₀ ≤ _) hx
  · intro x hx
    exact (le_sup_right : Algebra.adjoin ℤ (F : Set k) ≤ _) (Algebra.subset_adjoin hx)

theorem exists_model_with_sections : ∀ (k : Type) [Field k] (X : Scheme.{0}) (f : X ⟶ Sp k), Smooth f → IsProper f → ∀ (s : ℕ) (L : Fin s → LB X) (σ : ∀ i, (L i).Sec) (h : ∀ i, (L i).IsLB) (M : LB X) (hM : M.IsLB), ∃ (R : Subring k) (X₁ : Scheme.{0}) (f₁ : X₁ ⟶ Sp R) (π : X ⟶ X₁) (L₁ : Fin s → LB X₁) (σ₁ : ∀ i, (L₁ i).Sec) (h₁ : ∀ i, (L₁ i).IsLB) (M₁ : LB X₁) (hM₁ : M₁.IsLB), Algebra.FiniteType ℤ R ∧ Smooth f₁ ∧ IsProper f₁ ∧ IsPullback π f f₁ (spMap R.subtype) ∧ (∀ i, cls (L i) (h i) = CechPic.pull π (cls (L₁ i) (h₁ i))) ∧ (∀ i, SameDiv (σ i) (Cartier.secPull (σ₁ i) π)) ∧ cls M hM = CechPic.pull π (cls M₁ hM₁) := by
  classical
  intro k _ X f hsm hpr s L σ h M hM
  obtain ⟨R₀, X₀, f₀, π₀, hft, hsm₀, hpr₀, hpb⟩ := GlobalTheory.T.exists_smooth_proper_model_finitelyGenerated_subring k X f hsm hpr
  choose F hF using fun i => GlobalTheory.T.spread_out_line_bundle_section k R₀ X X₀ f f₀ π₀ (L i) (h i) (σ i) hpb
  obtain ⟨G, hG⟩ := GlobalTheory.T.spread_out_line_bundle_section k R₀ X X₀ f f₀ π₀ M hM 0 hpb
  obtain ⟨R, hR, hFR, hRft⟩ :=
    exists_finiteType_subring_ge_finset R₀ hft (G ∪ Finset.univ.biUnion F)
  have hsp : spMap R.subtype ≫ spMap (Subring.inclusion hR) = spMap R₀.subtype := by
    simp only [spMap]
    rw [← Spec.map_comp]
    rfl
  have P := IsPullback.of_hasPullback f₀ (spMap (Subring.inclusion hR))
  let j : X ⟶ pullback f₀ (spMap (Subring.inclusion hR)) :=
    pullback.lift π₀ (f ≫ spMap R.subtype) (by rw [Category.assoc, hsp, hpb.w])
  have hj1 : j ≫ pullback.fst _ _ = π₀ := pullback.lift_fst _ _ _
  have hj2 : j ≫ pullback.snd _ _ = f ≫ spMap R.subtype := pullback.lift_snd _ _ _
  have hGR : (G : Set k) ⊆ R := fun x hx => hFR (by
    simp only [Finset.coe_union, Set.mem_union]; exact Or.inl hx)
  have hFi : ∀ i, (F i : Set k) ⊆ R := fun i x hx => hFR (by
    rw [Finset.mem_coe, Finset.mem_union]
    exact Or.inr (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, hx⟩))
  choose L₁ h₁ σ₁ hc hd using fun i => hF i R hR (hFi i) _ _ _ j P hj1 hj2
  obtain ⟨M₁, hM₁, -, hMc, -⟩ := hG R hR hGR _ _ _ j P hj1 hj2
  refine ⟨R, _, pullback.snd f₀ (spMap (Subring.inclusion hR)), j, L₁, σ₁, h₁, M₁, hM₁, hRft,
    inferInstance, inferInstance, ?_, hc, hd, hMc⟩
  exact IsPullback.of_right (by rw [hj1, hsp]; exact hpb) hj2 P

end GlobalTheory.LogPair
