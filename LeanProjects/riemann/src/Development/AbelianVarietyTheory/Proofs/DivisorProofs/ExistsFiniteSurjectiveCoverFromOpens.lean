import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UOver
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.ZH GlobalTheory.UPoinc GlobalTheory.UCovSep
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FinCover

theorem exists_finite_union {X : Scheme.{0}} {T : Type} (N : T → Scheme.{0}) (p : ∀ t, N t ⟶ X)
    (hp : ∀ t, IsFinite (p t)) (S : Finset T) :
    ∃ (Y : Scheme.{0}) (q : Y ⟶ X), IsFinite q ∧ (∀ t ∈ S, Set.range (p t) ⊆ Set.range q) ∧
      ∀ (K : Type) [Field K] (y' : Sp K ⟶ Y), ∃ (t : T) (z : Sp K ⟶ N t), z ≫ p t = y' ≫ q := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    refine ⟨∅, Scheme.emptyTo X, inferInstance, by simp, fun K _ y' => ?_⟩
    exact (show PEmpty from y' (closedPoint K)).elim
  | insert a S _ ih =>
    obtain ⟨Y, q, hq, hr, hK⟩ := ih
    have := hp a
    refine ⟨N a ⨿ Y, coprod.desc (p a) q, inferInstance, fun t ht => ?_, fun K _ y' => ?_⟩
    · rintro _ ⟨x, rfl⟩
      rcases Finset.mem_insert.1 ht with rfl | ht
      · exact ⟨(coprod.inl : N t ⟶ N t ⨿ Y) x, by rw [← Scheme.Hom.comp_apply, coprod.inl_desc]⟩
      · obtain ⟨y, hy⟩ := hr t ht ⟨x, rfl⟩
        exact ⟨(coprod.inr : Y ⟶ N a ⨿ Y) y, by rw [← Scheme.Hom.comp_apply, coprod.inr_desc, hy]⟩
    · have hsub : ∀ x : Sp K, x = closedPoint K := fun x =>
        Subsingleton.elim (α := PrimeSpectrum K) _ _
      have hc := (isCompl_range_inl_inr (N a) Y).sup_eq_top
      have hm : y' (closedPoint K) ∈ Set.range (coprod.inl : N a ⟶ N a ⨿ Y) ∪
          Set.range (coprod.inr : Y ⟶ N a ⨿ Y) := by
        have h : y' (closedPoint K) ∈ (⊤ : Set (N a ⨿ Y : Scheme.{0})) := trivial
        rw [← hc] at h
        exact h
      rcases hm with hm | hm
      · have hs : Set.range y' ⊆ Set.range (coprod.inl : N a ⟶ N a ⨿ Y) := by
          rintro _ ⟨x, rfl⟩; rw [hsub x]; exact hm
        refine ⟨a, IsOpenImmersion.lift _ y' hs, ?_⟩
        conv_rhs => rw [← IsOpenImmersion.lift_fac _ y' hs]
        rw [Category.assoc, coprod.inl_desc]
      · have hs : Set.range y' ⊆ Set.range (coprod.inr : Y ⟶ N a ⨿ Y) := by
          rintro _ ⟨x, rfl⟩; rw [hsub x]; exact hm
        obtain ⟨t, z, hz⟩ := hK K (IsOpenImmersion.lift _ y' hs)
        refine ⟨t, z, ?_⟩
        conv_rhs => rw [← IsOpenImmersion.lift_fac _ y' hs]
        rw [Category.assoc, coprod.inr_desc, hz]

theorem exists_finite_surjective_cover : ∀ (X Z : Scheme.{0}) (i : X ⟶ Z) (T : Type) [Finite T] (M : T → Scheme.{0}) (U : T → Z.Opens) (g : ∀ t, M t ⟶ (U t).toScheme), (∀ t, IsFinite (g t)) → (∀ t, Set.range i ⊆ (U t : Set Z)) → (∀ x : X, ∃ (t : T) (w : M t), (g t ≫ (U t).ι) w ⤳ i x) → ∃ (Y : Scheme.{0}) (q : Y ⟶ X), IsFinite q ∧ Surjective q ∧ ∀ (K : Type) [Field K] (y' : Sp K ⟶ Y), ∃ (t : T) (yM : Sp K ⟶ M t), yM ≫ g t ≫ (U t).ι = y' ≫ q ≫ i := by
  intro X Z i T _ M U g hg hU hx
  have hU' : ∀ t, Set.range i ⊆ Set.range (U t).ι := fun t => by
    rw [Scheme.Opens.range_ι]; exact hU t
  have := Fintype.ofFinite T
  let i' : ∀ t, X ⟶ (U t).toScheme := fun t => IsOpenImmersion.lift (U t).ι i (hU' t)
  have hi' : ∀ t, i' t ≫ (U t).ι = i := fun t => IsOpenImmersion.lift_fac _ _ _
  obtain ⟨Y, q, hq, hr, hK⟩ := exists_finite_union (fun t => pullback (g t) (i' t))
    (fun t => pullback.snd (g t) (i' t)) (fun t => by have := hg t; infer_instance) Finset.univ
  refine ⟨Y, q, hq, ⟨fun x => ?_⟩, fun K _ y' => ?_⟩
  · obtain ⟨t, w, hw⟩ := hx x
    have := hg t
    refine hr t (Finset.mem_univ t) ?_
    rw [Scheme.Pullback.range_snd]
    rw [← hi' t, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply,
      (U t).ι.isOpenEmbedding.isInducing.specializes_iff] at hw
    exact hw.mem_closed (g t).isClosedMap.isClosed_range ⟨w, rfl⟩
  · obtain ⟨t, z, hz⟩ := hK K y'
    refine ⟨t, z ≫ pullback.fst (g t) (i' t), ?_⟩
    rw [Category.assoc, pullback.condition_assoc, hi' t, ← Category.assoc, hz, Category.assoc]

end GlobalTheory.FinCover
