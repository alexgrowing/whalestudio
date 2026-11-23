import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite

open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.GlueStalk

theorem isDominant_fromSpecStalk_of_isIntegral (X : Scheme.{0}) [IsIntegral X] (x : X) :
    IsDominant (X.fromSpecStalk x) := by
  refine ⟨?_⟩
  have h : genericPoint X ∈ Set.range (X.fromSpecStalk x) := by
    rw [Scheme.range_fromSpecStalk]
    exact (genericPoint_spec X).specializes trivial
  have h2 : Dense ({genericPoint X} : Set X) := by
    rw [dense_iff_closure_eq]; exact genericPoint_spec X
  exact h2.mono (Set.singleton_subset_iff.2 h)

theorem fromSpecStalk_generic {T S P : Scheme.{0}} (h : ∀ x : T, Spec (T.presheaf.stalk x) ⟶ S)
    (H : ∀ (x ξ : T) (e : ξ ⤳ x), (∀ y, y ⤳ ξ → y = ξ) → Spec.map (T.presheaf.stalkSpecializes e) ≫ h x = h ξ)
    (V : T.Opens) [IsIntegral V] {x : T} (hx : x ∈ V) (f : V.toScheme ⟶ S)
    (hf : V.fromSpecStalkOfMem x hx ≫ f = h x) [IsIntegral P] (j : P ⟶ V) (k : P ⟶ T) [IsOpenImmersion k]
    (hk : j ≫ V.ι = k) :
    P.fromSpecStalk (genericPoint P) ≫ j ≫ f =
      Spec.map (k.stalkMap (genericPoint P)) ≫ h (k (genericPoint P)) := by
  have hmax : ∀ y, y ⤳ k (genericPoint P) → y = k (genericPoint P) := fun y hy => by
    obtain ⟨p, rfl⟩ : y ∈ Set.range k := hy.mem_open k.isOpenEmbedding.isOpen_range ⟨_, rfl⟩
    exact (hy.antisymm (((genericPoint_spec P).specializes trivial).map k.continuous)).eq
  have e₀ : V.ι (genericPoint V) = k (genericPoint P) := hmax _ (by
    rw [← hk, Scheme.Hom.comp_apply]
    exact ((genericPoint_spec V).specializes trivial).map V.ι.continuous)
  have e : k (genericPoint P) ⤳ x := by
    rw [← e₀]
    exact ((genericPoint_spec V).specializes (y := (⟨x, hx⟩ : V)) trivial).map V.ι.continuous
  rw [← H x _ e hmax, ← hf, ← Category.assoc, ← Category.assoc, ← Category.assoc]
  congr 1
  rw [← cancel_mono V.ι, Category.assoc, hk, Category.assoc, Category.assoc,
    Scheme.Opens.fromSpecStalkOfMem_ι, Scheme.SpecMap_stalkSpecializes_fromSpecStalk,
    Scheme.SpecMap_stalkMap_fromSpecStalk]

theorem exists_glue_of_stalks : ∀ (B T S : Scheme.{0}) (t : T ⟶ B) (s : S ⟶ B) (h : ∀ x : T, Spec (T.presheaf.stalk x) ⟶ S), LocallyOfFiniteType s → IsSeparated s → IsLocallyNoetherian T → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme T → (∀ x, h x ≫ s = T.fromSpecStalk x ≫ t) → (∀ (x ξ : T) (e : ξ ⤳ x), (∀ y, y ⤳ ξ → y = ξ) → Spec.map (T.presheaf.stalkSpecializes e) ≫ h x = h ξ) → ∃ g : T ⟶ S, ∀ x, T.fromSpecStalk x ≫ g = h x := by
  intro B T S t s h _ _ _ hn hs H
  have : GlobalTheory.IsNormalScheme T := GlobalTheory.IsNormalScheme.of_pred hn
  have loc : ∀ x : T, ∃ (V : T.Opens) (hx : x ∈ V) (f : V.toScheme ⟶ S), IsIntegral V ∧
      V.fromSpecStalkOfMem x hx ≫ f = h x ∧ f ≫ s = V.ι ≫ t := fun x => by
    obtain ⟨U, hU, f, h₁, h₂⟩ := spread_out_of_isGermInjective' t s (h x) (hs x)
    let Z : irreducibleComponents T := ⟨_, irreducibleComponent_mem_irreducibleComponents x⟩
    have hx : x ∈ U ⊓ GlobalTheory.IsNormalScheme.component Z := ⟨hU, mem_irreducibleComponent⟩
    have : Nonempty (U ⊓ GlobalTheory.IsNormalScheme.component Z).toScheme := ⟨⟨x, hx⟩⟩
    refine ⟨_, hx, T.homOfLE inf_le_left ≫ f, isIntegral_of_isOpenImmersion (T.homOfLE inf_le_right), ?_, ?_⟩
    · rw [h₁, ← Category.assoc]
      congr 1
      rw [← cancel_mono U.ι, Category.assoc, Scheme.homOfLE_ι, Scheme.Opens.fromSpecStalkOfMem_ι,
        Scheme.Opens.fromSpecStalkOfMem_ι]
    · rw [Category.assoc, h₂, Scheme.homOfLE_ι_assoc]
  choose V hx f hi h₁ h₂ using loc
  have hc : ⨆ x, V x = ⊤ := top_le_iff.1 fun x _ => TopologicalSpace.Opens.mem_iSup.2 ⟨x, hx x⟩
  have key : ∀ x y, pullback.fst (V x).ι (V y).ι ≫ f x = pullback.snd (V x).ι (V y).ι ≫ f y := fun x y => by
    have := hi x
    have := hi y
    cases isEmpty_or_nonempty ↥(pullback (V x).ι (V y).ι) with
    | inl _ => exact (isInitialOfIsEmpty (X := pullback (V x).ι (V y).ι)).hom_ext _ _
    | inr _ =>
      have : IsIntegral (pullback (V x).ι (V y).ι) := isIntegral_of_isOpenImmersion (pullback.fst (V x).ι (V y).ι)
      have := isDominant_fromSpecStalk_of_isIntegral _ (genericPoint ↥(pullback (V x).ι (V y).ι))
      refine ext_of_isDominant_of_isSeparated s ?_
        ((pullback (V x).ι (V y).ι).fromSpecStalk (genericPoint _)) ?_
      · rw [Category.assoc, Category.assoc, h₂, h₂, pullback.condition_assoc]
      · exact (fromSpecStalk_generic h H (V x) (hx x) (f x) (h₁ x) _ _ rfl).trans
          (fromSpecStalk_generic h H (V y) (hx y) (f y) (h₁ y) _ _ pullback.condition.symm).symm
  refine ⟨(T.openCoverOfIsOpenCover V hc).glueMorphisms f key, fun x => ?_⟩
  rw [← Scheme.Opens.fromSpecStalkOfMem_ι (V x) x (hx x), Category.assoc, ← h₁ x]
  exact congrArg (_ ≫ ·) (Scheme.Cover.ι_glueMorphisms (T.openCoverOfIsOpenCover V hc) f key x)

end GlobalTheory.GlueStalk
