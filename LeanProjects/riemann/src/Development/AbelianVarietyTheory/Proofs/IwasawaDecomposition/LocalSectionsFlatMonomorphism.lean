import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMorphismOfStalkMaps

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Models GlobalTheory.TorRef

namespace GlobalTheory.GlueDense

theorem ext_of_fromSpecStalk {X Y Z : Scheme.{0}} [IsReduced X] (s : Y ⟶ Z) [IsSeparated s] {f g : X ⟶ Y}
    (h : f ≫ s = g ≫ s) (P : Set X) (hP : ∀ x : X, ∃ p ∈ P, p ⤳ x)
    (hU : ∀ p ∈ P, X.fromSpecStalk p ≫ f = X.fromSpecStalk p ≫ g) : f = g := by
  let ι : (∐ fun p : P => Spec (X.presheaf.stalk p.1)) ⟶ X := Sigma.desc fun p => X.fromSpecStalk p.1
  have hι : ∀ p : P, Sigma.ι (fun p : P => Spec (X.presheaf.stalk p.1)) p ≫ ι = X.fromSpecStalk p.1 :=
    fun p => Sigma.ι_desc _ _
  have : IsDominant ι := by
    refine ⟨?_⟩
    intro x
    obtain ⟨p, hp, e⟩ := hP x
    have hr : p ∈ Set.range ι := by
      have hr' : p ∈ Set.range (X.fromSpecStalk p) := by
        rw [Scheme.range_fromSpecStalk]; exact specializes_rfl
      obtain ⟨a, ha⟩ := hr'
      refine ⟨Sigma.ι (fun p : P => Spec (X.presheaf.stalk p.1)) ⟨p, hp⟩ a, ?_⟩
      rw [← Scheme.Hom.comp_apply, hι, ha]
    exact e.mem_closed isClosed_closure (subset_closure hr)
  exact ext_of_isDominant_of_isSeparated s h ι (Sigma.hom_ext _ _ fun p => by
    rw [← Category.assoc, ← Category.assoc, hι]; exact hU _ p.2)

theorem eq_of_specializes_of_isDomain {T : Scheme.{0}} {x ξ p : T} [IsDomain (T.presheaf.stalk x)]
    (e₁ : ξ ⤳ x) (e₂ : p ⤳ x) (h₁ : ∀ y, y ⤳ ξ → y = ξ) (h₂ : ∀ y, y ⤳ p → y = p) : ξ = p := by
  have hξ : ξ ∈ Set.range (T.fromSpecStalk x) := by rw [Scheme.range_fromSpecStalk]; exact e₁
  have hp : p ∈ Set.range (T.fromSpecStalk x) := by rw [Scheme.range_fromSpecStalk]; exact e₂
  obtain ⟨a, rfl⟩ := hξ
  obtain ⟨b, rfl⟩ := hp
  exact (h₁ _ ((genericPoint_specializes a).map (T.fromSpecStalk x).continuous)).symm.trans
    (h₂ _ ((genericPoint_specializes b).map (T.fromSpecStalk x).continuous))

theorem isDominant_specMap_stalkSpecializes {T : Scheme.{0}} {x p : T} [IsDomain (T.presheaf.stalk x)]
    (e : p ⤳ x) (h : ∀ y, y ⤳ p → y = p) : IsDominant (Spec.map (T.presheaf.stalkSpecializes e)) := by
  have hm : Spec.map (T.presheaf.stalkSpecializes e) ≫ T.fromSpecStalk x = T.fromSpecStalk p :=
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk e
  have hp : p ∈ Set.range (T.fromSpecStalk p) := by
    rw [Scheme.range_fromSpecStalk]; exact specializes_rfl
  obtain ⟨c, hc⟩ := hp
  have hη : T.fromSpecStalk x (Spec.map (T.presheaf.stalkSpecializes e) c) = p := by
    rw [← Scheme.Hom.comp_apply, hm, hc]
  have hθ : T.fromSpecStalk x (genericPoint (Spec (T.presheaf.stalk x))) = p :=
    h _ (hη ▸ (genericPoint_specializes _).map (T.fromSpecStalk x).continuous)
  have hinj : Function.Injective (T.fromSpecStalk x) := (T.fromSpecStalk x).isEmbedding.injective
  have hr : genericPoint (Spec (T.presheaf.stalk x)) ∈
      Set.range (Spec.map (T.presheaf.stalkSpecializes e)) := ⟨c, hinj (hη.trans hθ.symm)⟩
  refine ⟨?_⟩
  have h2 : Dense ({genericPoint (Spec (T.presheaf.stalk x))} : Set (Spec (T.presheaf.stalk x))) := by
    rw [dense_iff_closure_eq]; exact genericPoint_spec _
  exact h2.mono (Set.singleton_subset_iff.2 hr)

theorem exists_generic_specializes {U : Scheme.{0}} (x : U) :
    ∃ q : U, (∀ y, y ⤳ q → y = q) ∧ q ⤳ x := by
  have hZ := irreducibleComponent_mem_irreducibleComponents x
  obtain ⟨q, hq⟩ := QuasiSober.sober (isIrreducible_irreducibleComponent (x := x)) isClosed_irreducibleComponent
  refine ⟨q, fun y hy => ?_, hq.specializes mem_irreducibleComponent⟩
  have h1 : irreducibleComponent x ⊆ closure {y} := by
    rw [← hq.def]; exact specializes_iff_closure_subset.mp hy
  have h2 := hZ.2 isIrreducible_singleton.closure h1
  exact (hy.antisymm (specializes_iff_closure_subset.mpr (h2.trans_eq hq.def.symm))).eq

theorem exists_glue_of_flat_dense : ∀ (S T U Y : Scheme.{0}) (t : T ⟶ S) (s : Y ⟶ S) (j : U ⟶ T) (g : U ⟶ Y), LocallyOfFiniteType s → IsSeparated s → S.IsSeparated → IsLocallyNoetherian T → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme T → IsReduced U → IsLocallyNoetherian U → Mono j → Flat j → g ≫ s = j ≫ t → (∀ x : T, ∃ (V : T.Opens) (hx : x ∈ V) (h : V.toScheme ⟶ Y) (p : T) (hp : p ∈ V) (v : Spec (T.presheaf.stalk p) ⟶ U), p ⤳ x ∧ (∀ q : T, q ⤳ p → q = p) ∧ v ≫ j = T.fromSpecStalk p ∧ V.fromSpecStalkOfMem p hp ≫ h = v ≫ g) → ∃ F : T ⟶ Y, F ≫ s = t ∧ j ≫ F = g := by
  intro S T U Y t s j g _ _ _ _ hn _ _ _ _ hgs loc
  have : GlobalTheory.IsNormalScheme T := GlobalTheory.IsNormalScheme.of_pred hn
  choose V hx hh p hp v hsp hgen hv hhv using loc
  let h : ∀ x : T, Spec (T.presheaf.stalk x) ⟶ Y := fun x => (V x).fromSpecStalkOfMem x (hx x) ≫ hh x
  have hres : ∀ x, Spec.map (T.presheaf.stalkSpecializes (hsp x)) ≫ h x = v x ≫ g := fun x => by
    rw [← hhv x, ← Category.assoc]
    congr 1
    rw [← cancel_mono (V x).ι, Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι,
      Scheme.Opens.fromSpecStalkOfMem_ι, Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
  have claim : ∀ (x ξ : T) (e : ξ ⤳ x), (∀ y, y ⤳ ξ → y = ξ) → ∃ w : Spec (T.presheaf.stalk ξ) ⟶ U,
      w ≫ j = T.fromSpecStalk ξ ∧ Spec.map (T.presheaf.stalkSpecializes e) ≫ h x = w ≫ g := by
    intro x ξ e hξ
    obtain rfl : ξ = p x := eq_of_specializes_of_isDomain e (hsp x) hξ (hgen x)
    exact ⟨v x, hv x, hres x⟩
  have gen : ∀ ξ : T, (∀ y, y ⤳ ξ → y = ξ) → ∃ w : Spec (T.presheaf.stalk ξ) ⟶ U,
      w ≫ j = T.fromSpecStalk ξ ∧ h ξ = w ≫ g := by
    intro ξ hξ
    obtain ⟨w, hw, hw'⟩ := claim ξ ξ specializes_rfl hξ
    refine ⟨w, hw, ?_⟩
    rw [← hw', TopCat.Presheaf.stalkSpecializes_refl]
    simp
  have compat : ∀ (x ξ : T) (e : ξ ⤳ x), (∀ y, y ⤳ ξ → y = ξ) →
      Spec.map (T.presheaf.stalkSpecializes e) ≫ h x = h ξ := by
    intro x ξ e hξ
    obtain ⟨w, hw, hw'⟩ := claim x ξ e hξ
    obtain ⟨w₂, hw₂, hw₂'⟩ := gen ξ hξ
    have hww : w = w₂ := by rw [← cancel_mono j, hw, hw₂]
    rw [hw', hww, hw₂']
  have hover : ∀ x, h x ≫ s = T.fromSpecStalk x ≫ t := by
    intro x
    have := isDominant_specMap_stalkSpecializes (hsp x) (hgen x)
    refine ext_of_isDominant (Spec.map (T.presheaf.stalkSpecializes (hsp x))) ?_
    rw [← Category.assoc, hres, Category.assoc, hgs, ← Category.assoc, hv, ← Category.assoc,
      Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
  obtain ⟨F, hF⟩ := GlobalTheory.GlueStalk.exists_glue_of_stalks S T Y t s h ‹_› ‹_› ‹_› hn hover compat
  have hFs : F ≫ s = t := ext_of_fromSpecStalk (terminal.from S) (terminal.hom_ext _ _) Set.univ
    (fun x => ⟨x, trivial, specializes_rfl⟩) fun x _ => by
      rw [← Category.assoc, hF, hover]
  refine ⟨F, hFs, ?_⟩
  refine ext_of_fromSpecStalk s (by rw [Category.assoc, hFs, hgs]) {q | ∀ y, y ⤳ q → y = q}
    (fun x => ?_) fun q hq => ?_
  · obtain ⟨q, hq, e⟩ := exists_generic_specializes x
    exact ⟨q, hq, e⟩
  · have hq' : ∀ y, y ⤳ j q → y = j q := fun y hy => by
      obtain ⟨q', h₁, rfl⟩ := Flat.generalizingMap j hy
      exact congrArg j (hq q' h₁)
    obtain ⟨w, hw, hw'⟩ := gen (j q) hq'
    have e₁ : U.fromSpecStalk q ≫ j = Spec.map (j.stalkMap q) ≫ T.fromSpecStalk (j q) :=
      (Scheme.SpecMap_stalkMap_fromSpecStalk j).symm
    have e₂ : Spec.map (j.stalkMap q) ≫ w = U.fromSpecStalk q := by
      rw [← cancel_mono j, Category.assoc, hw, e₁]
    rw [← Category.assoc, e₁, Category.assoc, hF, hw', ← Category.assoc, e₂]

end GlobalTheory.GlueDense
