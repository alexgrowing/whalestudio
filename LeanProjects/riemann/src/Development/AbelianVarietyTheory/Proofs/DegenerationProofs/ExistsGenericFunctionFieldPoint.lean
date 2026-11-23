import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsUnitEv
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

noncomputable section
namespace GlobalTheory.SS.WtRat

variable {Y : Scheme.{0}}

theorem top_le_fromSpecStalk_preimage (x : Y) {V : Y.Opens} (hx : x ∈ V) :
    ⊤ ≤ Y.fromSpecStalk x ⁻¹ᵁ V := by
  intro y _
  have : Y.fromSpecStalk x y ∈ Set.range (Y.fromSpecStalk x) := ⟨y, rfl⟩
  rw [Scheme.range_fromSpecStalk] at this
  exact this.mem_open V.isOpen hx

theorem ev_fromSpecStalk (x : Y) {V : Y.Opens} (hx : x ∈ V)
    (h : ⊤ ≤ Y.fromSpecStalk x ⁻¹ᵁ V) (u : Γ(Y, V)) :
    ev (R := Y.presheaf.stalk x) (Y.fromSpecStalk x) V h u = (Y.presheaf.germ V x hx).hom u := by
  have : (Y.fromSpecStalk x).appLE V ⊤ h ≫ (Scheme.ΓSpecIso (Y.presheaf.stalk x)).hom =
      Y.presheaf.germ V x hx := by
    rw [Scheme.Hom.appLE, Scheme.fromSpecStalk_app hx]
    simp only [Category.assoc, ← Functor.map_comp]
    rw [show ∀ q : (Opposite.op (⊤ : (Spec (Y.presheaf.stalk x)).Opens) ⟶ Opposite.op ⊤),
      (Spec (Y.presheaf.stalk x)).presheaf.map q = 𝟙 _ from fun q => by
        rw [Subsingleton.elim q (𝟙 _)]; exact CategoryTheory.Functor.map_id _ _]
    simp
  exact congrArg (fun q => CommRingCat.Hom.hom q u) this

theorem genericPoint_mem [IsIntegral Y] {V : Y.Opens} (hV : (V : Set Y).Nonempty) :
    genericPoint Y ∈ V :=
  ((genericPoint_spec Y).mem_open_set_iff V.isOpen).mpr (by simpa using hV)

theorem exists_generic_field_point : ∀ (Y : Scheme.{0}) [IsIntegral Y], ∃ (F : Type) (_ : Field F) (g : Sp F ⟶ Y) (hg : ∀ V : Y.Opens, (V : Set Y).Nonempty → ⊤ ≤ g ⁻¹ᵁ V), (∀ (V : Y.Opens) (hV : (V : Set Y).Nonempty), Function.Injective (WtRat.ev g V (hg V hV))) ∧ (∀ τ : Y ≅ Y, ∃ σ : F →+* F, spMap σ ≫ g = g ≫ τ.hom) ∧ ∀ U : Y.Opens, (U : Set Y).Nonempty → ∀ (I : Type) [Fintype I] (x : I → F), ∃ (U' : Y.Opens) (hU' : (U' : Set Y).Nonempty) (s : I → Γ(Y, U')), U' ≤ U ∧ ∀ j, WtRat.ev g U' (hg U' hU') (s j) = x j ∧ (x j ≠ 0 → IsUnit (s j)) := by
  intro Y _
  have hg : ∀ V : Y.Opens, (V : Set Y).Nonempty → ⊤ ≤ Y.fromSpecStalk (genericPoint Y) ⁻¹ᵁ V :=
    fun V hV => top_le_fromSpecStalk_preimage _ (genericPoint_mem hV)
  refine ⟨Y.functionField, inferInstance, Y.fromSpecStalk (genericPoint Y), hg, ?_, ?_, ?_⟩
  · intro V hV a b hab
    have ha := ev_fromSpecStalk _ (genericPoint_mem hV) (hg V hV) a
    have hb := ev_fromSpecStalk _ (genericPoint_mem hV) (hg V hV) b
    exact germ_injective_of_isIntegral Y (genericPoint Y) (genericPoint_mem hV)
      (ha.symm.trans (hab.trans hb))
  · intro τ
    have e : τ.hom (genericPoint Y) = genericPoint Y := genericPoint_eq_of_isOpenImmersion τ.hom
    have sp : τ.hom (genericPoint Y) ⤳ genericPoint Y := specializes_of_eq e
    refine ⟨(Y.presheaf.stalkSpecializes sp ≫ τ.hom.stalkMap (genericPoint Y)).hom, ?_⟩
    change Spec.map (Y.presheaf.stalkSpecializes sp ≫ τ.hom.stalkMap (genericPoint Y)) ≫
      Y.fromSpecStalk (genericPoint Y) = Y.fromSpecStalk (genericPoint Y) ≫ τ.hom
    rw [Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk,
      Scheme.SpecMap_stalkMap_fromSpecStalk]
  · intro U hU I _ x
    have key : ∀ a : Y.functionField, ∃ (V : Y.Opens) (hV : genericPoint Y ∈ V) (s : Γ(Y, V)),
        (Y.presheaf.germ V _ hV).hom s = a ∧ (a ≠ 0 → IsUnit s) := by
      intro a
      obtain ⟨V, hV, s, hs⟩ := Y.presheaf.exists_germ_eq (x := genericPoint Y) a
      by_cases ha : a = 0
      · exact ⟨V, hV, s, hs, fun h => (h ha).elim⟩
      · have hm : genericPoint Y ∈ Y.basicOpen s := by
          rw [Scheme.mem_basicOpen Y s _ hV]
          have : IsUnit a := isUnit_iff_ne_zero.mpr ha
          rw [← hs] at this
          exact this
        refine ⟨Y.basicOpen s, hm, (Y.presheaf.map (homOfLE (Y.basicOpen_le s)).op).hom s, ?_,
          fun _ => Y.toRingedSpace.isUnit_res_basicOpen s⟩
        rw [← hs]
        exact Y.presheaf.germ_res_apply (homOfLE (Y.basicOpen_le s)) _ hm s
    choose V hV s hs hu using fun j => key (x j)
    have hle : ∀ j, U ⊓ Finset.univ.inf V ≤ V j := fun j =>
      inf_le_right.trans (Finset.inf_le (Finset.mem_univ j))
    have hm : genericPoint Y ∈ U ⊓ Finset.univ.inf V := by
      refine ⟨genericPoint_mem hU, ?_⟩
      change genericPoint Y ∈ ((Finset.univ.inf V : Y.Opens) : Set Y)
      rw [TopologicalSpace.Opens.coe_finset_inf, Finset.inf_set_eq_iInter]
      simp only [Set.mem_iInter]
      exact fun j _ => hV j
    refine ⟨U ⊓ Finset.univ.inf V, ⟨_, hm⟩,
      fun j => (Y.presheaf.map (homOfLE (hle j)).op).hom (s j), inf_le_left, fun j => ⟨?_, fun h => (hu j h).map _⟩⟩
    refine (ev_fromSpecStalk _ hm _ _).trans ?_
    rw [← hs j]
    exact Y.presheaf.germ_res_apply (homOfLE (hle j)) _ hm (s j)

end GlobalTheory.SS.WtRat
end
