import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartSome
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Div.DescendOpens

theorem overlap_preimage_open : ∀ (B S X : Scheme.{0}) (π : S ⟶ B) (U : Over B) (J : Type) (e : J → (pullback U.hom π ⟶ X)), IsProper π → Surjective π → (∀ j, IsOpenImmersion (e j)) → (∀ (i j : J) (T : Scheme.{0}) (w₁ w₂ h₁ : T ⟶ pullback U.hom π), w₁ ≫ pullback.fst _ _ = w₂ ≫ pullback.fst _ _ → h₁ ≫ e j = w₁ ≫ e i → ∃ h₂ : T ⟶ pullback U.hom π, h₂ ≫ e j = w₂ ≫ e i ∧ h₂ ≫ pullback.fst _ _ = h₁ ≫ pullback.fst _ _) → ∀ i j : J, ∃ V : U.left.Opens, ∀ a : ↥(pullback U.hom π), pullback.fst U.hom π a ∈ V ↔ e i a ∈ Set.range (e j) := by
  intro B S X π U J e hP _ hO key i j
  haveI := hP
  haveI : UniversallyClosed (pullback.fst U.hom π) := inferInstance
  set p := pullback.fst U.hom π with hp
  let W : Set ↥(pullback U.hom π) := (e i) ⁻¹' Set.range (e j)
  have hWo : IsOpen W := by
    haveI := hO j
    exact (e i).continuous.isOpen_preimage _ (e j).isOpenEmbedding.isOpen_range
  have sat : ∀ a c : ↥(pullback U.hom π), p a = p c → a ∈ W → c ∈ W := by
    intro a c hac ha
    obtain ⟨b, hb⟩ := ha
    obtain ⟨t, ht1, ht2⟩ := Scheme.Pullback.exists_preimage_pullback (f := p) (g := p) a c hac
    have h1 : (pullback.fst p p ≫ e i) t = e j b := by
      simp only [Scheme.Hom.comp_apply, ht1]; exact hb.symm
    obtain ⟨t', ht'1, ht'2⟩ := Scheme.Pullback.exists_preimage_pullback
      (f := pullback.fst p p ≫ e i) (g := e j) t b h1
    obtain ⟨h₂, hh₂, -⟩ := key i j _
      (pullback.fst (pullback.fst p p ≫ e i) (e j) ≫ pullback.fst p p)
      (pullback.fst (pullback.fst p p ≫ e i) (e j) ≫ pullback.snd p p)
      (pullback.snd (pullback.fst p p ≫ e i) (e j))
      (by simp only [Category.assoc]; rw [pullback.condition])
      (by rw [← pullback.condition, Category.assoc])
    refine ⟨h₂ t', ?_⟩
    have := congrArg (fun f => f t') hh₂
    simp only [Scheme.Hom.comp_apply, ht'1, ht2] at this
    exact this
  refine ⟨⟨(p '' Wᶜ)ᶜ, ?_⟩, ?_⟩
  · exact (p.isClosedMap _ hWo.isClosed_compl).isOpen_compl
  · intro a
    change p a ∈ (p '' Wᶜ)ᶜ ↔ a ∈ W
    constructor
    · intro h
      by_contra ha
      exact h ⟨a, ha, rfl⟩
    · rintro ha ⟨c, hc, hca⟩
      exact hc (sat a c hca.symm ha)

end GlobalTheory.Div.DescendOpens
