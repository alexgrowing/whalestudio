import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsTranslSum
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsMonHomIffOfIsGrpPullback

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HeckeFrCompare GlobalTheory.PlaceInt
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HkIntegral

namespace GlobalTheory.HkIntegral.PairBC

section General

variable {S S' : Scheme.{0}} {j : S' ⟶ S}

theorem exists_proj {X : Scheme.{0}} (G : Over X) [GrpObj G] (x : S ⟶ X) (w : S' ⟶ X) (h : w = j ≫ x) :
    ∃ π : pullback G.hom w ⟶ pullback G.hom x, π ≫ pullback.fst _ _ = pullback.fst _ _ ∧
      π ≫ pullback.snd _ _ = pullback.snd _ _ ≫ j ∧
      IsGrpPullback ((Over.pullback w).obj G) ((Over.pullback x).obj G) j π := by
  have e : pullback.fst G.hom w ≫ G.hom = (pullback.snd _ _ ≫ j) ≫ x := by
    rw [Category.assoc, ← h, pullback.condition]
  exact ⟨pullback.lift _ _ e, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _, (isGrpPullback_pullback G _).cancel
    ((isGrpPullback_pullback G _).congr h (pullback.lift_fst _ _ e).symm) (pullback.lift_snd _ _ _)⟩

theorem id_pow_left {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {π : G'.left ⟶ G.left}
    (h : IsGrpPullback G' G j π) (N : ℕ) : (𝟙 G' ^ N).left ≫ π = π ≫ (𝟙 G ^ N).left := by
  let U : Over.mk (G'.hom ≫ j) ⟶ G := Over.homMk π h.1.w
  have e : pushHom h G' (𝟙 G') = U := Over.OverMorphism.ext (Category.id_comp π)
  have e' : pushHom h G' (𝟙 G' ^ N) = U ≫ 𝟙 G ^ N := by
    rw [map_pow, e, MonObj.comp_pow, Category.comp_id]
  exact congrArg (fun u => u.left) e'

theorem eq_iff [Flat j] [Surjective j] {A B : Over S} {A' B' : Over S'} {α : A'.left ⟶ A.left}
    {β : B'.left ⟶ B.left} (hα : IsPullback α A'.hom A.hom j) (hβ : IsPullback β B'.hom B.hom j)
    {u v : A ⟶ B} {u' v' : A' ⟶ B'} (hu : u'.left ≫ β = α ≫ u.left) (hv : v'.left ≫ β = α ≫ v.left) :
    u = v ↔ u' = v' := by
  have : Flat α := MorphismProperty.of_isPullback (P := @Flat) hα.flip ‹_›
  have : Surjective α := MorphismProperty.of_isPullback (P := @Surjective) hα.flip ‹_›
  have : Epi α := Flat.epi_of_flat_of_surjective α
  constructor
  · rintro rfl
    exact Over.OverMorphism.ext (hβ.hom_ext (hu.trans hv.symm) (by rw [Over.w, Over.w]))
  · rintro rfl
    exact Over.OverMorphism.ext ((cancel_epi α).1 (hu.symm.trans hv))

theorem comp_sq {A B C : Over S} {A' B' C' : Over S'} {α : A'.left ⟶ A.left} {β : B'.left ⟶ B.left}
    {δ : C'.left ⟶ C.left} {u : A ⟶ B} {v : B ⟶ C} {u' : A' ⟶ B'} {v' : B' ⟶ C'}
    (hu : u'.left ≫ β = α ≫ u.left) (hv : v'.left ≫ δ = β ≫ v.left) :
    (u' ≫ v').left ≫ δ = α ≫ (u ≫ v).left := by
  rw [Over.comp_left, Over.comp_left, Category.assoc, hv, reassoc_of% hu]

theorem map_sq {X : Scheme.{0}} {G : Over X} {x : S ⟶ X} {w : S' ⟶ X} (π : pullback G.hom w ⟶ pullback G.hom x)
    (h₁ : π ≫ pullback.fst _ _ = pullback.fst _ _) (h₂ : π ≫ pullback.snd _ _ = pullback.snd _ _ ≫ j) (a : G ⟶ G) :
    ((Over.pullback w).map a).left ≫ π = π ≫ ((Over.pullback x).map a).left := by
  apply pullback.hom_ext <;>
    simp [h₁, h₂, reassoc_of% h₁, pullback.lift_fst, pullback.lift_snd, pullback.lift_snd_assoc]

end General

theorem exists_isBC_and_isPair_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (K L : Type) [Field K] [Field L] (φ : K →+* L) (x x' : Sp K ⟶ Xo.X) (w w' : Sp L ⟶ Xo.X), (w = spMap φ ≫ x → w' = spMap φ ≫ x' → ∀ f : Fib Xo x ⟶ Fib Xo x', ∃ g : Fib Xo w ⟶ Fib Xo w', IsBC φ f g) ∧ ∀ (f : Fib Xo x ⟶ Fib Xo x') (f' : Fib Xo x' ⟶ Fib Xo x) (g : Fib Xo w ⟶ Fib Xo w') (g' : Fib Xo w' ⟶ Fib Xo w) (N : ℕ), IsBC φ f g → IsBC φ f' g' → (IsPair N f f' ↔ IsPair N g g') := by
  intro E _ _ _ H Dw l Xo K L _ _ φ x x' w w'
  refine ⟨fun hw hw' f => ?_, fun f f' g g' N hf hf' => ?_⟩
  · obtain ⟨π, p₁, p₂, hπ⟩ := exists_proj Xo.univ.t.G x w hw
    obtain ⟨π', p₁', p₂', hπ'⟩ := exists_proj Xo.univ.t.G x' w' hw'
    have e : (π ≫ f.left) ≫ (Fib Xo x').hom = (Fib Xo w).hom ≫ spMap φ :=
      (Category.assoc _ _ _).trans ((congrArg (π ≫ ·) (Over.w f)).trans hπ.1.w)
    refine ⟨Over.homMk (hπ'.1.lift _ _ e) (hπ'.1.lift_snd _ _ e), hw, hw', fun ρ ρ' q₁ q₂ q₁' q₂' => ?_⟩
    obtain rfl : ρ = π := pullback.hom_ext (q₁.trans p₁.symm) (q₂.trans p₂.symm)
    obtain rfl : ρ' = π' := pullback.hom_ext (q₁'.trans p₁'.symm) (q₂'.trans p₂'.symm)
    exact hπ'.1.lift_fst _ _ e
  · have := FieldBaseChange.flat_spMap φ
    have := FieldBaseChange.surjective_spMap φ
    obtain ⟨π, p₁, p₂, hπ⟩ := exists_proj Xo.univ.t.G x w hf.1
    obtain ⟨π', p₁', p₂', hπ'⟩ := exists_proj Xo.univ.t.G x' w' hf.2.1
    have e := hf.2.2 π π' p₁ p₂ p₁' p₂'
    have e' := hf'.2.2 π' π p₁' p₂' p₁ p₂
    refine and_congr (FieldBaseChange.isMonHom_iff_of_isGrpPullback hπ hπ' g f e.symm).symm
      (and_congr (FieldBaseChange.isMonHom_iff_of_isGrpPullback hπ' hπ g' f' e'.symm).symm
      (and_congr (eq_iff hπ.1 hπ.1 (comp_sq e e') (id_pow_left hπ N))
      (and_congr (eq_iff hπ'.1 hπ'.1 (comp_sq e' e) (id_pow_left hπ' N))
      (and_congr (forall_congr' fun a => ?_) (forall_congr' fun a => ?_)))))
    · exact eq_iff hπ.1 hπ'.1 (comp_sq (map_sq π p₁ p₂ _) e)
        (comp_sq (u := f) (u' := g) (v := (Over.pullback x').map _) (v' := (Over.pullback w').map _) e
          (map_sq π' p₁' p₂' _))
    · exact eq_iff hπ'.1 hπ.1 (comp_sq (map_sq π' p₁' p₂' _) e')
        (comp_sq (u := f') (u' := g') (v := (Over.pullback x).map _) (v' := (Over.pullback w).map _) e'
          (map_sq π p₁ p₂ _))

end GlobalTheory.HkIntegral.PairBC
