import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AuxiliaryInertOddPrime

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory.Models

theorem isFinite_lift_comp {X X' X'' S S' S'' : Scheme.{0}} {s : X ⟶ S} {s' : X' ⟶ S'} {s'' : X'' ⟶ S''}
    {g : S' ⟶ S} {g' : S'' ⟶ S'} {g'' : S'' ⟶ S} (hg : g'' = g' ≫ g) {p : X' ⟶ X} {p' : X'' ⟶ X'}
    (w : p ≫ s = s' ≫ g) (w' : p' ≫ s' = s'' ≫ g') (w'' : (p' ≫ p) ≫ s = s'' ≫ g'')
    (h : IsFinite (pullback.lift p s' w)) (h' : IsFinite (pullback.lift p' s'' w')) :
    IsFinite (pullback.lift (p' ≫ p) s'' w'') := by
  subst hg
  obtain ⟨θ, hθ1, hθ2⟩ : ∃ θ : pullback s' g' ⟶ pullback s (g' ≫ g),
      θ ≫ pullback.fst s (g' ≫ g) = pullback.fst s' g' ≫ p ∧ θ ≫ pullback.snd s (g' ≫ g) = pullback.snd s' g' :=
    ⟨pullback.lift (pullback.fst s' g' ≫ p) (pullback.snd s' g')
      (by rw [Category.assoc, w, pullback.condition_assoc]), pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  obtain ⟨κ, hκ1, hκ2⟩ : ∃ κ : pullback s (g' ≫ g) ⟶ pullback s g,
      κ ≫ pullback.fst s g = pullback.fst s (g' ≫ g) ∧ κ ≫ pullback.snd s g = pullback.snd s (g' ≫ g) ≫ g' :=
    ⟨pullback.lift (pullback.fst s (g' ≫ g)) (pullback.snd s (g' ≫ g) ≫ g')
      (by rw [Category.assoc]; exact pullback.condition), pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩

  have hfac : pullback.lift (p' ≫ p) s'' w'' = pullback.lift p' s'' w' ≫ θ := by
    apply pullback.hom_ext
    · simp only [Category.assoc, hθ1, pullback.lift_fst, pullback.lift_fst_assoc]
    · simp only [Category.assoc, hθ2, pullback.lift_snd]

  have hright : IsPullback (pullback.snd s (g' ≫ g)) κ g' (pullback.snd s g) := by
    refine IsPullback.of_bot ?_ hκ2.symm (IsPullback.of_hasPullback s g).flip
    rw [hκ1]
    exact (IsPullback.of_hasPullback s (g' ≫ g)).flip

  have hsq : IsPullback θ (pullback.fst s' g') κ (pullback.lift p s' w) := by
    refine IsPullback.of_right ?_ ?_ hright
    · rw [hθ2, pullback.lift_snd]
      exact (IsPullback.of_hasPullback s' g').flip
    · apply pullback.hom_ext
      · simp only [Category.assoc, hκ1, hθ1, pullback.lift_fst]
      · simp only [Category.assoc, hκ2, reassoc_of% hθ2, pullback.lift_snd, pullback.condition]
  have hfin : IsFinite θ := MorphismProperty.of_isPullback (P := @IsFinite) hsq.flip h
  rw [hfac]
  infer_instance

theorem above_comp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (U : Scheme.{0}) (F O : Type) [Field F] [CommRing O] (c : U ⟶ Sp F) (t : SAB H U) (β : O →+* F) (U' : Scheme.{0}) (F' O' : Type) [Field F'] [CommRing O'] (c' : U' ⟶ Sp F') (t' : SAB H U') (β' : O' →+* F') (U'' : Scheme.{0}) (F'' O'' : Type) [Field F''] [CommRing O''] (c'' : U'' ⟶ Sp F'') (t'' : SAB H U'') (β'' : O'' →+* F'') (C : Cpt c t β) (C' : Cpt c' t' β') (C'' : Cpt c'' t'' β'') (b : O →+* O') (b' : O' →+* O'') (r : U' ⟶ U) (ν : SABMap t' t r) (r' : U'' ⟶ U') (ν' : SABMap t'' t' r') (ν'' : SABMap t'' t (r' ≫ r)) (a : C'.Above C b r ν) (a' : C''.Above C' b' r' ν'), ν''.φ = ν'.φ ≫ ν.φ → ∃ a'' : C''.Above C (b'.comp b) (r' ≫ r) ν'', a''.π = a'.π ≫ a.π ∧ a''.mu.φ = a'.mu.φ ≫ a.mu.φ := by
  intro E _ _ _ H U F O _ _ c t β U' F' O' _ _ c' t' β' U'' F'' O'' _ _ c'' t'' β'' C C' C'' b b' r ν r' ν' ν'' a a' hν
  obtain ⟨mu, hmu⟩ := sabComp pullCubComp E H _ _ _ C.t C'.t C''.t a.π a'.π a.mu a'.mu
  have hsp : spMap (b'.comp b) = spMap b' ≫ spMap b := by
    unfold spMap
    rw [CommRingCat.ofHom_comp, Spec.map_comp]
  have hover : (a'.π ≫ a.π) ≫ C.s = C''.s ≫ spMap (b'.comp b) := by
    rw [hsp, Category.assoc, a.π_over, ← Category.assoc, a'.π_over, Category.assoc]
  refine ⟨⟨a'.π ≫ a.π, hover, isFinite_lift_comp hsp a.π_over a'.π_over hover a.fin a'.fin, mu, ?_, ?_⟩, rfl, hmu⟩
  · rw [← Category.assoc, a'.j_comm, Category.assoc, a.j_comm, Category.assoc]
  · rw [hmu, hν, ← Category.assoc, a'.φ_comm, Category.assoc, a.φ_comm, Category.assoc]

end GlobalTheory.Models
