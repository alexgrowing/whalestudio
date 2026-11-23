import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameCover
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)

namespace GlobalTheory.ProjFinProd

theorem exists_isProjOver_finite_prod : ∀ (O : Type) [CommRing O] (ι : Type) [Finite ι] (X : Scheme.{0}) (s : X ⟶ Sp O) (Y : ι → Scheme.{0}) (f : ∀ i, Y i ⟶ Sp O), IsProjOver s → (∀ i, IsProjOver (f i)) → ∃ (P : Scheme.{0}) (p0 : P ⟶ X) (p : ∀ i, P ⟶ Y i), IsProjOver (p0 ≫ s) ∧ (∀ i, p i ≫ f i = p0 ≫ s) ∧ ∀ (Z : Scheme.{0}) (a : Z ⟶ X) (b : ∀ i, Z ⟶ Y i), (∀ i, b i ≫ f i = a ≫ s) → ∃! h : Z ⟶ P, h ≫ p0 = a ∧ ∀ i, h ≫ p i = b i := by
  intro O _ ι _ X s
  induction ι using Finite.induction_empty_option with
  | of_equiv e ih =>
    intro Y f hs hf
    rename_i α β
    obtain ⟨P, p0, p, hP, hp, hu⟩ := ih (fun i => Y (e i)) (fun i => f (e i)) hs (fun i => hf _)
    have key : ∀ j : β, ∃ q : P ⟶ Y j, q ≫ f j = p0 ≫ s ∧ ∀ i (h : e i = j), q = p i ≫ eqToHom (congrArg Y h) := by
      intro j
      obtain ⟨i, rfl⟩ := e.surjective j
      refine ⟨p i, hp i, fun i' h => ?_⟩
      obtain rfl := e.injective h
      simp
    choose q hq1 hq2 using key
    have hq : ∀ i, q (e i) = p i := fun i => by simpa using hq2 (e i) i rfl
    refine ⟨P, p0, q, hP, hq1, fun Z a b hb => ?_⟩
    obtain ⟨h, ⟨h1, h2⟩, h3⟩ := hu Z a (fun i => b (e i)) (fun i => hb _)
    refine ⟨h, ⟨h1, fun j => ?_⟩, fun h' hh => h3 h' ⟨hh.1, fun i => ?_⟩⟩
    · obtain ⟨i, rfl⟩ := e.surjective j
      rw [hq]; exact h2 i
    · rw [← hq]; exact hh.2 _
  | h_empty =>
    intro Y f hs hf
    refine ⟨X, 𝟙 X, fun i => i.elim, by simpa using hs, fun i => i.elim, fun Z a b _ => ?_⟩
    exact ⟨a, ⟨by simp, fun i => i.elim⟩, fun h hh => by simpa using hh.1⟩
  | h_option ih =>
    intro Y f hs hf
    obtain ⟨P, p0, p, hP, hp, hu⟩ := ih (fun i => Y (some i)) (fun i => f (some i)) hs (fun i => hf _)
    refine ⟨pullback (p0 ≫ s) (f none), pullback.fst _ _ ≫ p0,
      fun i => match i with
        | none => pullback.snd _ _
        | some i => pullback.fst _ _ ≫ p i, ?_, ?_, fun Z a b hb => ?_⟩
    · rw [Category.assoc]
      exact isProjOver_pullback hP (hf none)
    · rintro (_ | i)
      · simp only [Category.assoc]; exact pullback.condition.symm
      · simp only [Category.assoc]; rw [hp i]
    · obtain ⟨h, ⟨h1, h2⟩, h3⟩ := hu Z a (fun i => b (some i)) (fun i => hb _)
      refine ⟨pullback.lift h (b none) (by rw [reassoc_of% h1, hb]), ⟨?_, ?_⟩, fun h' hh => ?_⟩
      · rw [pullback.lift_fst_assoc, h1]
      · rintro (_ | i)
        · exact pullback.lift_snd _ _ _
        · exact (pullback.lift_fst_assoc _ _ _ _).trans (h2 i)
      · apply pullback.hom_ext
        · rw [pullback.lift_fst]
          refine h3 _ ⟨by simpa using hh.1, fun i => ?_⟩
          simpa using hh.2 (some i)
        · rw [pullback.lift_snd]; exact hh.2 none

end GlobalTheory.ProjFinProd
