import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullFlag
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleProductOfEach
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsFlagBundleIsArithVar
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagFree

open Limits

theorem exists_widePullback {B : Scheme.{0}} (ι : Type) [Finite ι] : ∀ (Z : ι → Scheme.{0}) (ρ : ∀ a, Z a ⟶ B),
      ∃ (Y : Scheme.{0}) (π : Y ⟶ B) (p : ∀ a, Y ⟶ Z a), (∀ a, p a ≫ ρ a = π) ∧
        ∀ (T : Scheme.{0}) (g : T ⟶ B) (h : ∀ a, T ⟶ Z a), (∀ a, h a ≫ ρ a = g) →
          ∃! g' : T ⟶ Y, g' ≫ π = g ∧ ∀ a, g' ≫ p a = h a := by
  induction ι using Finite.induction_empty_option with
  | @of_equiv α β e ih =>
    intro Z ρ
    obtain ⟨Y, π, p, hp, H⟩ := ih (fun a => Z (e a)) (fun a => ρ (e a))
    let p' : ∀ b, Y ⟶ Z b := Equiv.piCongrLeft (fun b => Y ⟶ Z b) e p
    have hp' (a : α) : p' (e a) = p a := Equiv.piCongrLeft_apply_apply _ _ _ _
    refine ⟨Y, π, p', e.forall_congr_right.1 fun a => by rw [hp', hp], fun T g h hh => ?_⟩
    obtain ⟨g', ⟨h₁, h₂⟩, u⟩ := H T g (fun a => h (e a)) fun a => hh _
    exact ⟨g', ⟨h₁, e.forall_congr_right.1 fun a => by rw [hp', h₂]⟩,
      fun y hy => u y ⟨hy.1, fun a => by rw [← hp', hy.2]⟩⟩
  | h_empty =>
    intro Z ρ
    exact ⟨B, 𝟙 B, fun a => a.elim, fun a => a.elim,
      fun T g _ _ => ⟨g, ⟨Category.comp_id g, fun a => a.elim⟩, fun y hy => (Category.comp_id y).symm.trans hy.1⟩⟩
  | @h_option α _ ih =>
    intro Z ρ
    obtain ⟨Y, π, p, hp, H⟩ := ih (fun a => Z (some a)) (fun a => ρ (some a))
    refine ⟨pullback π (ρ none), pullback.fst _ _ ≫ π,
      fun a => Option.rec (pullback.snd _ _) (fun a => pullback.fst _ _ ≫ p a) a, ?_, fun T g h hh => ?_⟩
    · rintro (_ | a)
      · exact pullback.condition.symm
      · exact (Category.assoc _ _ _).trans (congrArg _ (hp a))
    · obtain ⟨g', ⟨h₁, h₂⟩, u⟩ := H T g (fun a => h (some a)) fun a => hh _
      refine ⟨pullback.lift g' (h none) (h₁.trans (hh none).symm), ⟨by rw [pullback.lift_fst_assoc, h₁], ?_⟩,
        fun y hy => ?_⟩
      · rintro (_ | a)
        · exact pullback.lift_snd _ _ _
        · exact (pullback.lift_fst_assoc _ _ _ _).trans (h₂ a)
      · refine pullback.hom_ext ?_ ?_
        · rw [pullback.lift_fst]
          exact u _ ⟨(Category.assoc _ _ _).trans hy.1, fun a => (Category.assoc _ _ _).trans (hy.2 (some a))⟩
        · rw [pullback.lift_snd]
          exact hy.2 none

theorem exists_isFlagBundle_freeModule : ∀ (ι : Type) [Fintype ι] (r : ι → ℕ), ∃ (Y : Scheme.{0}) (π : Y ⟶ Sp ℤ) (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (GlobalTheory.QCoh.freeModule (X := Sp ℤ) (Fin (r a)))) (r a)), IsFlagBundle π (fun a => GlobalTheory.QCoh.freeModule (X := Sp ℤ) (Fin (r a))) r fl := by
  intro ι _ r
  obtain ⟨Y, π, p, hp, H⟩ := exists_widePullback ι (fun a => _) (fun a => GlobalTheory.FlagZ.flStr Unit (r a))
  exact ⟨Y, π, _, GlobalTheory.FlagFamily.isFlagBundle_of_widePullback
    (fun a => GlobalTheory.QCoh.freeModule (X := Sp ℤ) (Fin (r a))) r (fun a => GlobalTheory.FlagZ.flStr Unit (r a))
    (fun a => GlobalTheory.FlagZ.Univ.flag Unit (r a)) (fun a => GlobalTheory.FlagZ.Univ.isFlagBundle_flag Unit (r a)) π p hp H⟩

end GlobalTheory.FlagFree

end
