import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleProductOfEach
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleTransportAlongIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleBaseChangeAltBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackFreeModuleIsoStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.NormSqColGrLineOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartialFlagSmoothArithmetic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CellVarietyDimensionCounts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StalkStepMono
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagVarietyLiftExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagVarietyLiftUniqueStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TautologicalSubbundleRankStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoInclLast
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace GlobalTheory.FlagFreeSmooth

open Limits

theorem exists_widePullback_smooth {B : Scheme.{0}} (ι : Type) [Fintype ι] :
    ∀ (Z : ι → Scheme.{0}) (ρ : ∀ a, Z a ⟶ B) (d : ι → ℕ), (∀ a, SmoothOfRelativeDimension (d a) (ρ a)) →
      ∃ (Y : Scheme.{0}) (π : Y ⟶ B) (p : ∀ a, Y ⟶ Z a), (∀ a, p a ≫ ρ a = π) ∧
        SmoothOfRelativeDimension (∑ a, d a) π ∧
        ∀ (T : Scheme.{0}) (g : T ⟶ B) (h : ∀ a, T ⟶ Z a), (∀ a, h a ≫ ρ a = g) →
          ∃! g' : T ⟶ Y, g' ≫ π = g ∧ ∀ a, g' ≫ p a = h a := by
  refine @Fintype.induction_empty_option (fun α _ => ∀ (Z : α → Scheme.{0}) (ρ : ∀ a, Z a ⟶ B) (d : α → ℕ),
      (∀ a, SmoothOfRelativeDimension (d a) (ρ a)) →
      ∃ (Y : Scheme.{0}) (π : Y ⟶ B) (p : ∀ a, Y ⟶ Z a), (∀ a, p a ≫ ρ a = π) ∧
        SmoothOfRelativeDimension (∑ a, d a) π ∧
        ∀ (T : Scheme.{0}) (g : T ⟶ B) (h : ∀ a, T ⟶ Z a), (∀ a, h a ≫ ρ a = g) →
          ∃! g' : T ⟶ Y, g' ≫ π = g ∧ ∀ a, g' ≫ p a = h a) ?_ ?_ ?_ ι _
  · intro α β _ e ih Z ρ d hρ
    letI : Fintype α := Fintype.ofEquiv β e.symm
    obtain ⟨Y, π, p, hp, hY, H⟩ := ih (fun a => Z (e a)) (fun a => ρ (e a)) (fun a => d (e a)) fun a => hρ _
    let p' : ∀ b, Y ⟶ Z b := Equiv.piCongrLeft (fun b => Y ⟶ Z b) e p
    have hp' (a : α) : p' (e a) = p a := Equiv.piCongrLeft_apply_apply _ _ _ _
    have hs : ∑ a, d (e a) = ∑ b, d b := Equiv.sum_comp e d
    rw [hs] at hY
    refine ⟨Y, π, p', e.forall_congr_right.1 fun a => by rw [hp', hp], hY, fun T g h hh => ?_⟩
    obtain ⟨g', ⟨h₁, h₂⟩, u⟩ := H T g (fun a => h (e a)) fun a => hh _
    exact ⟨g', ⟨h₁, e.forall_congr_right.1 fun a => by rw [hp', h₂]⟩,
      fun y hy => u y ⟨hy.1, fun a => by rw [← hp', hy.2]⟩⟩
  · intro Z ρ d _
    have h0 : (∑ a : PEmpty, d a) = 0 := by simp
    rw [h0]
    exact ⟨B, 𝟙 B, fun a => a.elim, fun a => a.elim, inferInstance,
      fun T g _ _ => ⟨g, ⟨Category.comp_id g, fun a => a.elim⟩, fun y hy => (Category.comp_id y).symm.trans hy.1⟩⟩
  · intro α _ ih Z ρ d hρ
    obtain ⟨Y, π, p, hp, hY, H⟩ := ih (fun a => Z (some a)) (fun a => ρ (some a)) (fun a => d (some a))
      fun a => hρ _
    have : SmoothOfRelativeDimension (d none) (pullback.fst π (ρ none)) :=
      haveI := smoothOfRelativeDimension_isStableUnderBaseChange (n := d none)
      MorphismProperty.pullback_fst (P := @SmoothOfRelativeDimension (d none)) π (ρ none) (hρ none)
    have hs : SmoothOfRelativeDimension (∑ a, d a) (pullback.fst π (ρ none) ≫ π) := by
      rw [Fintype.sum_option]
      infer_instance
    refine ⟨pullback π (ρ none), pullback.fst _ _ ≫ π,
      fun a => Option.rec (pullback.snd _ _) (fun a => pullback.fst _ _ ≫ p a) a, ?_, hs, fun T g h hh => ?_⟩
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

end GlobalTheory.FlagFreeSmooth

namespace GlobalTheory.FlagFreeSmooth

theorem smooth_flStr_unit (n : ℕ) : SmoothOfRelativeDimension (n * (n - 1) / 2) (GlobalTheory.FlagZ.flStr Unit n) := by
  have h := (GlobalTheory.FlagZ.smooth_dim_isArithVar_part Unit (Unit × Fin (n + 1)) n Prod.fst Prod.snd).1
  rw [(GlobalTheory.FlagZ.Count.card_cellVar Unit n).1] at h
  unfold dimFl at h
  simpa using h

end GlobalTheory.FlagFreeSmooth

namespace GlobalTheory.FlagFreeSmooth

open GlobalTheory.FlagZ GlobalTheory.FlagZ.Univ

def univFlag (ι : Type) [Fintype ι] (N : ℕ) (τ : ι) :
    Vert.Flag ((Scheme.Modules.pullback (flStr ι N)).obj (GlobalTheory.QCoh.freeModule (X := Sp ℤ) (Fin N))) N where
  F := F ι N τ
  ι := incl ι N τ
  isSubbundle i := (GlobalTheory.T.tautological_subbundle_rank ι N τ i).2
  isVB i := (GlobalTheory.T.tautological_subbundle_rank ι N τ i).1
  step := step ι N τ
  step_ι := step_incl ι N τ
  isIso_last := isIso_incl_last ι N τ

theorem isFlagBundle_univFlag (ι : Type) [Fintype ι] (N : ℕ) :
    IsFlagBundle (flStr ι N) (fun _ : ι => SheafOfModules.free (R := (Sp ℤ).ringCatSheaf) (Fin N)) (fun _ => N)
      (univFlag ι N) := by
  intro T g fl'
  obtain ⟨g', hg'⟩ := GlobalTheory.T.flag_variety_lift_exists ι N T g fl'
  exact ⟨g', hg', fun y hy => GlobalTheory.T.flag_variety_lift_unique ι N T g fl' y g' hy hg'⟩

theorem exists_single_int : ∀ (n : ℕ), ∃ (Y : Scheme.{0}) (π : Y ⟶ Sp ℤ) (fl : ∀ _ : Unit, Vert.Flag ((Scheme.Modules.pullback π).obj (SheafOfModules.free (R := (Sp ℤ).ringCatSheaf) (Fin n))) n), IsFlagBundle π (fun _ : Unit => SheafOfModules.free (R := (Sp ℤ).ringCatSheaf) (Fin n)) (fun _ => n) fl ∧ SmoothOfRelativeDimension (n * (n - 1) / 2) π := fun n =>
  ⟨Fl Unit n, flStr Unit n, univFlag Unit n, isFlagBundle_univFlag Unit n, smooth_flStr_unit n⟩

end GlobalTheory.FlagFreeSmooth

namespace GlobalTheory.FlagFreeSmooth

open Limits

theorem exists_single (B : Scheme.{0}) (n : ℕ) :
    ∃ (Y : Scheme.{0}) (π : Y ⟶ B) (fl : ∀ _ : Unit, Vert.Flag ((Scheme.Modules.pullback π).obj
      (SheafOfModules.free (R := B.ringCatSheaf) (Fin n))) n),
      IsFlagBundle π (fun _ : Unit => SheafOfModules.free (R := B.ringCatSheaf) (Fin n)) (fun _ => n) fl ∧
      SmoothOfRelativeDimension (n * (n - 1) / 2) π := by
  obtain ⟨Y, π, fl, hfl, hs⟩ := exists_single_int n
  let g : B ⟶ Sp ℤ := specZIsTerminal.from B
  have hbc := GlobalTheory.T.isFlagBundle_pullback' (Sp ℤ) Y B π g Unit _ (fun _ => n) fl hfl
  obtain ⟨e⟩ := GlobalTheory.T.pullback_free_module_iso B (Sp ℤ) g n
  have hiso := GlobalTheory.FlagIsoBundle.isFlagBundle_of_iso B (pullback π g) (pullback.snd π g) Unit _
    (fun _ : Unit => SheafOfModules.free (R := B.ringCatSheaf) (Fin n)) (fun _ => n) _ (fun _ => e) hbc
  have : SmoothOfRelativeDimension (n * (n - 1) / 2) (pullback.snd π g) :=
    haveI := smoothOfRelativeDimension_isStableUnderBaseChange (n := n * (n - 1) / 2)
    MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension (n * (n - 1) / 2)) π g hs
  exact ⟨_, _, _, hiso, this⟩

theorem main : ∀ (B : Scheme.{0}) (ι : Type) [Fintype ι] (r : ι → ℕ), ∃ (Y : Scheme.{0}) (π : Y ⟶ B) (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (SheafOfModules.free (R := B.ringCatSheaf) (Fin (r a)))) (r a)), IsFlagBundle π (fun a => SheafOfModules.free (R := B.ringCatSheaf) (Fin (r a))) r fl ∧ SmoothOfRelativeDimension (∑ a, r a * (r a - 1) / 2) π := by
  intro B ι _ r
  choose Z ρ fl hfl hs using fun a => exists_single B (r a)
  obtain ⟨Y, π, p, hp, hY, H⟩ := exists_widePullback_smooth ι Z ρ (fun a => r a * (r a - 1) / 2) hs
  exact ⟨Y, π, _, GlobalTheory.FlagFamily.isFlagBundle_of_widePullback
    (fun a => SheafOfModules.free (R := B.ringCatSheaf) (Fin (r a))) r ρ fl hfl π p hp H, hY⟩

end GlobalTheory.FlagFreeSmooth
