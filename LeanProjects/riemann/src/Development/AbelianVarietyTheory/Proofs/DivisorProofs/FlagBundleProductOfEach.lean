import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BcDensEqOfGram
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace GlobalTheory.FlagFamily

open Limits

theorem isProjOver_pullback_over {k : Type} [CommRing k] {B X Y : Scheme.{0}} {q : B ⟶ Sp k} (hq : IsProjOver q)
    {f : X ⟶ B} {g : Y ⟶ B} (hf : IsProjOver (f ≫ q)) (hg : IsProjOver (g ≫ q)) :
    IsProjOver (pullback.fst f g ≫ f ≫ q) := by
  have : IsProper q := projProper k B q hq
  have h := ProjSpace.isProjOver_comp_of_isClosedImmersion (pullback.mapDesc f g q)
    (ProjSpace.isProjOver_pullback hf hg)
  rwa [pullback.lift_fst_assoc, Category.comp_id] at h

theorem exists_widePullback {k : Type} [CommRing k] {B : Scheme.{0}} {q : B ⟶ Sp k} (hq : IsProjOver q)
    (ι : Type) [Finite ι] : ∀ (Z : ι → Scheme.{0}) (ρ : ∀ a, Z a ⟶ B), (∀ a, IsProjOver (ρ a ≫ q)) →
      ∃ (Y : Scheme.{0}) (π : Y ⟶ B) (p : ∀ a, Y ⟶ Z a), (∀ a, p a ≫ ρ a = π) ∧ IsProjOver (π ≫ q) ∧
        ∀ (T : Scheme.{0}) (g : T ⟶ B) (h : ∀ a, T ⟶ Z a), (∀ a, h a ≫ ρ a = g) →
          ∃! g' : T ⟶ Y, g' ≫ π = g ∧ ∀ a, g' ≫ p a = h a := by
  induction ι using Finite.induction_empty_option with
  | @of_equiv α β e ih =>
    intro Z ρ hρ
    obtain ⟨Y, π, p, hp, hY, H⟩ := ih (fun a => Z (e a)) (fun a => ρ (e a)) fun a => hρ _
    let p' : ∀ b, Y ⟶ Z b := Equiv.piCongrLeft (fun b => Y ⟶ Z b) e p
    have hp' (a : α) : p' (e a) = p a := Equiv.piCongrLeft_apply_apply _ _ _ _
    refine ⟨Y, π, p', e.forall_congr_right.1 fun a => by rw [hp', hp], hY, fun T g h hh => ?_⟩
    obtain ⟨g', ⟨h₁, h₂⟩, u⟩ := H T g (fun a => h (e a)) fun a => hh _
    exact ⟨g', ⟨h₁, e.forall_congr_right.1 fun a => by rw [hp', h₂]⟩,
      fun y hy => u y ⟨hy.1, fun a => by rw [← hp', hy.2]⟩⟩
  | h_empty =>
    intro Z ρ _
    exact ⟨B, 𝟙 B, fun a => a.elim, fun a => a.elim, by rwa [Category.id_comp],
      fun T g _ _ => ⟨g, ⟨Category.comp_id g, fun a => a.elim⟩, fun y hy => (Category.comp_id y).symm.trans hy.1⟩⟩
  | @h_option α _ ih =>
    intro Z ρ hρ
    obtain ⟨Y, π, p, hp, hY, H⟩ := ih (fun a => Z (some a)) (fun a => ρ (some a)) fun a => hρ _
    refine ⟨pullback π (ρ none), pullback.fst _ _ ≫ π,
      fun a => Option.rec (pullback.snd _ _) (fun a => pullback.fst _ _ ≫ p a) a, ?_,
      by simpa only [Category.assoc] using isProjOver_pullback_over hq hY (hρ none), fun T g h hh => ?_⟩
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

def compIso {X Y B : Scheme.{0}} (p : X ⟶ Y) (ρ : Y ⟶ B) {π : X ⟶ B} (w : p ≫ ρ = π) (E : B.Modules) :
    (Scheme.Modules.pullback p).obj ((Scheme.Modules.pullback ρ).obj E) ≅ (Scheme.Modules.pullback π).obj E :=
  (Scheme.Modules.pullbackComp p ρ).app E ≪≫ (Scheme.Modules.pullbackCongr w).app E

theorem compIso_assoc {T X Y B : Scheme.{0}} (t : T ⟶ X) (p : X ⟶ Y) (ρ : Y ⟶ B) {π : X ⟶ B} (w : p ≫ ρ = π)
    {g : T ⟶ B} (w' : t ≫ π = g) (w'' : (t ≫ p) ≫ ρ = g) (E : B.Modules) :
    (Scheme.Modules.pullback t).map (compIso p ρ w E).hom ≫ (compIso t π w' E).hom =
      (Scheme.Modules.pullbackComp t p).hom.app _ ≫ (compIso (t ≫ p) ρ w'' E).hom := by
  subst w w'
  have h := Scheme.Modules.pseudofunctor_associativity t p ρ
  rw [Iso.inv_comp_eq, ← Functor.isoWhiskerRight_inv, Iso.inv_comp_eq] at h
  have h' := congrArg (fun φ => φ.app E) h
  simp [compIso, Scheme.Modules.pullbackCongr] at h' ⊢
  simpa using h'.symm

def Induces {T Y B : Scheme.{0}} (t : T ⟶ Y) (π : Y ⟶ B) {g : T ⟶ B} (w : t ≫ π = g) {E : B.Modules} {n : ℕ}
    (fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) n) (fl' : Vert.Flag ((Scheme.Modules.pullback g).obj E) n) : Prop :=
  ∀ i, ∃ e : (Scheme.Modules.pullback t).obj (fl.F i) ≅ fl'.F i,
    e.hom ≫ fl'.ι i = (Scheme.Modules.pullback t).map (fl.ι i) ≫ (compIso t π w E).hom

theorem Induces.congr {T Y B : Scheme.{0}} {t t' : T ⟶ Y} {π : Y ⟶ B} {g : T ⟶ B} {w : t ≫ π = g} {E : B.Modules} {n : ℕ}
    {fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) n} {fl' : Vert.Flag ((Scheme.Modules.pullback g).obj E) n}
    (h : Induces t π w fl fl') (e : t = t') (w' : t' ≫ π = g) : Induces t' π w' fl fl' := by
  subst e
  exact h

theorem induces_pull_iff {T X Y B : Scheme.{0}} (t : T ⟶ X) (p : X ⟶ Y) (ρ : Y ⟶ B) {π : X ⟶ B} (w : p ≫ ρ = π)
    {g : T ⟶ B} (w' : t ≫ π = g) (w'' : (t ≫ p) ≫ ρ = g) {E : B.Modules} {n : ℕ}
    (fl : Vert.Flag ((Scheme.Modules.pullback ρ).obj E) n) (fl' : Vert.Flag ((Scheme.Modules.pullback g).obj E) n) :
    Induces t π w' ((fl.pull p).ofIso (compIso p ρ w E)) fl' ↔ Induces (t ≫ p) ρ w'' fl fl' := by
  refine forall_congr' fun i => ?_
  have key : (Scheme.Modules.pullback t).map ((Scheme.Modules.pullback p).map (fl.ι i) ≫ (compIso p ρ w E).hom) ≫
      (compIso t π w' E).hom = (Scheme.Modules.pullbackComp t p).hom.app (fl.F i) ≫
        (Scheme.Modules.pullback (t ≫ p)).map (fl.ι i) ≫ (compIso (t ≫ p) ρ w'' E).hom := by
    rw [Functor.map_comp, Category.assoc, compIso_assoc t p ρ w w' w'',
      ← (Scheme.Modules.pullbackComp t p).hom.naturality_assoc]
    rfl
  constructor
  · rintro ⟨e, he⟩
    refine ⟨((Scheme.Modules.pullbackComp t p).app (fl.F i)).symm ≪≫ e, ?_⟩
    rw [Iso.trans_hom, Category.assoc, Iso.symm_hom, Iso.inv_comp_eq]
    exact he.trans key
  · rintro ⟨e, he⟩
    refine ⟨(Scheme.Modules.pullbackComp t p).app (fl.F i) ≪≫ e, ?_⟩
    rw [Iso.trans_hom, Category.assoc, he]
    exact key.symm

theorem isFlagBundle_of_widePullback {B Y : Scheme.{0}} {ι : Type} (E : ι → B.Modules) (r : ι → ℕ)
    {Z : ι → Scheme.{0}} (ρ : ∀ a, Z a ⟶ B)
    (fl : ∀ a, Unit → Vert.Flag ((Scheme.Modules.pullback (ρ a)).obj (E a)) (r a))
    (hfl : ∀ a, IsFlagBundle (ρ a) (fun _ : Unit => E a) (fun _ => r a) (fl a))
    (π : Y ⟶ B) (p : ∀ a, Y ⟶ Z a) (hp : ∀ a, p a ≫ ρ a = π)
    (H : ∀ (T : Scheme.{0}) (g : T ⟶ B) (h : ∀ a, T ⟶ Z a), (∀ a, h a ≫ ρ a = g) →
      ∃! g' : T ⟶ Y, g' ≫ π = g ∧ ∀ a, g' ≫ p a = h a) :
    IsFlagBundle π E r fun a => ((fl a ()).pull (p a)).ofIso (compIso (p a) (ρ a) (hp a) (E a)) := by
  intro T g fl'
  have h₀ (a : ι) : ∃! h : T ⟶ Z a, ∃ w : h ≫ ρ a = g, ∀ _ : Unit, Induces h (ρ a) w (fl a ()) (fl' a) :=
    hfl a T g fun _ => fl' a
  choose h hh u using h₀
  choose w hw using hh
  obtain ⟨g', ⟨h₁, h₂⟩, u'⟩ := H T g h w
  have w₂ (y : T ⟶ Y) (hy : y ≫ π = g) (a : ι) : (y ≫ p a) ≫ ρ a = g := by rw [Category.assoc, hp, hy]
  refine ⟨g', ⟨h₁, fun a => ?_⟩, fun y ⟨hy, hy'⟩ => u' y ⟨hy, fun a => u a _ ⟨w₂ y hy a, fun _ => ?_⟩⟩⟩
  · refine (induces_pull_iff g' (p a) (ρ a) (hp a) h₁ (w₂ g' h₁ a) (fl a ()) (fl' a)).2 ?_
    exact (hw a ()).congr (h₂ a).symm _
  · exact (induces_pull_iff y (p a) (ρ a) (hp a) hy (w₂ y hy a) (fl a ()) (fl' a)).1 (hy' a)

theorem exists_isFlagBundle_isProjOver : ∀ (k : Type) [CommRing k] (B : Scheme.{0}) (q : B ⟶ Sp k) (ι : Type) [Fintype ι] (E : ι → B.Modules) (r : ι → ℕ), IsProjOver q → (∀ a, ∃ (Y : Scheme.{0}) (π : Y ⟶ B) (fl : ∀ _ : Unit, GlobalTheory.Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (r a)), GlobalTheory.CovTest.IsFlagBundle π (fun _ : Unit => E a) (fun _ => r a) fl ∧ IsProjOver (π ≫ q)) → ∃ (Y : Scheme.{0}) (π : Y ⟶ B) (fl : ∀ a, GlobalTheory.Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (r a)), GlobalTheory.CovTest.IsFlagBundle π E r fl ∧ IsProjOver (π ≫ q) := by
  intro k _ B q ι _ E r hq h
  choose Z ρ fl hfl hρ using h
  obtain ⟨Y, π, p, hp, hY, H⟩ := exists_widePullback hq ι Z ρ hρ
  exact ⟨Y, π, _, isFlagBundle_of_widePullback E r ρ fl hfl π p hp H, hY⟩

end GlobalTheory.FlagFamily
