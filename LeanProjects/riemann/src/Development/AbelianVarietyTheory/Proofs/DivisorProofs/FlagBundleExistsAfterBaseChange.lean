import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BcDensEqOfGram
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB
open CategoryTheory.Limits

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagBaseChange

variable {P Y B T T' : Scheme.{0}}

theorem pullbackComp_assoc_app (f : T' ⟶ P) (g : P ⟶ Y) (h : Y ⟶ B) (M : B.Modules) :
    (Scheme.Modules.pullbackComp f g).hom.app ((Scheme.Modules.pullback h).obj M) ≫
      (Scheme.Modules.pullbackComp (f ≫ g) h).hom.app M =
    (Scheme.Modules.pullback f).map ((Scheme.Modules.pullbackComp g h).hom.app M) ≫
      (Scheme.Modules.pullbackComp f (g ≫ h)).hom.app M ≫ eqToHom (by simp) := by
  have e := NatTrans.congr_app (Scheme.Modules.pseudofunctor_associativity f g h) M
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.whiskerLeft_app, Category.id_comp, eqToHom_app] at e
  rw [← e]
  simp only [← Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app, Iso.hom_inv_id_app_assoc]
  simp

theorem pullbackCongr_hom_app {f f' : P ⟶ B} (H : f = f') (M : B.Modules) :
    (Scheme.Modules.pullbackCongr H).hom.app M = eqToHom (by rw [H]) := by
  subst H; simp [Scheme.Modules.pullbackCongr]

theorem pullbackComp_congr_app (v : T' ⟶ P) {k k' : P ⟶ B} (H : k = k') (M : B.Modules) :
    (Scheme.Modules.pullback v).map ((Scheme.Modules.pullbackCongr H).hom.app M) ≫
      (Scheme.Modules.pullbackComp v k').hom.app M =
    (Scheme.Modules.pullbackComp v k).hom.app M ≫ eqToHom (by rw [H]) := by
  subst H; simp [Scheme.Modules.pullbackCongr]

def baseIso (f₁ : P ⟶ Y) (p : Y ⟶ B) (f₂ : P ⟶ T) (q : T ⟶ B) (cond : f₁ ≫ p = f₂ ≫ q) (M : B.Modules) :
    (Scheme.Modules.pullback f₁).obj ((Scheme.Modules.pullback p).obj M) ≅
      (Scheme.Modules.pullback f₂).obj ((Scheme.Modules.pullback q).obj M) :=
  (Scheme.Modules.pullbackComp f₁ p).app M ≪≫ (Scheme.Modules.pullbackCongr cond).app M ≪≫
    ((Scheme.Modules.pullbackComp f₂ q).app M).symm

theorem baseIso_coherence (f₁ : P ⟶ Y) (p : Y ⟶ B) (f₂ : P ⟶ T) (q : T ⟶ B) (cond : f₁ ≫ p = f₂ ≫ q)
    (v : T' ⟶ P) (w : (v ≫ f₁) ≫ p = (v ≫ f₂) ≫ q) (M : B.Modules) :
    (Scheme.Modules.pullback v).map (baseIso f₁ p f₂ q cond M).hom ≫
        (Scheme.Modules.pullbackComp v f₂).hom.app _ ≫ (Scheme.Modules.pullbackComp (v ≫ f₂) q).hom.app M =
      (Scheme.Modules.pullbackComp v f₁).hom.app _ ≫ (Scheme.Modules.pullbackComp (v ≫ f₁) p).hom.app M ≫
        (Scheme.Modules.pullbackCongr w).hom.app M := by
  rw [pullbackComp_assoc_app, ← Category.assoc ((Scheme.Modules.pullbackComp v f₁).hom.app _),
    pullbackComp_assoc_app]
  simp only [baseIso, Iso.trans_hom, Iso.app_hom, Iso.symm_hom, Iso.app_inv, Functor.map_comp,
    Category.assoc]
  rw [← Functor.map_comp_assoc (Scheme.Modules.pullback v) ((Scheme.Modules.pullbackComp f₂ q).inv.app M),
    Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, Category.id_comp, ← Category.assoc
      ((Scheme.Modules.pullback v).map ((Scheme.Modules.pullbackCongr cond).hom.app M)),
    pullbackComp_congr_app, pullbackCongr_hom_app]
  simp

def sqFlag (f₁ : P ⟶ Y) (p : Y ⟶ B) (f₂ : P ⟶ T) (q : T ⟶ B) (cond : f₁ ≫ p = f₂ ≫ q) {M : B.Modules} {n : ℕ}
    (fl : Vert.Flag ((Scheme.Modules.pullback p).obj M) n) :
    Vert.Flag ((Scheme.Modules.pullback f₂).obj ((Scheme.Modules.pullback q).obj M)) n :=
  (fl.pull f₁).ofIso (baseIso f₁ p f₂ q cond M)

theorem sqFlag_iff (f₁ : P ⟶ Y) (p : Y ⟶ B) (f₂ : P ⟶ T) (q : T ⟶ B) (cond : f₁ ≫ p = f₂ ≫ q)
    {M : B.Modules} {n : ℕ} (fl : Vert.Flag ((Scheme.Modules.pullback p).obj M) n)
    (v : T' ⟶ P) (h : T' ⟶ T) (hv : v ≫ f₂ = h) (w : (v ≫ f₁) ≫ p = h ≫ q)
    (fl'' : Vert.Flag ((Scheme.Modules.pullback h).obj ((Scheme.Modules.pullback q).obj M)) n) (i : Fin (n + 1)) :
    (∃ e : (Scheme.Modules.pullback v).obj ((sqFlag f₁ p f₂ q cond fl).F i) ≅ fl''.F i,
      e.hom ≫ fl''.ι i = (Scheme.Modules.pullback v).map ((sqFlag f₁ p f₂ q cond fl).ι i) ≫
        (Scheme.Modules.pullbackComp v f₂).hom.app _ ≫ (Scheme.Modules.pullbackCongr hv).hom.app _) ↔
    (∃ e : (Scheme.Modules.pullback (v ≫ f₁)).obj (fl.F i) ≅
        (fl''.ofIso ((Scheme.Modules.pullbackComp h q).app M)).F i,
      e.hom ≫ (fl''.ofIso ((Scheme.Modules.pullbackComp h q).app M)).ι i =
        (Scheme.Modules.pullback (v ≫ f₁)).map (fl.ι i) ≫
          (Scheme.Modules.pullbackComp (v ≫ f₁) p).hom.app M ≫ (Scheme.Modules.pullbackCongr w).hom.app M) := by
  subst hv
  have coh := baseIso_coherence f₁ p f₂ q cond v w M
  have nat := (Scheme.Modules.pullbackComp v f₁).hom.naturality (fl.ι i)
  simp only [Functor.comp_map] at nat
  constructor
  · rintro ⟨e, he⟩
    refine ⟨((Scheme.Modules.pullbackComp v f₁).app _).symm ≪≫ e, ?_⟩
    erw [Iso.trans_hom]
    simp only [Vert.Flag.ofIso, sqFlag, Vert.Flag.pull, Iso.symm_hom, Iso.app_inv, Iso.app_hom,
      Category.assoc] at he ⊢
    rw [reassoc_of% he, pullbackCongr_hom_app (f := v ≫ f₂)]
    simp only [eqToHom_refl, Category.id_comp, Functor.map_comp, Category.assoc]
    rw [coh, reassoc_of% nat, Iso.inv_hom_id_app_assoc]
  · rintro ⟨e, he⟩
    refine ⟨(Scheme.Modules.pullbackComp v f₁).app _ ≪≫ e, ?_⟩
    erw [Iso.trans_hom]
    simp only [Vert.Flag.ofIso, sqFlag, Vert.Flag.pull, Iso.app_hom, Category.assoc] at he ⊢
    rw [← cancel_mono ((Scheme.Modules.pullbackComp (v ≫ f₂) q).hom.app M)]
    simp only [Category.assoc]
    rw [he, pullbackCongr_hom_app (f := v ≫ f₂)]
    simp only [eqToHom_refl, Category.id_comp, Functor.map_comp, Category.assoc]
    rw [coh, reassoc_of% nat]

theorem isFlagBundle_pullback_snd : ∀ (B Y T : Scheme.{0}) (π : Y ⟶ B) (g : T ⟶ B) (ι : Type) [Fintype ι]
    (E : ι → B.Modules) (r : ι → ℕ) (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (r a)),
    IsFlagBundle π E r fl → ∃ fl' : ∀ a, Vert.Flag ((Scheme.Modules.pullback (pullback.snd π g)).obj
      ((Scheme.Modules.pullback g).obj (E a))) (r a),
      IsFlagBundle (pullback.snd π g) (fun a => (Scheme.Modules.pullback g).obj (E a)) r fl' := by
  intro B Y T π g ι _ E r fl hfl
  refine ⟨fun a => sqFlag (pullback.fst π g) π (pullback.snd π g) g pullback.condition (fl a), ?_⟩
  intro T' h fl''
  obtain ⟨u, ⟨wu, hu⟩, huniq⟩ := hfl T' (h ≫ g)
    (fun a => (fl'' a).ofIso ((Scheme.Modules.pullbackComp h g).app (E a)))
  have hfst := pullback.lift_fst u h wu
  refine ⟨pullback.lift u h wu, ⟨pullback.lift_snd _ _ _, fun a i => ?_⟩, ?_⟩
  · rw [sqFlag_iff _ _ _ _ _ (fl a) _ h (pullback.lift_snd _ _ _) (by rw [hfst]; exact wu)]
    have key : ∀ (u' : T' ⟶ Y) (e : u' = u) (w' : u' ≫ π = h ≫ g),
        ∃ e : (Scheme.Modules.pullback u').obj ((fl a).F i) ≅
          ((fl'' a).ofIso ((Scheme.Modules.pullbackComp h g).app (E a))).F i,
        e.hom ≫ ((fl'' a).ofIso ((Scheme.Modules.pullbackComp h g).app (E a))).ι i =
          (Scheme.Modules.pullback u').map ((fl a).ι i) ≫
            (Scheme.Modules.pullbackComp u' π).hom.app (E a) ≫ (Scheme.Modules.pullbackCongr w').hom.app (E a) := by
      intro u' e w'
      subst e
      exact hu a i
    exact key _ hfst _
  · rintro v ⟨hv, hprop⟩
    apply pullback.hom_ext
    · rw [pullback.lift_fst]
      have w : (v ≫ pullback.fst π g) ≫ π = h ≫ g := by
        rw [Category.assoc, pullback.condition, ← Category.assoc, hv]
      exact huniq _ ⟨w, fun a i => (sqFlag_iff _ _ _ _ pullback.condition (fl a) v h hv w (fl'' a) i).1
        (hprop a i)⟩
    · rw [pullback.lift_snd]
      exact hv

end GlobalTheory.FlagBaseChange

end
