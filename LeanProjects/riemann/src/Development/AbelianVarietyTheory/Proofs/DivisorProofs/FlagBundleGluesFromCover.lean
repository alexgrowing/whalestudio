import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullFlag
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MonoPullbackOfIsOpenImmersion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleUniqueUpToIso
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsRepresentableOfCover

open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace GlobalTheory.FlagGlue

open CategoryTheory Limits TopologicalSpace Opposite
open GlobalTheory.FlagLocal

section Cmp

variable {S T U X : Scheme.{0}}

def pcmp (h : T ⟶ U) (g : U ⟶ X) (k : T ⟶ X) (w : h ≫ g = k) :
    Scheme.Modules.pullback g ⋙ Scheme.Modules.pullback h ≅ Scheme.Modules.pullback k :=
  Scheme.Modules.pullbackComp h g ≪≫ Scheme.Modules.pullbackCongr w

@[reassoc]
theorem pcmp_hom_app (h : T ⟶ U) (g : U ⟶ X) (k : T ⟶ X) (w : h ≫ g = k) (M : X.Modules) :
    (pcmp h g k w).hom.app M =
      (Scheme.Modules.pullbackComp h g).hom.app M ≫ (Scheme.Modules.pullbackCongr w).hom.app M := rfl

theorem pcmp_rfl_hom_app (h : T ⟶ U) (g : U ⟶ X) (M : X.Modules) :
    (pcmp h g _ rfl).hom.app M = (Scheme.Modules.pullbackComp h g).hom.app M := by
  simp [pcmp, Scheme.Modules.pullbackCongr]

theorem pcmp_id_hom_app (g : U ⟶ X) (w : 𝟙 U ≫ g = g) (M : X.Modules) :
    (pcmp (𝟙 U) g g w).hom.app M =
      (Scheme.Modules.pullbackId U).hom.app ((Scheme.Modules.pullback g).obj M) :=
  pullbackComp_congr_id_app g w M

@[reassoc]
theorem pcmp_nat (h : T ⟶ U) (g : U ⟶ X) (k : T ⟶ X) (w : h ≫ g = k) {M N : X.Modules} (φ : M ⟶ N) :
    (Scheme.Modules.pullback h).map ((Scheme.Modules.pullback g).map φ) ≫ (pcmp h g k w).hom.app N =
      (pcmp h g k w).hom.app M ≫ (Scheme.Modules.pullback k).map φ :=
  (pcmp h g k w).hom.naturality φ

theorem pcmp_assoc (t : S ⟶ T) (h : T ⟶ U) (g : U ⟶ X) (k : T ⟶ X) (w : h ≫ g = k)
    (m : S ⟶ X) (w₁ : t ≫ k = m) (k' : S ⟶ U) (w' : t ≫ h = k') (w₂ : k' ≫ g = m) (M : X.Modules) :
    (Scheme.Modules.pullback t).map ((pcmp h g k w).hom.app M) ≫ (pcmp t k m w₁).hom.app M =
      (pcmp t h k' w').hom.app ((Scheme.Modules.pullback g).obj M) ≫ (pcmp k' g m w₂).hom.app M := by
  subst w w' w₁
  have := pullbackComp_congr_assoc_app g h (h ≫ g) rfl t (t ≫ h ≫ g) rfl w₂ M
  simp only [pcmp_hom_app, Category.assoc]
  rw [← this]
  simp [Scheme.Modules.pullbackCongr]

end Cmp

theorem ofIso_ι {X : Scheme.{0}} {M M' : X.Modules} {n : ℕ} (fl : Vert.Flag M n) (e : M ≅ M')
    (i : Fin (n + 1)) : (fl.ofIso e).ι i = fl.ι i ≫ e.hom := rfl

theorem range_sub_of_same {X : Scheme.{0}} {A A' M : X.Modules} {u : A ⟶ M} {v : A' ⟶ M}
    (h : Same u v) (V : X.Opens) : Set.range (u.app V) ⊆ Set.range (v.app V) := by
  obtain ⟨e, rfl⟩ := h
  rintro _ ⟨m, rfl⟩
  exact ⟨e.hom.app V m, QCoh.app_app _ _ _ _⟩

variable {B : Scheme.{0}} {ι : Type} {E : ι → B.Modules} {r : ι → ℕ}

variable (E r) in

abbrev Fls {T : Scheme.{0}} (g : T ⟶ B) := ∀ a, Vert.Flag ((Scheme.Modules.pullback g).obj (E a)) (r a)

def stepRg {T : Scheme.{0}} {g : T ⟶ B} (fl : Fls E r g) :
    ∀ a (i : Fin (r a + 1)) (V : T.Opens), Set Γ((Scheme.Modules.pullback g).obj (E a), V) :=
  fun a i V => Set.range (((fl a).ι i).app V)

def FlEq {T : Scheme.{0}} {g : T ⟶ B} (fl fl' : Fls E r g) : Prop :=
  ∀ a i, Same ((fl a).ι i) ((fl' a).ι i)

theorem stepRg_eq_iff {T : Scheme.{0}} {g : T ⟶ B} (fl fl' : Fls E r g) :
    stepRg fl = stepRg fl' ↔ FlEq fl fl' := by
  refine ⟨fun h a i => same_of_range fun V => congrFun (congrFun (congrFun h a) i) V, fun h => ?_⟩
  funext a i V
  exact (range_sub_of_same (h a i) V).antisymm (range_sub_of_same (h a i).symm V)

variable (E r) in

abbrev FPt (T : Scheme.{0}) : Type :=
  Σ g : T ⟶ B, {S : ∀ a (i : Fin (r a + 1)) (V : T.Opens), Set Γ((Scheme.Modules.pullback g).obj (E a), V) //
    ∃ fl : Fls E r g, stepRg fl = S}

def fpt {T : Scheme.{0}} (g : T ⟶ B) (fl : Fls E r g) : FPt E r T := ⟨g, stepRg fl, fl, rfl⟩

def FPt.fl {T : Scheme.{0}} (x : FPt E r T) : Fls E r x.1 := x.2.2.choose

theorem FPt.eta {T : Scheme.{0}} (x : FPt E r T) : x = fpt x.1 (FPt.fl x) := by
  obtain ⟨g, S, h⟩ := x
  exact congrArg (Sigma.mk g) (Subtype.ext h.choose_spec.symm)

theorem fpt_eq_iff {T : Scheme.{0}} {g : T ⟶ B} (fl fl' : Fls E r g) : fpt g fl = fpt g fl' ↔ FlEq fl fl' := by
  rw [← stepRg_eq_iff]
  constructor
  · intro h
    rw [fpt, fpt, Sigma.mk.inj_iff] at h
    exact congrArg Subtype.val (eq_of_heq h.2)
  · intro h
    exact congrArg (Sigma.mk g) (Subtype.ext h)

def pullFl {S T : Scheme.{0}} (h : S ⟶ T) {g : T ⟶ B} {k : S ⟶ B} (w : h ≫ g = k) (fl : Fls E r g) :
    Fls E r k :=
  fun a => ((fl a).pull h).ofIso ((pcmp h g k w).app (E a))

theorem pullFl_ι {S T : Scheme.{0}} (h : S ⟶ T) {g : T ⟶ B} {k : S ⟶ B} (w : h ≫ g = k) (fl : Fls E r g)
    (a : ι) (i : Fin (r a + 1)) :
    (pullFl h w fl a).ι i = (Scheme.Modules.pullback h).map ((fl a).ι i) ≫ (pcmp h g k w).hom.app (E a) := rfl

theorem FlEq.pull {S T : Scheme.{0}} {g : T ⟶ B} {fl fl' : Fls E r g} (H : FlEq fl fl') (h : S ⟶ T)
    {k : S ⟶ B} (w : h ≫ g = k) : FlEq (pullFl h w fl) (pullFl h w fl') :=
  fun a i => ((H a i).pull h).comp _

def FPt.map {S T : Scheme.{0}} (h : S ⟶ T) (x : FPt E r T) : FPt E r S := fpt (h ≫ x.1) (pullFl h rfl (FPt.fl x))

theorem fpt_map {S T : Scheme.{0}} (h : S ⟶ T) {g : T ⟶ B} (fl : Fls E r g) {k : S ⟶ B} (w : h ≫ g = k) :
    FPt.map h (fpt g fl) = fpt k (pullFl h w fl) := by
  subst w
  refine (fpt_eq_iff _ _).2 (FlEq.pull ?_ h rfl)
  exact (stepRg_eq_iff _ _).1 (fpt g fl).2.2.choose_spec

theorem FPt.map_id {T : Scheme.{0}} (x : FPt E r T) : FPt.map (𝟙 T) x = x := by
  obtain ⟨g, fl, rfl⟩ : ∃ g fl, x = fpt g fl := ⟨_, _, x.eta⟩
  rw [fpt_map (𝟙 T) fl (Category.id_comp g), fpt_eq_iff]
  intro a i
  refine ⟨(Scheme.Modules.pullbackId T).app ((fl a).F i), ?_⟩
  rw [pullFl_ι, pcmp_id_hom_app]
  exact ((Scheme.Modules.pullbackId T).hom.naturality ((fl a).ι i)).symm

theorem FPt.map_comp {R S T : Scheme.{0}} (b : R ⟶ S) (a : S ⟶ T) (x : FPt E r T) :
    FPt.map (b ≫ a) x = FPt.map b (FPt.map a x) := by
  obtain ⟨g, fl, rfl⟩ : ∃ g fl, x = fpt g fl := ⟨_, _, x.eta⟩
  rw [fpt_map (b ≫ a) fl (Category.assoc b a g), fpt_map a fl rfl, fpt_map b _ rfl, fpt_eq_iff]
  intro c i
  refine ⟨((pcmp b a (b ≫ a) rfl).app ((fl c).F i)).symm, ?_⟩
  simp only [pullFl_ι, ofIso_ι, Iso.symm_hom, Iso.app_inv, Iso.app_hom, Functor.map_comp, Category.assoc]
  rw [pcmp_assoc b a g (a ≫ g) rfl (b ≫ a ≫ g) rfl (b ≫ a) rfl (Category.assoc b a g), pcmp_nat_assoc,
    Iso.inv_hom_id_app_assoc]

variable (E r) in

def flagFunctor : Scheme.{0}ᵒᵖ ⥤ Type where
  obj T := FPt E r T.unop
  map h := TypeCat.ofHom (FPt.map h.unop)
  map_id T := by
    exact ConcreteCategory.hom_ext _ _ fun x => FPt.map_id x
  map_comp a b := by
    exact ConcreteCategory.hom_ext _ _ fun x => FPt.map_comp _ _ x

variable (E r) in

def flagProj : flagFunctor E r ⟶ yoneda.obj B where
  app T := TypeCat.ofHom fun x => x.1

theorem FPt.ext_cover {Z : Scheme.{0}} (𝒰 : Z.OpenCover) {y y' : FPt E r Z}
    (e : ∀ i, FPt.map (𝒰.f i) y = FPt.map (𝒰.f i) y') : y = y' := by
  obtain ⟨g, fl, rfl⟩ : ∃ g fl, y = fpt g fl := ⟨_, _, y.eta⟩
  obtain ⟨g', fl', rfl⟩ : ∃ g fl, y' = fpt g fl := ⟨_, _, y'.eta⟩
  obtain rfl : g = g' := 𝒰.hom_ext _ _ fun i => congrArg Sigma.fst (e i)
  refine (fpt_eq_iff _ _).2 fun a k => same_of_cover 𝒰.f 𝒰.exists_eq fun i => ?_
  have := (fpt_eq_iff _ _).1 (((fpt_map _ fl rfl).symm.trans (e i)).trans (fpt_map _ fl' rfl)) a k
  rw [pullFl_ι, pullFl_ι] at this
  exact (same_comp_iff _).1 this

theorem FPt.exists_glue {Z : Scheme.{0}} (𝒰 : Z.OpenCover) (x : ∀ i, FPt E r (𝒰.X i))
    (hx : ∀ i j (S : Scheme.{0}) (b : S ⟶ 𝒰.X i) (c : S ⟶ 𝒰.X j), b ≫ 𝒰.f i = c ≫ 𝒰.f j →
      FPt.map b (x i) = FPt.map c (x j)) : ∃ y : FPt E r Z, ∀ i, FPt.map (𝒰.f i) y = x i := by
  obtain ⟨f, hf⟩ : ∃ f : Z ⟶ B, ∀ i, 𝒰.f i ≫ f = (x i).1 :=
    ⟨𝒰.glueMorphisms (fun i => (x i).1) fun i j =>
      congrArg Sigma.fst (hx i j _ _ _ pullback.condition), fun i => 𝒰.ι_glueMorphisms _ _ i⟩
  let G : ∀ i a, Vert.Flag ((Scheme.Modules.pullback (𝒰.f i)).obj ((Scheme.Modules.pullback f).obj (E a))) (r a) :=
    fun i a => (FPt.fl (x i) a).ofIso ((pcmp (𝒰.f i) f _ (hf i)).app (E a)).symm
  have hG : ∀ a k, Compat 𝒰.f fun i => (G i a).ι k := by
    intro a k i j S b c w
    have w1 : b ≫ (x i).1 = c ≫ (x j).1 := by
      rw [← hf i, ← hf j, ← Category.assoc, w, Category.assoc]
    have w5 : (c ≫ 𝒰.f j) ≫ f = c ≫ (x j).1 := by rw [Category.assoc, hf j]
    have hij : FPt.map b (fpt _ (FPt.fl (x i))) = FPt.map c (fpt _ (FPt.fl (x j))) := by
      rw [← (x i).eta, ← (x j).eta]
      exact hx i j S b c w
    rw [fpt_map b _ w1, fpt_map c _ rfl, fpt_eq_iff] at hij
    have e1 := pcmp_assoc b (𝒰.f i) f (x i).1 (hf i) (c ≫ (x j).1) w1 (c ≫ 𝒰.f j) w w5 (E a)
    have e2 := pcmp_assoc c (𝒰.f j) f (x j).1 (hf j) (c ≫ (x j).1) rfl (c ≫ 𝒰.f j) rfl w5 (E a)
    have h1 := hij a k
    rw [pullFl_ι, pullFl_ι] at h1
    rw [← same_comp_iff ((pcmp (c ≫ 𝒰.f j) f (c ≫ (x j).1) w5).hom.app (E a))]
    simp only [G, ofIso_ι, Iso.symm_hom, Iso.app_inv, Functor.map_comp, Category.assoc]
    rw [← pcmp_hom_app_assoc, ← pcmp_rfl_hom_app, ← e1, ← e2]
    simp only [← Functor.map_comp_assoc, Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
    exact h1
  choose fl₀ hfl₀ using fun a => exists_flag_of_cover 𝒰.f 𝒰.exists_eq (fun i => G i a) (hG a)
  refine ⟨fpt f fl₀, fun i => ((fpt_map _ fl₀ (hf i)).trans ?_).trans (x i).eta.symm⟩
  refine (fpt_eq_iff _ _).2 fun a k => ?_
  have := (hfl₀ a i k).comp ((pcmp (𝒰.f i) f _ (hf i)).hom.app (E a))
  simp only [G, ofIso_ι, Iso.symm_hom, Iso.app_inv, Category.assoc, Iso.inv_hom_id_app,
    Category.comp_id] at this
  rw [pullFl_ι]
  exact this

theorem isSheaf_flagFunctor : Presieve.IsSheaf Scheme.zariskiTopology (flagFunctor E r) := by
  rw [Precoverage.isSheaf_toGrothendieck_iff_of_isStableUnderBaseChange]
  rintro Y P hP
  obtain ⟨(𝒰 : Scheme.OpenCover Y), rfl⟩ := Scheme.exists_cover_of_mem_pretopology hP
  rw [Presieve.isSheafFor_arrows_iff]
  intro x hx
  exact existsUnique_of_exists_of_unique (FPt.exists_glue 𝒰 x fun i j S b c h => hx i j S b c h)
    fun y y' h h' => FPt.ext_cover 𝒰 fun i => (h i).trans (h' i).symm

theorem exists_isFlagBundle_of_cover : ∀ (B : Scheme.{0}) (ι : Type) [Fintype ι] (E : ι → B.Modules) (r : ι → ℕ), (∀ a, GlobalTheory.VB.IsVB (E a) (r a)) → (∀ x : B, ∃ U : B.Opens, x ∈ U ∧ ∃ (Y : Scheme.{0}) (π : Y ⟶ U.toScheme) (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj ((Scheme.Modules.pullback U.ι).obj (E a))) (r a)), IsFlagBundle π (fun a => (Scheme.Modules.pullback U.ι).obj (E a)) r fl) → ∃ (Y : Scheme.{0}) (π : Y ⟶ B) (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (r a)), IsFlagBundle π E r fl := by
  intro B ι _ E r _ hU
  choose U hxU Y π fl hfb using hU
  let fly : ∀ x, Fls E r (π x ≫ (U x).ι) := fun x a => (fl x a).ofIso ((pcmp (π x) (U x).ι _ rfl).app (E a))
  have hrep : (flagFunctor E r).IsRepresentable := by
    refine GlobalTheory.GenTorsor.isRepresentable_of_cover (flagFunctor E r) isSheaf_flagFunctor (flagProj E r) U ?_ Y
      (fun x => (fpt (π x ≫ (U x).ι) (fly x) : FPt E r (Y x))) π (fun x => rfl) ?_
    · exact eq_top_iff.2 fun x _ => TopologicalSpace.Opens.mem_iSup.2 ⟨x, hxU x⟩
    · intro i Z x b hb
      obtain ⟨g, flx, rfl⟩ : ∃ g fl, x = fpt g fl := ⟨_, _, FPt.eta x⟩
      have hb' : g = b ≫ (U i).ι := hb
      subst hb'
      let flb : ∀ a, Vert.Flag ((Scheme.Modules.pullback b).obj ((Scheme.Modules.pullback (U i).ι).obj (E a))) (r a) :=
        fun a => (flx a).ofIso ((pcmp b (U i).ι _ rfl).app (E a)).symm
      have key : ∀ (c : Z ⟶ Y i) (wc : c ≫ π i = b),
          (FPt.map c (fpt (π i ≫ (U i).ι) (fly i)) = fpt (b ≫ (U i).ι) flx ↔
            ∀ a k, Same ((Scheme.Modules.pullback c).map ((fl i a).ι k) ≫
              (Scheme.Modules.pullbackComp c (π i)).hom.app _ ≫ (Scheme.Modules.pullbackCongr wc).hom.app _)
              ((flb a).ι k)) := by
        intro c wc
        have w' : c ≫ π i ≫ (U i).ι = b ≫ (U i).ι := by rw [← Category.assoc, wc]
        rw [fpt_map c _ w', fpt_eq_iff]
        refine forall_congr' fun a => forall_congr' fun k => ?_
        rw [← same_comp_iff ((pcmp b (U i).ι _ rfl).hom.app (E a))]
        simp only [flb, fly, pullFl_ι, ofIso_ι, Iso.app_hom, Iso.symm_hom, Iso.app_inv, Functor.map_comp,
          Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
        rw [pcmp_assoc c (π i) (U i).ι _ rfl (b ≫ (U i).ι) w' b wc rfl (E a)]
        simp only [pcmp_hom_app c (π i) b wc, Category.assoc]
      obtain ⟨c, ⟨wc, hc⟩, hu⟩ := hfb i Z b flb
      refine ⟨c, (key c wc).2 hc, fun c' hc' => ?_⟩
      have wc' : c' ≫ π i = b := by
        have := congrArg Sigma.fst hc'
        rw [← cancel_mono (U i).ι, Category.assoc]
        exact this
      exact hu c' ⟨wc', (key c' wc').1 hc'⟩
  obtain ⟨Yu, u, hu⟩ : ∃ (Yu : Scheme.{0}) (u : FPt E r Yu), ∀ (Z : Scheme.{0}) (x : FPt E r Z),
      ∃! c : Z ⟶ Yu, FPt.map c u = x := by
    obtain ⟨Yu, ⟨e⟩⟩ := hrep.has_representation
    have h : ∀ {Z : Scheme.{0}} (c : Z ⟶ Yu), FPt.map c (e.homEquiv (𝟙 Yu)) = e.homEquiv c :=
      fun c => (e.homEquiv_eq c).symm
    exact ⟨Yu, e.homEquiv (𝟙 Yu), fun Z x => ⟨e.homEquiv.symm x,
      (h _).trans (e.homEquiv.apply_symm_apply x), fun c hc => e.homEquiv.eq_symm_apply.2 ((h c).symm.trans hc)⟩⟩
  obtain ⟨g, flu, rfl⟩ : ∃ g fl, u = fpt g fl := ⟨_, _, FPt.eta u⟩
  refine ⟨Yu, g, flu, fun T g' fl' => ?_⟩
  have key2 : ∀ (c : T ⟶ Yu) (wc : c ≫ g = g'), FPt.map c (fpt g flu) = fpt g' fl' ↔
      ∀ a k, Same ((Scheme.Modules.pullback c).map ((flu a).ι k) ≫
        (Scheme.Modules.pullbackComp c g).hom.app (E a) ≫ (Scheme.Modules.pullbackCongr wc).hom.app (E a))
        ((fl' a).ι k) := by
    intro c wc
    rw [fpt_map c flu wc, fpt_eq_iff]
    simp only [FlEq, pullFl_ι, pcmp_hom_app]
  obtain ⟨c, hc, hcu⟩ := hu T (fpt g' fl')
  have wc : c ≫ g = g' := congrArg Sigma.fst hc
  exact ⟨c, ⟨wc, (key2 c wc).1 hc⟩, fun c' ⟨wc', hc'⟩ => hcu c' ((key2 c' wc').2 hc')⟩

end GlobalTheory.FlagGlue
