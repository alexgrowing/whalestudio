import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsSymm
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
noncomputable section
namespace GlobalTheory.KS.DerMor

def preHom {Z X : Scheme.{0}} (n : Z ⟶ X) (c : ∀ W : X.Opens, Γ(X, W) →+* Γ(Z, n ⁻¹ᵁ W))
    (hres : ∀ W W' (h : W' ≤ W) f, c W' (resG X h f) = resG Z (fun _ hy => h hy) (c W f)) :
    Z.toPresheafedSpace ⟶ X.toPresheafedSpace where
  base := n.base
  c :=
    { app := fun W => CommRingCat.ofHom (c W.unop)
      naturality := fun W W' i => by
        ext f
        exact hres W.unop W'.unop i.unop.le f }

def deform {Z X : Scheme.{0}} (n : Z ⟶ X) (c : ∀ W : X.Opens, Γ(X, W) →+* Γ(Z, n ⁻¹ᵁ W))
    (hres : ∀ W W' (h : W' ≤ W) f, c W' (resG X h f) = resG Z (fun _ hy => h hy) (c W f))
    (hnil : ∀ W f, IsNilpotent (c W f - (n.app W).hom f)) : Z ⟶ X :=
  ⟨⟨preHom n c hres, fun x => ⟨fun a ha => by
    obtain ⟨U, hU, s, rfl⟩ := TopCat.Presheaf.germ_exist X.presheaf a
    have hU' : n x ∈ U := hU
    have h1 := PresheafedSpace.stalkMap_germ_apply (preHom n c hres) U x hU s
    have h2 : IsUnit ((Z.presheaf.germ (n ⁻¹ᵁ U) x hU').hom (c U s)) := by
      have ha' := ha
      erw [h1] at ha'
      exact ha'
    have h3 : IsUnit ((Z.presheaf.germ (n ⁻¹ᵁ U) x hU').hom ((n.app U).hom s)) := by
      have hn := ((hnil U s).map (Z.presheaf.germ (n ⁻¹ᵁ U) x hU').hom).neg
      have := hn.isUnit_add_left_of_commute h2 (Commute.all _ _)
      simpa using this
    have h4 := Scheme.Hom.germ_stalkMap_apply n U x hU' s
    have h5 : IsUnit ((n.stalkMap x).hom ((X.presheaf.germ U (n x) hU').hom s)) := by
      erw [h4]
      exact h3
    exact (isUnit_map_iff (n.stalkMap x).hom _).mp h5⟩⟩⟩

theorem deform_app {Z X : Scheme.{0}} (n : Z ⟶ X) (c : ∀ W : X.Opens, Γ(X, W) →+* Γ(Z, n ⁻¹ᵁ W))
    (hres : ∀ W W' (h : W' ≤ W) f, c W' (resG X h f) = resG Z (fun _ hy => h hy) (c W f))
    (hnil : ∀ W f, IsNilpotent (c W f - (n.app W).hom f)) (W : X.Opens) :
    (deform n c hres hnil).app W = CommRingCat.ofHom (c W) := rfl

def cH {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) (U : X.Opens) : R →+* Γ(X, U) :=
  ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ p.appLE ⊤ U le_top).hom

theorem cH_eq {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) (U : X.Opens) (a : R) :
    constFn p U a = cH p U a := rfl

theorem appLE_cH {R : Type} [CommRing R] {X Y : Scheme.{0}} (p : X ⟶ Sp R) (f : Y ⟶ X) (U : X.Opens)
    (V : Y.Opens) (e : V ≤ f ⁻¹ᵁ U) (a : R) :
    (f.appLE U V e).hom (cH p U a) = cH (f ≫ p) V a := by
  unfold cH
  have key := Scheme.Hom.appLE_comp_appLE f p ⊤ U V le_top e
  rw [← CommRingCat.comp_apply, Category.assoc]
  exact congrArg (fun φ => ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ φ).hom a) key

theorem app_cH {R : Type} [CommRing R] {X Y : Scheme.{0}} (p : X ⟶ Sp R) (f : Y ⟶ X) (U : X.Opens)
    (a : R) : (f.app U).hom (cH p U a) = cH (f ≫ p) (f ⁻¹ᵁ U) a := by
  rw [Scheme.Hom.app_eq_appLE]
  exact appLE_cH p f U (f ⁻¹ᵁ U) le_rfl a

theorem res_cH {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) {U V : X.Opens} (h : V ≤ U)
    (a : R) : resG X h (cH p U a) = cH p V a := by
  unfold cH resG
  have key := Scheme.Hom.appLE_map p (U := ⊤) (V := U) (V' := V) le_top (homOfLE h).op
  rw [← CommRingCat.comp_apply, Category.assoc]
  exact congrArg (fun φ => ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ φ).hom a) key

theorem cH_spMap {R S : Type} [CommRing R] [CommRing S] {X : Scheme.{0}} (q : X ⟶ Sp S) (g : R →+* S)
    (U : X.Opens) (a : R) : cH (q ≫ spMap g) U a = cH q U (g a) := by
  unfold cH spMap
  have k1 := Scheme.Hom.comp_appLE q (Spec.map (CommRingCat.ofHom g)) ⊤ U le_top
  have k3 := congrArg (fun φ => (φ ≫ q.appLE ⊤ U le_top).hom a)
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom g))
  simp only [Category.assoc] at k3
  exact (congrArg (fun φ => ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ φ).hom a) k1).trans k3.symm

theorem res_app {X Y : Scheme.{0}} (f : Y ⟶ X) {U V : X.Opens} (h : V ≤ U) (a : Γ(X, U)) :
    (f.app V).hom (resG X h a) = resG Y (fun _ hy => h hy) ((f.app U).hom a) := by
  unfold resG
  rw [← CommRingCat.comp_apply, Scheme.Hom.naturality, CommRingCat.comp_apply]
  rfl

theorem appLE_app_of_section {Y Y' : Scheme.{0}} (ρ : Y' ⟶ Y) (j : Y ⟶ Y') (h : j ≫ ρ = 𝟙 Y)
    (O : Y.Opens) (e : O ≤ j ⁻¹ᵁ (ρ ⁻¹ᵁ O)) (a : Γ(Y, O)) :
    (j.appLE (ρ ⁻¹ᵁ O) O e).hom ((ρ.app O).hom a) = a := by
  have key : ∀ (g : Y ⟶ Y), g = 𝟙 Y → ∀ e' : O ≤ g ⁻¹ᵁ O, (g.appLE O O e').hom a = a := by
    intro g hg e'
    subst hg
    simp only [Scheme.Hom.appLE, Scheme.Hom.id_app]
    exact congrArg (fun φ => φ.hom a) (Y.presheaf.map_id (Opposite.op O))
  rw [← CommRingCat.comp_apply, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]
  exact key _ h _

theorem ext_cH {R : Type} [CommRing R] {X : Scheme.{0}} (f g : X ⟶ Sp R)
    (h : ∀ a, cH f ⊤ a = cH g ⊤ a) : f = g := by
  have top : ∀ (k : X ⟶ Sp R) (r : R),
      cH k ⊤ r = (Scheme.Γ.map k.op).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) := by
    intro k r
    have e1 : k.appLE ⊤ ⊤ le_top = k.app ⊤ := k.appLE_eq_app
    unfold cH
    rw [e1]
    rfl
  apply ext_to_Spec
  apply CommRingCat.hom_ext
  ext r
  exact (top f r).symm.trans ((h r).trans (top g r))

def pert {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (a : A →+* B) (b : B →+* C) (e : C)
    (he : e * e = 0) (d : A → B) (hadd : ∀ f f', d (f + f') = d f + d f')
    (hmul : ∀ f f', d (f * f') = a f * d f' + a f' * d f) : A →+* C where
  toFun f := b (a f) + e * b (d f)
  map_one' := by
    have h := hmul 1 1
    rw [show (1 : A) * 1 = 1 from mul_one 1, map_one] at h
    have h1 : d 1 = 0 := by linear_combination -h
    simp [h1]
  map_zero' := by
    have h := hadd 0 0
    simp only [add_zero] at h
    have h1 : d 0 = 0 := by linear_combination -h
    simp [h1]
  map_add' f f' := by
    simp only [hadd, map_add]; ring
  map_mul' f f' := by
    simp only [hmul, map_add, map_mul]
    linear_combination (-(b (d f) * b (d f'))) * he

theorem exists_mor : ∀ (Y Y' : Scheme.{0}) (q : Y ⟶ Sp ℂ) (π : Y' ⟶ Sp (DualNumber ℂ)) (ρ : Y' ⟶ Y) (j : Y ⟶ Y'), IsPullback ρ π q (spMap (algebraMap ℂ (DualNumber ℂ))) → j ≫ ρ = 𝟙 Y → j ≫ π = q ≫ (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) → ∀ (R : Type) [CommRing R] (xD : R →+* DualNumber ℂ) (X : Scheme.{0}) (p : X ⟶ Sp R) (m : Y ⟶ X) (d : ∀ W : X.Opens, Γ(X, W) → Γ(Y, m ⁻¹ᵁ W)), m ≫ p = q ≫ (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) ≫ spMap xD → LocDer q p m (fun r => (xD r).snd) ⊤ d → ∃ Φ : Y' ⟶ X, j ≫ Φ = m ∧ Φ ≫ p = π ≫ spMap xD := by
  intro Y Y' q π ρ j hpb hjρ hjπ R _ xD X p m d hmp hd
  have hee : ∀ V : Y'.Opens, cH π V DualNumber.eps * cH π V DualNumber.eps = 0 := by
    intro V
    rw [← map_mul, DualNumber.eps_mul_eps, map_zero]
  let c : ∀ W : X.Opens, Γ(X, W) →+* Γ(Y', (ρ ≫ m) ⁻¹ᵁ W) := fun W =>
    pert (m.app W).hom (ρ.app (m ⁻¹ᵁ W)).hom (cH π _ DualNumber.eps) (hee _) (d W)
      (hd.add W le_top) (hd.mul W le_top)
  have hres : ∀ W W' (h : W' ≤ W) f,
      c W' (resG X h f) = resG Y' (fun _ hy => h hy) (c W f) := by
    intro W W' h f
    show (ρ.app _).hom ((m.app W').hom (resG X h f)) +
        cH π _ DualNumber.eps * (ρ.app _).hom (d W' (resG X h f)) =
      resG Y' _ ((ρ.app _).hom ((m.app W).hom f) + cH π _ DualNumber.eps * (ρ.app _).hom (d W f))
    have h1 := (congrArg (ρ.app (m ⁻¹ᵁ W')).hom (res_app m h f)).trans
      (res_app ρ (U := m ⁻¹ᵁ W) (V := m ⁻¹ᵁ W') (fun _ hy => h hy) ((m.app W).hom f))
    have h2 := (congrArg (ρ.app (m ⁻¹ᵁ W')).hom (hd.res W W' h le_top f)).trans
      (res_app ρ (U := m ⁻¹ᵁ W) (V := m ⁻¹ᵁ W') (fun _ hy => h hy) (d W f))
    have h3 := (res_cH π (U := ρ ⁻¹ᵁ (m ⁻¹ᵁ W)) (V := ρ ⁻¹ᵁ (m ⁻¹ᵁ W')) (fun _ hy => h hy)
      DualNumber.eps).symm
    rw [map_add, map_mul]
    exact congrArg₂ (· + ·) h1 (congrArg₂ (· * ·) h3 h2)
  have hnil : ∀ W f, IsNilpotent (c W f - ((ρ ≫ m).app W).hom f) := by
    intro W f
    refine ⟨2, ?_⟩
    show ((ρ.app _).hom ((m.app W).hom f) + cH π _ DualNumber.eps * (ρ.app _).hom (d W f) -
      (ρ.app _).hom ((m.app W).hom f)) ^ 2 = 0
    rw [add_sub_cancel_left, mul_pow, sq (cH π _ _), hee, zero_mul]
  have hdual : ∀ x : DualNumber ℂ,
      algebraMap ℂ (DualNumber ℂ) x.fst + DualNumber.eps * algebraMap ℂ (DualNumber ℂ) x.snd = x := by
    intro x
    ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]
  have hfst : ∀ z : DualNumber ℂ, (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom z = z.fst := fun z => rfl
  have hq : ∀ (V : Y.Opens) (z : ℂ),
      (ρ.app V).hom (cH q V z) = cH π (ρ ⁻¹ᵁ V) (algebraMap ℂ (DualNumber ℂ) z) := by
    intro V z
    rw [app_cH, hpb.w, cH_spMap]
  have hc : ∀ W (r : R), c W (cH p W r) = cH π ((ρ ≫ m) ⁻¹ᵁ W) (xD r) := by
    intro W r
    show (ρ.app _).hom ((m.app W).hom (cH p W r)) +
      cH π _ DualNumber.eps * (ρ.app _).hom (d W (cH p W r)) = _
    rw [← cH_eq p W r, hd.base W le_top r]
    simp only [cH_eq]
    rw [app_cH, hmp, ← Category.assoc, cH_spMap, cH_spMap, hq, hq, ← map_mul, ← map_add, hfst,
      hdual]
    rfl
  refine ⟨deform (ρ ≫ m) c hres hnil, ?_, ?_⟩
  · have hb : (j ≫ deform (ρ ≫ m) c hres hnil).base = m.base := by
      show (j ≫ ρ ≫ m).base = m.base
      rw [← Category.assoc, hjρ, Category.id_comp]
    refine Scheme.Hom.ext hb ?_
    intro U
    have hle : m ⁻¹ᵁ U ≤ j ⁻¹ᵁ (ρ ⁻¹ᵁ (m ⁻¹ᵁ U)) := by
      intro x hx
      have hx' : (j ≫ ρ) x = x := by rw [hjρ]; rfl
      show (j ≫ ρ) x ∈ m ⁻¹ᵁ U
      rw [hx']
      exact hx
    apply CommRingCat.hom_ext
    ext f
    change (j.appLE (ρ ⁻¹ᵁ (m ⁻¹ᵁ U)) (m ⁻¹ᵁ U) hle).hom
      (((deform (ρ ≫ m) c hres hnil).app U).hom f) = _
    rw [deform_app]
    show (j.appLE _ _ hle).hom ((ρ.app _).hom ((m.app U).hom f) +
      cH π _ DualNumber.eps * (ρ.app _).hom (d U f)) = _
    rw [map_add, map_mul, appLE_app_of_section ρ j hjρ _ hle, appLE_cH, hjπ, cH_spMap, hfst]
    simp
  · apply ext_cH
    intro r
    rw [cH_spMap]
    have e1 := app_cH p (deform (ρ ≫ m) c hres hnil) ⊤ r
    rw [deform_app] at e1
    have e2 := res_cH (deform (ρ ≫ m) c hres hnil ≫ p)
      (U := (deform (ρ ≫ m) c hres hnil) ⁻¹ᵁ ⊤) (V := ⊤) le_top r
    rw [← e2, ← e1]
    show resG Y' _ (c ⊤ (cH p ⊤ r)) = _
    rw [hc]
    exact res_cH π _ _

end GlobalTheory.KS.DerMor
end
