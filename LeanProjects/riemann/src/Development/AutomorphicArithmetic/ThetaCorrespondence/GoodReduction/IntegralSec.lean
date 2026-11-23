import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralAtSection
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

open GlobalTheory.Cartier in
private theorem UpperTheory.Lit.Nos.IntegralSec.sec_of_rel {X Y : Scheme.{0}} (f : Y ⟶ X) (P M : LB X) (N : LB Y)
    (hP : P.IsLB) (hM : M.IsLB) (w : LB.Iso (M.pull f) N) (w₁ : LB.Iso (P.pull f) N)
    (v : LB.Iso P M) (hv : v.IsGen) (g₀ : Γ(X, ⊤))
    (H : ∀ (n : N.ι) (i : P.ι) (m : M.ι) (V : Y.Opens) (h₁ : V ≤ N.U n ⊓ (P.pull f).U (fun _ => i))
      (h₂ : V ≤ N.U n ⊓ (M.pull f).U (fun _ => m)) (h₃ : V ≤ f ⁻¹ᵁ (M.U m ⊓ P.U i)),
      resG Y h₁ (@id (Γ(Y, N.U n ⊓ (P.pull f).U (fun _ => i))ˣ) (w₁.s (n, fun _ => i))).val =
        resG Y (le_top : V ≤ f ⁻¹ᵁ ⊤) ((f.app ⊤).hom g₀) *
          resG Y h₃ ((f.app _).hom (@id (Γ(X, M.U m ⊓ P.U i)ˣ) (v.s (m, i))).val) *
          resG Y h₂ (@id (Γ(Y, N.U n ⊓ (M.pull f).U (fun _ => m))ˣ) (w.s (n, fun _ => m))).val)
    (t : P.Sec) (b : N.Sec) (hb : SecMaps w₁ (secPull t f) b) :
    ∃ t' : M.Sec, SecMaps w (secPull t' f) b := by
  obtain ⟨u, hu⟩ := GlobalTheory.exists_secMaps hP hM v hv t
  let t' : M.Sec := ⟨fun m => resG X le_top g₀ * u.f m, fun m m' => by
    have e := u.compat m m'
    change resG X _ _ = _ * resG X _ _ at e ⊢
    rw [map_mul, map_mul, resG_resG, resG_resG, e, mul_left_comm]⟩
  refine ⟨t', ?_⟩
  rintro ⟨n, j⟩
  obtain ⟨m, rfl⟩ : ∃ m : M.ι, j = fun _ => m := ⟨j ⟨⟩, rfl⟩
  refine ext_germ fun y hy => ?_
  obtain ⟨i, hi⟩ := LB.mem_of_cover hP (f y)
  let V : Y.Opens := N.U n ⊓ (M.pull f).U (fun _ => m) ⊓ (P.pull f).U (fun _ => i)
  have hyV : y ∈ V := ⟨hy, (pull_U P f (fun _ => i)).ge hi⟩
  have h₂ : V ≤ N.U n ⊓ (M.pull f).U (fun _ => m) := inf_le_left
  have hn : V ≤ N.U n := inf_le_left.trans inf_le_left
  have hq : V ≤ (P.pull f).U (fun _ => i) := inf_le_right
  have hm : V ≤ f ⁻¹ᵁ M.U m := (h₂.trans inf_le_right).trans (pull_U M f (fun _ => m)).le
  have hi' : V ≤ f ⁻¹ᵁ P.U i := hq.trans (pull_U P f (fun _ => i)).le
  have h₃ : V ≤ f ⁻¹ᵁ (M.U m ⊓ P.U i) := le_inf hm hi'
  rw [← germ_resG h₂ y hyV, ← germ_resG h₂ y hyV]
  congr 1
  have e₁ := hb.on n (fun _ => i) hn hq
  have e₂ := H n i m V (le_inf hn hq) h₂ h₃
  have e₃ := congrArg (fun a => resG Y h₃ ((f.app _).hom a)) (hu (m, i))
  simp only [map_mul, app_resG, resG_resG] at e₃
  have e₄ : resG Y hq ((secPull t f).f (fun _ => i)) = resG Y hi' ((f.app _).hom (t.f i)) :=
    resG_resG _ _ _
  have e₅ : resG Y (h₂.trans inf_le_right) ((secPull t' f).f (fun _ => m)) =
      resG Y (le_top : V ≤ f ⁻¹ᵁ ⊤) ((f.app ⊤).hom g₀) * resG Y hm ((f.app _).hom (u.f m)) := by
    refine (resG_resG _ _ _).trans ?_
    change resG Y hm ((f.app _).hom (resG X le_top g₀ * u.f m)) = _
    rw [map_mul, map_mul, app_resG, resG_resG]
    rfl
  rw [map_mul, resG_resG, resG_resG, e₅, e₃]
  refine e₁.trans ?_
  rw [e₂, e₄]
  ring

private theorem UpperTheory.Lit.Nos.IntegralSec.cst_algebraMap {W K' : Type} [CommRing W] [Field K'] [Algebra W K']
    {X Y : Scheme.{0}} (p : X ⟶ Sp W) (f : Y ⟶ X) (q : Y ⟶ Sp K')
    (h : f ≫ p = q ≫ spMap (algebraMap W K')) (V : Y.Opens) (a : W) :
    GlobalTheory.AbLaw.cst q V (algebraMap W K' a) =
      resG Y (le_top : V ≤ f ⁻¹ᵁ ⊤) ((f.app ⊤).hom (p.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of W)).inv.hom a))) := by
  have e : (Scheme.ΓSpecIso (CommRingCat.of W)).inv ≫ p.appTop ≫ f.appTop =
      CommRingCat.ofHom (algebraMap W K') ≫ (Scheme.ΓSpecIso (CommRingCat.of K')).inv ≫ q.appTop := by
    rw [← Scheme.Hom.comp_appTop, h, Scheme.Hom.comp_appTop, ← Scheme.ΓSpecIso_inv_naturality_assoc]
  exact congrArg (fun φ => resG Y (le_top : V ≤ ⊤) (φ.hom a)) e.symm

private theorem UpperTheory.Lit.Nos.IntegralSec.ev_cst {K' : Type} [Field K'] {Y : Scheme.{0}} (q : Y ⟶ Sp K')
    (x : Sp K' ⟶ Y) (hx : x ≫ q = 𝟙 _) (V : Y.Opens) (h : ⊤ ≤ x ⁻¹ᵁ V) (c : K') :
    (Scheme.ΓSpecIso (CommRingCat.of K')).hom.hom ((x.appLE V ⊤ h).hom (GlobalTheory.AbLaw.cst q V c)) = c := by
  have e : (Scheme.ΓSpecIso (CommRingCat.of K')).inv ≫ q.appTop ≫ Y.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op ≫
      x.appLE V ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of K')).hom = 𝟙 _ := by
    rw [Scheme.Hom.map_appLE_assoc]
    have : q.appTop ≫ x.appLE ⊤ ⊤ le_top = 𝟙 _ := by
      have h1 : x.appLE ⊤ ⊤ le_top = x.appTop := (Scheme.Hom.app_eq_appLE x).symm
      rw [h1, ← Scheme.Hom.comp_appTop, hx, Scheme.Hom.id_appTop]
    rw [reassoc_of% this, Iso.inv_hom_id]
  exact congrArg (fun φ => φ.hom c) e

private theorem UpperTheory.Lit.Nos.IntegralSec.ev_pull {W K' : Type} [CommRing W] [Field K'] [Algebra W K']
    {X Y : Scheme.{0}} (f : Y ⟶ X) (x : Sp K' ⟶ Y) (e₀ : Sp W ⟶ X)
    (hx : x ≫ f = spMap (algebraMap W K') ≫ e₀) (U : X.Opens) (V : Y.Opens) (hle : V ≤ f ⁻¹ᵁ U)
    (h : ⊤ ≤ x ⁻¹ᵁ V) (h₀ : ⊤ ≤ e₀ ⁻¹ᵁ U) (s : Γ(X, U)) :
    (Scheme.ΓSpecIso (CommRingCat.of K')).hom.hom ((x.appLE V ⊤ h).hom ((f.appLE U V hle).hom s)) =
      algebraMap W K' ((Scheme.ΓSpecIso (CommRingCat.of W)).hom.hom ((e₀.appLE U ⊤ h₀).hom s)) := by
  have key : ∀ (g g' : Sp K' ⟶ X) (_ : g = g') (k : ⊤ ≤ g ⁻¹ᵁ U) (k' : ⊤ ≤ g' ⁻¹ᵁ U),
      g.appLE U ⊤ k = g'.appLE U ⊤ k' := by
    rintro g _ rfl k k'
    rfl
  have e : f.appLE U V hle ≫ x.appLE V ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of K')).hom =
      e₀.appLE U ⊤ h₀ ≫ (Scheme.ΓSpecIso (CommRingCat.of W)).hom ≫ CommRingCat.ofHom (algebraMap W K') := by
    have h1 : (spMap (algebraMap W K')).appLE ⊤ ⊤ le_top = (spMap (algebraMap W K')).appTop :=
      (Scheme.Hom.app_eq_appLE _).symm
    rw [← Scheme.ΓSpecIso_naturality, ← Category.assoc, ← Category.assoc, Scheme.Hom.appLE_comp_appLE]
    congr 1
    exact (key _ _ hx _ _).trans ((Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm.trans
      (congrArg (e₀.appLE U ⊤ h₀ ≫ ·) h1))
  exact congrArg (fun φ => φ.hom s) e

theorem UpperTheory.Lit.Nos.integralSec :
    ∀ (W K' : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field K'] [Algebra W K'] [IsFractionRing W K'] (G : Over (Sp W)) (P M : LB G.left) (N : LB (pullback G.hom (spMap (algebraMap W K')))), P.IsLB → M.IsLB → N.IsLB → ∀ (w : LB.Iso (M.pull (pullback.fst G.hom (spMap (algebraMap W K')))) N) (w₁ : LB.Iso (P.pull (pullback.fst G.hom (spMap (algebraMap W K')))) N), w.IsGen → w₁.IsGen → GlobalTheory.SectionLattice.IntegralAtSection G.hom w w₁ → ∀ (v : LB.Iso P M) (c : K'), v.IsGen → (∀ (n : N.ι) (i : P.ι) (m : M.ι) (hle : N.U n ⊓ (P.pull (pullback.fst G.hom (spMap (algebraMap W K')))).U (fun _ => i) ⊓ (M.pull (pullback.fst G.hom (spMap (algebraMap W K')))).U (fun _ => m) ≤ pullback.fst G.hom (spMap (algebraMap W K')) ⁻¹ᵁ (M.U m ⊓ P.U i)), GlobalTheory.AbLaw.rs _ (inf_le_left : N.U n ⊓ (P.pull (pullback.fst G.hom (spMap (algebraMap W K')))).U (fun _ => i) ⊓ (M.pull (pullback.fst G.hom (spMap (algebraMap W K')))).U (fun _ => m) ≤ N.U n ⊓ (P.pull (pullback.fst G.hom (spMap (algebraMap W K')))).U (fun _ => i)) (w₁.s (n, fun _ => i)).val = GlobalTheory.AbLaw.cst (pullback.snd G.hom (spMap (algebraMap W K'))) _ c * ((pullback.fst G.hom (spMap (algebraMap W K'))).appLE (M.U m ⊓ P.U i) _ hle).hom (v.s (m, i)).val * GlobalTheory.AbLaw.rs _ (le_inf (inf_le_left.trans inf_le_left) inf_le_right : N.U n ⊓ (P.pull (pullback.fst G.hom (spMap (algebraMap W K')))).U (fun _ => i) ⊓ (M.pull (pullback.fst G.hom (spMap (algebraMap W K')))).U (fun _ => m) ≤ N.U n ⊓ (M.pull (pullback.fst G.hom (spMap (algebraMap W K')))).U (fun _ => m)) (w.s (n, fun _ => m)).val) → ∀ (t : P.Sec) (b : N.Sec), GlobalTheory.Cartier.SecMaps w₁ (GlobalTheory.Cartier.secPull t (pullback.fst G.hom (spMap (algebraMap W K')))) b → ∃ t' : M.Sec, GlobalTheory.Cartier.SecMaps w (GlobalTheory.Cartier.secPull t' (pullback.fst G.hom (spMap (algebraMap W K')))) b := by
  intro W K' _ _ _ _ _ _ G P M N hP hM _ w w₁ _ _ hI v c hv hrel t b hb
  obtain ⟨e₀, -, x, hx₁, hx₂, i, m, n, hi, hm, h₁, h₂, a, ha⟩ := hI
  have hle : ∀ (n : N.ι) (i : P.ι) (m : M.ι), N.U n ⊓ (P.pull (pullback.fst G.hom (spMap (algebraMap W K')))).U (fun _ => i) ⊓ (M.pull (pullback.fst G.hom (spMap (algebraMap W K')))).U (fun _ => m) ≤ pullback.fst G.hom (spMap (algebraMap W K')) ⁻¹ᵁ (M.U m ⊓ P.U i) := fun n i m =>
    le_inf (inf_le_right.trans (GlobalTheory.Cartier.pull_U M _ (fun _ => m)).le)
      ((inf_le_left.trans inf_le_right).trans (GlobalTheory.Cartier.pull_U P _ (fun _ => i)).le)
  have h₃ : ⊤ ≤ x ⁻¹ᵁ (N.U n ⊓ (P.pull (pullback.fst G.hom (spMap (algebraMap W K')))).U (fun _ => i) ⊓ (M.pull (pullback.fst G.hom (spMap (algebraMap W K')))).U (fun _ => m)) :=
    fun y hy => ⟨h₁ hy, (h₂ hy).2⟩
  have h₀ : ⊤ ≤ e₀ ⁻¹ᵁ (M.U m ⊓ P.U i) := fun y hy => ⟨hm hy, hi hy⟩
  have hres : ∀ (U V : (pullback G.hom (spMap (algebraMap W K'))).Opens) (k : V ≤ U) (hU : ⊤ ≤ x ⁻¹ᵁ U)
      (hV : ⊤ ≤ x ⁻¹ᵁ V) (s : Γ(pullback G.hom (spMap (algebraMap W K')), U)),
      (x.appLE V ⊤ hV).hom (GlobalTheory.AbLaw.rs _ k s) = (x.appLE U ⊤ hU).hom s := fun U V k hU hV s =>
    congrArg (fun φ => φ.hom s) (Scheme.Hom.map_appLE x hV (homOfLE k).op)
  have e := congrArg (fun s => (Scheme.ΓSpecIso (CommRingCat.of K')).hom.hom ((x.appLE _ ⊤ h₃).hom s))
    (hrel n i m (hle n i m))
  simp only [map_mul] at e
  erw [hres _ _ _ h₁, hres _ _ _ h₂, UpperTheory.Lit.Nos.IntegralSec.ev_cst _ x hx₂,
    UpperTheory.Lit.Nos.IntegralSec.ev_pull _ x e₀ hx₁ _ _ _ _ h₀] at e
  have hu : IsUnit ((Scheme.ΓSpecIso (CommRingCat.of K')).hom.hom
      ((x.appLE _ ⊤ h₂).hom (w.s (n, fun _ => m)).val)) := ((Units.isUnit _).map _).map _
  have hv₀ : IsUnit ((Scheme.ΓSpecIso (CommRingCat.of W)).hom.hom
      ((e₀.appLE _ ⊤ h₀).hom (v.s (m, i)).val)) := ((Units.isUnit _).map _).map _
  have e' := mul_right_cancel₀ hu.ne_zero (ha.symm.trans e)
  obtain ⟨r, hr⟩ := hv₀.exists_right_inv
  have hc : c = algebraMap W K' (a * r) := by
    rw [map_mul, e', _root_.mul_assoc, ← map_mul]
    exact ((congrArg (fun z => c * algebraMap W K' z) hr).trans (by rw [map_one, _root_.mul_one])).symm
  refine UpperTheory.Lit.Nos.IntegralSec.sec_of_rel _ P M N hP hM w w₁ v hv
    (G.hom.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of W)).inv.hom (a * r))) ?_ t b hb
  intro n i m V k₁ k₂ k₃
  have k : V ≤ N.U n ⊓ (P.pull (pullback.fst G.hom (spMap (algebraMap W K')))).U (fun _ => i) ⊓ (M.pull (pullback.fst G.hom (spMap (algebraMap W K')))).U (fun _ => m) := le_inf k₁ (k₂.trans inf_le_right)
  have e := congrArg (GlobalTheory.AbLaw.rs _ k) (hrel n i m (hle n i m))
  rw [map_mul, map_mul, GlobalTheory.AbLaw.rs_cst, hc,
    UpperTheory.Lit.Nos.IntegralSec.cst_algebraMap G.hom _ _ pullback.condition] at e
  refine ((GlobalTheory.AbLaw.rs_rs _ _ _).symm.trans e).trans ?_
  exact congrArg₂ (· * ·) (congrArg (_ * ·) (GlobalTheory.LB.resG_appLE _ _ k _)) (GlobalTheory.AbLaw.rs_rs _ _ _)
