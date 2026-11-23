import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GenericExistsUniqueOActOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianHomExtensionHolds
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.NonemptyTorusExtensionOfIsPowGrp
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

namespace GlobalTheory.Poinc.Sep.PowModel

variable {C : Type*} [Category C] {J : Type*}

theorem isIso_of_prod {X Y Z : C} {p : J → (X ⟶ Z)} {r : J → (Y ⟶ Z)}
    (hX : ∀ (T : C) (y : J → (T ⟶ Z)), ∃! x : T ⟶ X, ∀ a, x ≫ p a = y a)
    (hY : ∀ (T : C) (y : J → (T ⟶ Z)), ∃! x : T ⟶ Y, ∀ a, x ≫ r a = y a)
    (f : X ⟶ Y) (hf : ∀ a, f ≫ r a = p a) : IsIso f := by
  obtain ⟨g, hg, -⟩ := hX Y r
  refine ⟨g, ?_, ?_⟩
  · exact (hX X p).unique (fun a => by rw [Category.assoc, hg, hf]) (fun a => Category.id_comp _)
  · exact (hY Y r).unique (fun a => by rw [Category.assoc, hf, hg]) (fun a => Category.id_comp _)

theorem prod_precomp {X X' Z : C} {p : J → (X ⟶ Z)} (e : X' ≅ X)
    (hX : ∀ (T : C) (y : J → (T ⟶ Z)), ∃! x : T ⟶ X, ∀ a, x ≫ p a = y a) :
    ∀ (T : C) (y : J → (T ⟶ Z)), ∃! x : T ⟶ X', ∀ a, x ≫ (e.hom ≫ p a) = y a := by
  intro T y
  obtain ⟨x, hx, hu⟩ := hX T y
  refine ⟨x ≫ e.inv, fun a => by rw [Category.assoc, Iso.inv_hom_id_assoc, hx], fun x' hx' => ?_⟩
  rw [← hu (x' ≫ e.hom) (fun a => by rw [Category.assoc, hx']), Category.assoc, Iso.hom_inv_id,
    Category.comp_id]

theorem prod_postcomp {X Z Z' : C} {p : J → (X ⟶ Z)} (e : Z ≅ Z')
    (hX : ∀ (T : C) (y : J → (T ⟶ Z)), ∃! x : T ⟶ X, ∀ a, x ≫ p a = y a) :
    ∀ (T : C) (y : J → (T ⟶ Z')), ∃! x : T ⟶ X, ∀ a, x ≫ (p a ≫ e.hom) = y a := by
  intro T y
  obtain ⟨x, hx, hu⟩ := hX T (fun a => y a ≫ e.inv)
  refine ⟨x, fun a => by rw [← Category.assoc, hx, Category.assoc, Iso.inv_hom_id, Category.comp_id],
    fun x' hx' => hu x' (fun a => by rw [← hx' a, Category.assoc, Category.assoc, Iso.hom_inv_id,
      Category.comp_id])⟩

theorem prod_of_isLimit {X Z : C} {p : J → (X ⟶ Z)} (h : IsLimit (Fan.mk X p)) :
    ∀ (T : C) (y : J → (T ⟶ Z)), ∃! x : T ⟶ X, ∀ a, x ≫ p a = y a := fun T y =>
  ⟨Fan.IsLimit.lift h y, fun a => Fan.IsLimit.fac h y a, fun x hx =>
    Fan.IsLimit.hom_ext h _ _ fun a => by
      change x ≫ p a = Fan.IsLimit.lift h y ≫ p a
      rw [hx a]; exact (Fan.IsLimit.fac h y a).symm⟩

theorem prod_pullback {S S' : Scheme.{0}} (j : S' ⟶ S) {X Z : Over S} {p : J → (X ⟶ Z)}
    (hX : ∀ (T : Over S) (y : J → (T ⟶ Z)), ∃! x : T ⟶ X, ∀ a, x ≫ p a = y a) :
    ∀ (T : Over S') (y : J → (T ⟶ (Over.pullback j).obj Z)),
      ∃! x : T ⟶ (Over.pullback j).obj X, ∀ a, x ≫ (Over.pullback j).map (p a) = y a := by
  intro T y
  let adj := Over.mapPullbackAdj j
  obtain ⟨x, hx, hu⟩ := hX _ (fun a => (adj.homEquiv _ _).symm (y a))
  refine ⟨adj.homEquiv _ _ x, fun a => ?_, fun x' hx' => ?_⟩
  · rw [← adj.homEquiv_naturality_right, hx, Equiv.apply_symm_apply]
  · rw [← hu ((adj.homEquiv _ _).symm x') (fun a => by rw [← adj.homEquiv_naturality_right_symm, hx']),
      Equiv.apply_symm_apply]

end GlobalTheory.Poinc.Sep.PowModel

open GlobalTheory.Poinc.Sep.PowModel in

theorem GlobalTheory.Poinc.Sep.unif_pow_isPow_model : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → ∀ (D₀ : DegData V₁ (maximalIdeal V₁)) (G₀ : Over (Sp V₁)) [GrpObj G₀] [IsCommMonObj G₀] (A₀ : PolAV (Sp (FractionRing V₁))) (U₀ : Unif (maximalIdeal V₁) D₀ A₀ G₀) (y : Sp (FractionRing V₁) ⟶ F.X) (α : A₀.A.left ⟶ F.univ.A.left), IsSemiAbelian G₀ → IsGrpPullback A₀.A F.univ.A y α → ∀ (P : PolAV (Sp (FractionRing V₁))) (c : SiegPre g n ζ (y ≫ F.s)) (φc : c.A.left ⟶ F.univ.A.left), IsGrpPullback c.A F.univ.A y φc → ∀ pr : Fin 8 → (P.A ⟶ c.A), (∀ a, IsMonHom (pr a)) → (∀ (T' : Over (Sp (FractionRing V₁))) (y' : Fin 8 → (T' ⟶ c.A)), ∃! x : T' ⟶ P.A, ∀ a, x ≫ pr a = y' a) → ∀ (G : Over (Sp V₁)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData V₁ (maximalIdeal V₁)) (U : Unif (maximalIdeal V₁) D P G), ∃ q : Fin 8 → (G ⟶ G₀), (∀ u, IsMonHom (q u)) ∧ (∀ (T' : Over (Sp V₁)) (y' : Fin 8 → (T' ⟶ G₀)), ∃! x : T' ⟶ G, ∀ u, x ≫ q u = y' u) ∧ ∀ u, ((Over.pullback (jK V₁)).map (q u) ≫ U₀.gen.hom).left ≫ α = (U.gen.hom ≫ pr u).left ≫ φc := by
  intro g n o _ ζ F V₁ _ _ _ hCN D₀ G₀ _ _ A₀ U₀ y α hsa hα P c φc hφc pr hpr hP G _ _ hG D U
  haveI : IsNoetherianRing V₁ := hCN.1
  haveI : IsIntegrallyClosed V₁ := hCN.2.1
  obtain ⟨κ, hκ, hκα⟩ := grpPullback_iso hφc hα
  haveI := U.gen_hom
  haveI := U₀.gen_hom
  have hf : ∀ u, IsMonHom (U.gen.hom ≫ pr u ≫ κ.hom ≫ U₀.gen.inv) := fun u => by
    haveI := hpr u
    infer_instance
  have hext : ∀ u, ∃ F : G ⟶ G₀, IsMonHom F ∧
      (Over.pullback (jK V₁)).map F = U.gen.hom ≫ pr u ≫ κ.hom ≫ U₀.gen.inv := fun u => by
    haveI := hf u
    exact (GlobalTheory.Published.SemiAbelianHomExtension.fractionField GlobalTheory.semiAbelianHomExtension_holds V₁
      (FractionRing V₁) G G₀ hG hsa (U.gen.hom ≫ pr u ≫ κ.hom ≫ U₀.gen.inv)).exists
  choose q hq hq' using hext
  have hcomp : ∀ u, ((Over.pullback (jK V₁)).map (q u) ≫ U₀.gen.hom).left ≫ α =
      (U.gen.hom ≫ pr u).left ≫ φc := by
    intro u
    rw [hq' u]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, Over.comp_left]
    rw [hκα]
  have hsa8 : IsSemiAbelian (powObj G₀ 8) :=
    GlobalTheory.PowGrp.isSemiAbelian_pow _ (powObj G₀ 8) G₀ 8 (powIsPowGrp G₀ 8) hsa
  have hPi := prod_of_isLimit (powIsLimit G₀ 8)
  obtain ⟨Q, hQ, -⟩ := hPi G q
  have hmul : ∀ (T : Over (Sp V₁)) (x y : T ⟶ G), (x * y) ≫ Q = (x ≫ Q) * (y ≫ Q) := fun T x y =>
    (hPi T fun u => (x * y) ≫ q u).unique (fun u => by rw [Category.assoc, hQ u]) (fun u => by
      haveI := hq u
      rw [MonObj.mul_comp, Category.assoc, Category.assoc, hQ u, MonObj.mul_comp])
  haveI hQm : IsMonHom Q := by
    constructor
    · have h := hmul _ (1 : 𝟙_ (Over (Sp V₁)) ⟶ G) 1
      rw [_root_.mul_one] at h
      have h' : (1 : 𝟙_ (Over (Sp V₁)) ⟶ G) ≫ Q = 1 := mul_eq_left.1 h.symm
      simpa [Hom.one_def] using h'
    · have h := hmul (G ⊗ G) (fst _ _) (snd _ _)
      rw [Hom.mul_def, Hom.mul_def, lift_fst_snd, Category.id_comp] at h
      rw [h]; congr 1
  have hGK := prod_postcomp (κ ≪≫ U₀.gen.symm) (prod_precomp U.gen hP)
  have hPiK := prod_pullback (jK V₁) hPi
  haveI : IsIso ((Over.pullback (jK V₁)).map Q) :=
    isIso_of_prod hGK hPiK _ (fun u => by
      rw [← Functor.map_comp, hQ u, hq' u]
      simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc])
  let e := asIso ((Over.pullback (jK V₁)).map Q)
  obtain ⟨Q', hQ'm, hQ'⟩ := (GlobalTheory.Published.SemiAbelianHomExtension.fractionField GlobalTheory.semiAbelianHomExtension_holds V₁
      (FractionRing V₁) (powObj G₀ 8) G hsa8 hG e.inv).exists
  have e1 : Q ≫ Q' = 𝟙 G := (GlobalTheory.Published.SemiAbelianHomExtension.fractionField
      GlobalTheory.semiAbelianHomExtension_holds V₁ (FractionRing V₁) G G hG hG (𝟙 _)).unique ⟨inferInstance, by rw [Functor.map_comp, hQ']; exact e.hom_inv_id⟩
    ⟨inferInstance, (Over.pullback _).map_id G⟩
  have e2 : Q' ≫ Q = 𝟙 _ := (GlobalTheory.Published.SemiAbelianHomExtension.fractionField
      GlobalTheory.semiAbelianHomExtension_holds V₁ (FractionRing V₁) (powObj G₀ 8) (powObj G₀ 8) hsa8 hsa8 (𝟙 _)).unique ⟨inferInstance, by rw [Functor.map_comp, hQ']; exact e.inv_hom_id⟩
    ⟨inferInstance, (Over.pullback _).map_id _⟩
  let E : G ≅ powObj G₀ 8 := ⟨Q, Q', e1, e2⟩
  refine ⟨q, hq, fun T' y' => ?_, hcomp⟩
  obtain ⟨x, hx, hu⟩ := prod_precomp E hPi T' y'
  exact ⟨x, fun u => by rw [← hQ u]; exact hx u, fun x' hx' => hu x' fun u => by
    change x' ≫ Q ≫ powPr G₀ u = y' u
    rw [hQ u]; exact hx' u⟩
