import Mathlib
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CubNRatioTwist
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
import Development.AbelianVarietyTheory.Definitions.Uniformization.WCompat
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UU.ImagePairing

theorem eq_map_of_isCPMap {S S' : Scheme.{0}} {f : S' ⟶ S} {G : Over S} [GrpObj G] [IsCommMonObj G] {G' : Over S'}
    [GrpObj G'] [IsCommMonObj G'] {P : CP G} {P' : CP G'} {F : G'.left ⟶ G.left} {hw} {w}
    (h : IsCPMap P' P f F hw w) {N : ℕ} {T' : Over S'} {T : Over S} (r : T'.left ⟶ T.left)
    (hr : r ≫ T.hom = T'.hom ≫ f) {x' y' : T' ⟶ G'} {x y : T ⟶ G} (hx : x'.left ≫ F = r ≫ x.left)
    (hy : y'.left ≫ F = r ≫ y.left) {ζ' ζ} (h' : CubWeil P'.c N x' y' ζ') (h₀ : CubWeil P.c N x y ζ) :
    ζ' = Units.map r.appTop.hom.toMonoidHom ζ := by
  let ρ : Over.mk (T'.hom ≫ f) ⟶ T := Over.homMk r hr
  have a := cubWeil_map S S' f G G' P P' F hw w h N T' x' y' ζ' h'
  have ex : toBase hw x' = ρ ≫ x := Over.OverMorphism.ext hx
  have ey : toBase hw y' = ρ ≫ y := Over.OverMorphism.ext hy
  rw [ex, ey] at a
  exact a.unique (h₀.comp ρ)

theorem pow_eq_one_of_pullback {S S' : Scheme.{0}} (f : S' ⟶ S) {G : Over S} [GrpObj G] {N : ℕ} {T' : Over S'}
    {T : Over S} (r : T'.left ⟶ T.left) (hr : r ≫ T.hom = T'.hom ≫ f) {x' : T' ⟶ (Over.pullback f).obj G}
    {x : T ⟶ G} (hx : x'.left ≫ pullback.fst G.hom f = r ≫ x.left) (h : x ^ N = 1) : x' ^ N = 1 := by
  let ρ : Over.mk (T'.hom ≫ f) ⟶ T := Over.homMk r hr
  let β : (T' ⟶ (Over.pullback f).obj G) →* (Over.mk (T'.hom ≫ f) ⟶ G) :=
    MonoidHom.mk' (toBase (A := G) (A' := (Over.pullback f).obj G) (g := pullback.fst G.hom f) pullback.condition)
      (toBase_mul_pullback G f T')
  have ex : β x' = ρ ≫ x := Over.OverMorphism.ext hx
  have e : β (x' ^ N) = β 1 := by rw [map_pow, map_one, ex, ← MonObj.comp_pow, h, MonObj.comp_one]
  refine Over.OverMorphism.ext (pullback.hom_ext (congrArg (fun q => q.left) e) ?_)
  exact (Over.w (x' ^ N)).trans (Over.w (1 : T' ⟶ (Over.pullback f).obj G)).symm

theorem fn_eq_of_thick {R : Type} [CommRing R] (I : Ideal R) [IsHausdorff I R]
    (a b : Γ(Spec (CommRingCat.of R), ⊤))
    (h : ∀ e, (thick R I e).appTop.hom a = (thick R I e).appTop.hom b) : a = b := by
  apply (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).hom).1
  have key : ∀ (e : ℕ) (c : Γ(Spec (CommRingCat.of R), ⊤)),
      Ideal.Quotient.mk (I ^ (e + 1)) ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom c) =
        (Scheme.ΓSpecIso (CommRingCat.of (R ⧸ I ^ (e + 1)))).hom.hom ((thick R I e).appTop.hom c) := fun e c =>
    (congrArg (fun q => q.hom c)
      (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (e + 1)))))).symm
  have := IsHausdorff.StrictMono.funext' I (a := fun n => n + 1) (strictMono_id.add_const 1)
    (f := fun _ : Unit => (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom a)
    (g := fun _ : Unit => (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom b)
    (fun n _ => (key n a).trans ((congrArg _ (h n)).trans (key n b).symm))
  exact congrFun this ()

theorem exists_thick_hom {V W : Type} [CommRing V] [CommRing W] [Algebra V W] (I : Ideal V) (e : ℕ) :
    ∃ φ : Spec (CommRingCat.of (W ⧸ (I.map (algebraMap V W)) ^ (e + 1))) ⟶ Spec (CommRingCat.of (V ⧸ I ^ (e + 1))),
      thick W (I.map (algebraMap V W)) e ≫ Spec.map (CommRingCat.ofHom (algebraMap V W)) = φ ≫ thick V I e := by
  refine ⟨Spec.map (CommRingCat.ofHom (Ideal.quotientMap _ (algebraMap V W) ?_)), ?_⟩
  · rw [← Ideal.map_pow]; exact Ideal.le_comap_map
  · simp only [thick, ← Spec.map_comp, ← CommRingCat.ofHom_comp, Ideal.quotientMap_comp_mk]

theorem cubWeil_image : AllSet fun {V} _ _ _ {A} {G} _ _ s => ∀ (t : Tower s) (a : t.Alg) (W : Type) [CommRing W] [IsLocalRing W] [Algebra V W], IsAdicComplete ((IsLocalRing.maximalIdeal V).map (algebraMap V W)) W → IsLocalHom (algebraMap V W) → ∀ (N : ℕ) (x x' : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W))) ⟶ G) (b b' : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W))) ⟶ a.B) (ζ), (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ Spec (CommRingCat.of W)) (xe : Z ⟶ (thickObj V (IsLocalRing.maximalIdeal V) e G).left), xe ≫ (fstG _ e G).left = r ≫ (x).left → xe ≫ (t.l e).Q.q.left ≫ a.b e = r ≫ (b).left) → (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ Spec (CommRingCat.of W)) (xe : Z ⟶ (thickObj V (IsLocalRing.maximalIdeal V) e G).left), xe ≫ (fstG _ e G).left = r ≫ (x').left → xe ≫ (t.l e).Q.q.left ≫ a.b e = r ≫ (b').left) → b ^ N = 1 → b' ^ N = 1 → CubWeil s.P.c N x x' ζ → CubWeil a.M.c N b b' ζ := by
  intro V _ _ _ A G _ _ s t a W _ _ _ hW _ N x x' b b' ζ hx hx' hb hb' h
  obtain ⟨ξ, hξ, -⟩ := existsUnique_cubWeil a.M.c hb hb'
  suffices e : ζ = ξ from e ▸ hξ
  refine Units.ext (fn_eq_of_thick ((IsLocalRing.maximalIdeal V).map (algebraMap V W)) _ _ fun e => ?_)
  obtain ⟨φ, hφ⟩ := exists_thick_hom (W := W) (IsLocalRing.maximalIdeal V) e
  let r := thick W ((IsLocalRing.maximalIdeal V).map (algebraMap V W)) e
  have lifts : ∀ y : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W))) ⟶ G,
      ∃ ye : Over.mk φ ⟶ thickObj V (IsLocalRing.maximalIdeal V) e G,
        ye.left ≫ pullback.fst G.hom (thick V _ e) = r ≫ y.left := fun y =>
    ⟨Over.homMk (pullback.lift (r ≫ y.left) φ ((Category.assoc _ _ _).trans ((congrArg (r ≫ ·) (Over.w y)).trans hφ)))
      (pullback.lift_snd _ _ _), pullback.lift_fst _ _ _⟩
  obtain ⟨y, hy⟩ := lifts x
  obtain ⟨y', hy'⟩ := lifts x'
  obtain ⟨θ, hθ, -⟩ := existsUnique_cubWeil (t.l e).Pe.c
    (pow_eq_one_of_pullback (T' := Over.mk φ) (T := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W))))
      _ r hφ hy h.1)
    (pow_eq_one_of_pullback (T' := Over.mk φ) (T := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W))))
      _ r hφ hy' h.2.1)
  obtain ⟨w, hw⟩ := (t.l e).lev
  obtain ⟨hp, v, hv⟩ := a.b_pb e
  have e₁ := eq_map_of_isCPMap hw (T' := Over.mk φ)
    (T := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W)))) r hφ hy hy' hθ h
  obtain ⟨u, -, hu⟩ := hv.exists_comp (t.l e).D.map (by
    rw [Category.assoc, hp.1.w, ← Category.assoc, Over.w, Category.id_comp])
  have e₂ := eq_map_of_isCPMap hu (T' := Over.mk φ)
    (T := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W)))) r
    (hφ.trans (congrArg (φ ≫ ·) (Category.id_comp _).symm)) (hx e _ r y.left hy) (hx' e _ r y'.left hy') hθ hξ
  exact congrArg Units.val (e₁.symm.trans e₂)

end GlobalTheory.UU.ImagePairing
