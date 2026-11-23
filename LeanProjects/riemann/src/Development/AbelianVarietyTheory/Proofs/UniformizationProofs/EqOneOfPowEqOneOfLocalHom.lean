import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CubWeilOneLeft
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CubNRatioTwist
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

noncomputable section
namespace GlobalTheory.UU

theorem eq_one_of_pow_eq_one_of_localHom {W Ω : Type} [CommRing W] [IsLocalRing W] [Field Ω] (f : W →+* Ω)
    [IsLocalHom f] {N : ℕ} (hN : IsUnit (N : W)) {ζ : W} (h : ζ ^ N = 1) (hf : f ζ = 1) : ζ = 1 := by
  have hu : IsUnit (∑ i ∈ Finset.range N, ζ ^ i) := by
    refine isUnit_of_map_unit f _ ?_
    have := hN.map f
    simpa [map_sum, hf] using this
  have := geom_sum_mul ζ N
  rw [h, sub_self] at this
  exact sub_eq_zero.1 ((hu.mul_right_eq_zero).1 this)

theorem unit_eq_one_of_localHom {W Ω : Type} [CommRing W] [IsLocalRing W] [Field Ω] (f : W →+* Ω)
    [IsLocalHom f] {N : ℕ} (hN : IsUnit (N : W)) {ζ : Γ(Spec (CommRingCat.of W), ⊤)ˣ} (h : ζ ^ N = 1)
    (hf : Units.map (Spec.map (CommRingCat.ofHom f)).appTop.hom.toMonoidHom ζ = 1) : ζ = 1 := by
  have nat := congrArg (fun q => q.hom ζ.val) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom f))
  have hf' : (Spec.map (CommRingCat.ofHom f)).appTop.hom ζ.val = 1 := congrArg Units.val hf
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, hf', map_one, CommRingCat.hom_ofHom] at nat
  have h1 := eq_one_of_pow_eq_one_of_localHom f hN
    (ζ := (Scheme.ΓSpecIso (CommRingCat.of W)).hom.hom ζ.val)
    (by rw [← map_pow, ← Units.val_pow_eq_pow_val, h, Units.val_one, map_one]) nat.symm
  apply Units.ext
  apply (Scheme.ΓSpecIso (CommRingCat.of W)).commRingCatIsoToRingEquiv.injective
  rw [Units.val_one, map_one]
  exact h1

theorem IsCPMap.cubWeil_iff {S S' : Scheme.{0}} {f : S' ⟶ S} {G : Over S} [GrpObj G] [IsCommMonObj G] {G' : Over S'}
    [GrpObj G'] [IsCommMonObj G'] {P : CP G} {P' : CP G'} {F : G'.left ⟶ G.left} {hw} {w}
    (h : IsCPMap P' P f F hw w) {N : ℕ} {T : Over S'} {x y : T ⟶ G'} (hx : x ^ N = 1) (hy : y ^ N = 1)
    (ζ : Γ(T.left, ⊤)ˣ) : CubWeil P'.c N x y ζ ↔ CubWeil P.c N (toBase hw x) (toBase hw y) ζ := by
  refine ⟨cubWeil_map _ _ _ _ _ _ _ _ _ _ h N T x y ζ, fun h' => ?_⟩
  obtain ⟨ξ, hξ, -⟩ := existsUnique_cubWeil P'.c hx hy
  have := (cubWeil_map _ _ _ _ _ _ _ _ _ _ h N T x y ξ hξ).unique h'
  exact this ▸ hξ

theorem TQ.Desc.cubWeil_one_iff {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {X : Type} [AddCommGroup X]
    {Q : TQ G X} {P : CP G} (D : Q.Desc P) {N : ℕ} {T : Over S} {x y : T ⟶ G} (hx : x ^ N = 1) (hy : y ^ N = 1) :
    CubWeil P.c N x y 1 ↔ CubWeil D.M.c N (x ≫ Q.q) (y ≫ Q.q) 1 := by
  rw [D.map.cubWeil_iff hx hy]
  let ρ : T ⟶ Over.mk (T.hom ≫ 𝟙 S) := Over.homMk (𝟙 T.left) (by simp)
  let ρ' : Over.mk (T.hom ≫ 𝟙 S) ⟶ T := Over.homMk (𝟙 T.left) (by simp)
  have hw : Q.q.left ≫ Q.B.hom = G.hom ≫ 𝟙 S := by simp
  have e : ∀ a : T ⟶ G, ρ ≫ toBase hw a = a ≫ Q.q := fun a =>
    Over.OverMorphism.ext (Category.id_comp (a.left ≫ Q.q.left))
  have e' : ∀ a : T ⟶ G, ρ' ≫ (a ≫ Q.q) = toBase hw a := fun a =>
    Over.OverMorphism.ext (Category.id_comp (a.left ≫ Q.q.left))
  constructor
  · intro h
    have := h.comp ρ
    rwa [e, e, map_one] at this
  · intro h
    have := h.comp ρ'
    rwa [e', e', map_one] at this

theorem cubWeil_one_iff_closedFibre : AllSet fun {V} _ _ _ {A} {G} _ _ s => ∀ (t : Tower s) (W Ω : Type) [CommRing W] [IsLocalRing W] [Algebra V W] [Field Ω] (f' : W →+* Ω), IsLocalHom f' → ∀ (p : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of (V ⧸ (IsLocalRing.maximalIdeal V) ^ (0 + 1)))) (N : ℕ), IsUnit (N : V) → ∀ (y y' : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W))) ⟶ G) (x x' : Over.mk p ⟶ thickObj V (IsLocalRing.maximalIdeal V) 0 G), y ^ N = 1 → y' ^ N = 1 → x.left ≫ (fstG _ 0 G).left = (Spec.map (CommRingCat.ofHom f')) ≫ y.left → x'.left ≫ (fstG _ 0 G).left = (Spec.map (CommRingCat.ofHom f')) ≫ y'.left → (CubWeil s.P.c N y y' 1 ↔ CubWeil (t.l 0).D.M.c N (x ≫ (t.l 0).Q.q) (x' ≫ (t.l 0).Q.q) 1) := by
  intro V _ _ _ A G _ _ s t W Ω _ _ _ _ f' hf' p N hN y y' x x' hy hy' hx hx'
  let I := IsLocalRing.maximalIdeal V
  have hw : pullback.fst G.hom (thick V I 0) ≫ G.hom = (thickObj V I 0 G).hom ≫ thick V I 0 := pullback.condition
  obtain ⟨w, hl⟩ := (t.l 0).lev
  have hρ : Spec.map (CommRingCat.ofHom f') ≫ Spec.map (CommRingCat.ofHom (algebraMap V W)) =
      (Over.mk p).hom ≫ thick V I 0 := by
    have a := Over.w (toBase hw x)
    have b := Over.w y
    exact (congrArg (Spec.map (CommRingCat.ofHom f') ≫ ·) b).symm.trans
      ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ G.hom) hx).symm.trans a))
  let ρ : Over.mk ((Over.mk p).hom ≫ thick V I 0) ⟶ Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W))) :=
    Over.homMk (Spec.map (CommRingCat.ofHom f')) hρ
  have e : ρ ≫ y = toBase hw x := Over.OverMorphism.ext hx.symm
  have e' : ρ ≫ y' = toBase hw x' := Over.OverMorphism.ext hx'.symm
  have inj : ∀ a b : Over.mk p ⟶ thickObj V I 0 G, toBase hw a = toBase hw b → a = b := fun a b h =>
    Over.OverMorphism.ext (pullback.hom_ext (congrArg (fun q => q.left) h) ((Over.w a).trans (Over.w b).symm))
  have tor : ∀ (a : Over.mk p ⟶ thickObj V I 0 G) (b : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W))) ⟶ G),
      b ^ N = 1 → ρ ≫ b = toBase hw a → a ^ N = 1 := fun a b hb h => by
    refine inj _ _ ((map_pow (toBaseHom hl.mul _) a N).trans (Eq.trans ?_ (map_one (toBaseHom hl.mul _)).symm))
    exact (congrArg (· ^ N) h.symm).trans (by rw [← MonObj.comp_pow, hb, MonObj.comp_one])
  have hxN := tor x y hy e
  have hxN' := tor x' y' hy' e'
  refine Iff.trans ?_ ((t.l 0).D.cubWeil_one_iff hxN hxN')
  refine Iff.trans ?_ (hl.cubWeil_iff hxN hxN' 1).symm
  constructor
  · intro h
    have := h.comp ρ
    rw [e, e', map_one] at this
    exact this
  · intro h
    obtain ⟨ζ, hζ, -⟩ := existsUnique_cubWeil s.P.c hy hy'
    have c := hζ.comp ρ
    rw [e, e'] at c
    have hNW : IsUnit (N : W) := by simpa using hN.map (algebraMap V W)
    have : ζ = 1 := unit_eq_one_of_localHom f' hNW hζ.pow_eq_one (c.unique h)
    exact this ▸ hζ

end GlobalTheory.UU
end
