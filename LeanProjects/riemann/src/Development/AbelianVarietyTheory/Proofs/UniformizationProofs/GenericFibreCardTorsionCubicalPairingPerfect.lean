import Mathlib
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CubNRatioTwist
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsProjectiveRep
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
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

namespace GlobalTheory.UU

theorem card_and_nondeg_of_pullback (hL : Laws) {S S' : Scheme.{0}} [IsLocallyNoetherian S'] (f : S' ⟶ S)
    (A : PolAV S') {G : Over S} [GrpObj G] [IsCommMonObj G] (P : CP G) (φ : A.A.left ⟶ G.left)
    (hφ : IsPullback φ A.A.hom G.hom f)
    (mul : ∀ (T : Over S') (x y : T ⟶ A.A), toBase hφ.w (x * y) = toBase hφ.w x * toBase hφ.w y)
    (hw : LBIso A.L (P.L.L.pull φ)) {F : Type} [Field F] [IsAlgClosed F] (q : Spec (CommRingCat.of F) ⟶ S')
    {N : ℕ} (h1 : 1 ≤ N) (hN : (N : F) ≠ 0) :
    Nat.card {x : Over.mk (q ≫ f) ⟶ G // x ^ N = 1} = N ^ (2 * A.g) ∧
      ∀ x : Over.mk (q ≫ f) ⟶ G, x ^ N = 1 →
        (∀ y : Over.mk (q ≫ f) ⟶ G, y ^ N = 1 → CubWeil P.c N x y 1) → x = 1 := by
  haveI := A.isAb.comm
  obtain ⟨w, hg⟩ := hw
  obtain ⟨rig, hr, c, s, h₁, h₂, h₃, hm⟩ := exists_isCPMap P mul A.L A.isLB w hg
  let β : (Over.mk q ⟶ A.A) →* (Over.mk (q ≫ f) ⟶ G) := toBaseHom mul (Over.mk q)
  have hβ : ∀ y, (β y).left = y.left ≫ φ := fun y => rfl
  have inj : Function.Injective β := fun a b e => Over.OverMorphism.ext (hφ.hom_ext
    ((hβ a).symm.trans ((congrArg CommaMorphism.left e).trans (hβ b))) ((Over.w a).trans (Over.w b).symm))
  have surj : Function.Surjective β := fun x =>
    ⟨Over.homMk (hφ.lift x.left q (Over.w x)) (hφ.lift_snd _ _ _),
      Over.OverMorphism.ext ((hβ _).trans (hφ.lift_fst _ _ _))⟩
  have hp : ∀ y, y ^ N = 1 ↔ β y ^ N = 1 := fun y => by
    rw [← map_pow, ← map_one β, inj.eq_iff]
  refine ⟨?_, fun x hx h => ?_⟩
  · rw [← (hL.mulN S' A N h1).2.2.2.2 F q hN]
    exact (Nat.card_congr ((Equiv.ofBijective β ⟨inj, surj⟩).subtypeEquiv hp)).symm
  · obtain ⟨x, rfl⟩ := surj x
    have hx' := (hp x).2 hx
    rw [GlobalTheory.ThetaRep.eq_one_of_weilIs hL A q hN x hx' fun y hy => ?_, map_one]
    obtain ⟨ζ, hζ, -⟩ := existsUnique_cubWeil c hx' hy
    have e := (cubWeil_map _ _ f G A.A P ⟨_, c, s, h₁, h₂, h₃⟩ φ _ w hm N (Over.mk q) x y ζ hζ).unique (h _ ((hp y).1 hy))
    exact (cubWeil_iff_weilIs hL.globalFns A.isAb hx' hy 1).1 (e ▸ hζ)

theorem generic_card_and_nondeg : Laws → AllSet fun {V} _ _ _ {A} {G} _ _ s => ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F] (N : ℕ), 1 ≤ N → Nat.card {x : TF (R := V) F ⟶ G // x ^ N = 1} = N ^ (2 * A.g) ∧ ∀ x : TF (R := V) F ⟶ G, x ^ N = 1 → (∀ y : TF (R := V) F ⟶ G, y ^ N = 1 → CubWeil s.P.c N x y 1) → x = 1 := by
  intro hL V _ _ _ A G _ _ s F _ _ _ N h1
  haveI := s.gen_hom
  haveI : CharZero V := s.cdvr.2.2
  haveI : CharZero (FractionRing V) := charZero_of_injective_ringHom (IsFractionRing.injective V (FractionRing V))
  haveI : CharZero F := charZero_of_injective_ringHom (algebraMap (FractionRing V) F).injective
  let φ : A.A.left ⟶ G.left := s.gen.inv.left ≫ pullback.fst G.hom (jK V)
  haveI : IsIso s.gen.inv.left := inferInstanceAs (IsIso ((Over.forget _).map s.gen.inv))
  have hφ : IsPullback φ A.A.hom G.hom (jK V) := by
    have a : IsPullback s.gen.inv.left A.A.hom (pullback.snd G.hom (jK V)) (𝟙 _) :=
      IsPullback.of_horiz_isIso ⟨(Over.w s.gen.inv).trans (Category.comp_id _).symm⟩
    simpa using a.paste_horiz (IsPullback.of_hasPullback G.hom (jK V))
  refine card_and_nondeg_of_pullback hL (jK V) A s.P φ hφ (fun T x y => ?_) ?_ (jFK F) h1
    (Nat.cast_ne_zero.2 (by omega))
  · have e : ∀ a : T ⟶ A.A, toBase hφ.w a = toBase (A := G) (A' := (Over.pullback (jK V)).obj G)
        (g := pullback.fst G.hom (jK V)) pullback.condition (a ≫ s.gen.inv) := fun a =>
      Over.OverMorphism.ext (Category.assoc _ _ _).symm
    rw [e, e, e, MonObj.mul_comp, toBase_mul_pullback]
  · exact LBIso.chartPull (chartPullSec A.L s.gen.hom.left s.gen.inv.left
      (congrArg CommaMorphism.left s.gen.inv_hom_id)) (chartPullSame s.P.L.L _ _ _ _ fun _ => rfl) ⟨s.wA, s.wA_gen⟩

end GlobalTheory.UU
