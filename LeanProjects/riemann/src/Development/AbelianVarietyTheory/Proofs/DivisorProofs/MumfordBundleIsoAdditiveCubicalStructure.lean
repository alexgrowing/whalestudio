import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExtId
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleIsoEqOneAlongAxesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleIsoNormalisedRespectsLaws
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj

namespace GlobalTheory.TInj

theorem lamVal_add_cub : ∀ {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (T : TautBase o W) {I : Type} [Fintype I] (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ)) (n : ℕ) (V : Type) [CommRing V] [IsDomain V] (D : DegPre V) (ω : W →+* V) (s : I → V) (e : D.X ≃+ (Fin T.r → ℤ)) (β : D.P.A.left ⟶ T.B.left) (ββ : (G2 D.P.A).left ⟶ (G2 T.B).left) (w : LB.Iso (abelian₂ D.P.A D.P.L) ((abelian₂ T.B T.M.L).pull ββ)), D.TauBimult → From T ω s ε n D e β ββ w → ∀ (Z : Over (Sp V)) (x x' y : Z ⟶ D.P.A) (x₀ x₀' y₀ : Over.mk (Z.hom ≫ spMap ω) ⟶ T.B), x.left ≫ β = x₀.left → x'.left ≫ β = x₀'.left → y.left ≫ β = y₀.left → ∀ (z : Z.left) J J', Good T.M.L z J → Good D.P.L z J' → lamVal w (lift (x * x') y).left z J J' * cubV D.cub z J' x x' y = lamVal w (lift x y).left z J J' * lamVal w (lift x' y).left z J J' * @id (Z.left.presheaf.stalk z)ˣ (cubV T.cub (T := Over.mk (Z.hom ≫ spMap ω)) z J x₀ x₀' y₀) ∧ lamVal w (lift y (x * x')).left z J J' * cubV D.cub z J' y x x' = lamVal w (lift y x).left z J J' * lamVal w (lift y x').left z J J' * @id (Z.left.presheaf.stalk z)ˣ (cubV T.cub (T := Over.mk (Z.hom ≫ spMap ω)) z J y₀ x₀ x₀') := by
  intro o W _ _ _ T I _ ε n V _ _ D ω s e β ββ w hτ hF Z x x' y x₀ x₀' y₀ hx hx' hy z J J' hJ hJ'
  have hn : ∀ (T' : Over (Sp V)) (z : T'.left) (J : (T'.left ⟶ T.B.left) → T.M.L.ι)
      (J' : (T'.left ⟶ D.P.A.left) → D.P.L.ι), Good T.M.L z J → Good D.P.L z J' →
      lamVal w (lift (1 : T' ⟶ D.P.A) (1 : T' ⟶ D.P.A)).left z J J' = 1 := fun T' z J J' hJ hJ' =>
    (GlobalTheory.T.mumford_bundle_iso_eq_one_along_axes T ε n V D ω s e β ββ w hτ hF T' 1 z J J' hJ hJ').1
  have L := GlobalTheory.LamRigid.lam_iso_laws (Sp W) (Sp V) T.B D.P.A T.M _ T.cub D.cub (spMap ω) β ββ w hF.1 D.P.isAb
    hF.2.1 hF.2.2.1 hn
  have C₁ : IsCub (cubV D.cub z J') := isCub_cubV D.cub hJ'
  have C₀ : IsCub (cubV T.cub (T := Over.mk (Z.hom ≫ spMap ω)) z J) := isCub_cubV T.cub hJ
  have A₁ := (L Z x x' y z J J' hJ hJ').2 x₀ x₀' y₀ hx.symm hx'.symm hy.symm
  refine ⟨?_, ?_⟩
  · rw [A₁]; simp only [id]; ac_rfl
  · rw [(L Z y y (x * x') z J J' hJ hJ').1, (L Z y y x z J J' hJ hJ').1, (L Z y y x' z J J' hJ hJ').1,
      C₁.s01 y x x', C₁.s12 x y x', C₀.s01 y₀ x₀ x₀', C₀.s12 x₀ y₀ x₀', A₁]
    simp only [id]; ac_rfl

end GlobalTheory.TInj
