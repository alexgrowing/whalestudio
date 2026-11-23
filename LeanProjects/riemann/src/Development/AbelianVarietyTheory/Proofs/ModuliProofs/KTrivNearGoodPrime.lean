import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.DenseOfDenseP
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.KTrivAwayOfKTrivFibre

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory.ZM.NearBuild

namespace GlobalTheory.ZM.NearBuild

private theorem isGrpPullback_pullback_fst {S S' : Scheme.{0}} (G : Over S) [GrpObj G] (f : S' ⟶ S) :
    IsGrpPullback ((Over.pullback f).obj G) G f (pullback.fst G.hom f) := by
  refine ⟨IsPullback.of_hasPullback G.hom f, ?_⟩
  intro T x y x₀ y₀ hx hy
  have h := GlobalTheory.UU.toBase_mul_pullback G f T x y
  have ex : x₀ = Out.toBase (A := G) (A' := (Over.pullback f).obj G) (g := pullback.fst G.hom f) pullback.condition x := by
    ext
    simp [hx, Out.toBase]
  have ey : y₀ = Out.toBase (A := G) (A' := (Over.pullback f).obj G) (g := pullback.fst G.hom f) pullback.condition y := by
    ext
    simp [hy, Out.toBase]
  rw [ex, ey, ← h]
  simp [Out.toBase]

theorem kTriv_near_good_prime : ∀ (o : Type) [CommRing o] (g N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ : ℕ) (R : Type) [CommRing R] [IsNoetherianRing R] (β : o →+* R) (v : Ix g (N' ^ 2) → R) (A : Over (Sp R)) [GrpObj A] (L : LB A.left) (act : J → (A ⟶ A)) (Q : Fin (2 * g) → (Out.baseOver (Sp R) ⟶ A)) (q₀ : Ideal R), q₀ ∈ objPrimes b Mat κ β v → PolFam b Mat κ β v A L act Q → ∃ f : R, f ∉ q₀ ∧ Out.KTriv ((Over.pullback (spMap (loc f))).obj A) (L.pull (pullback.fst A.hom (spMap (loc f)))) := by
  intro o _ g N' J b Mat κ R _ _ β v A _ L act Q q₀ hq hP
  obtain ⟨K, _, _, x, s, t, hker, hgood⟩ := mem_objPrimes.1 hq
  obtain ⟨hab, -, hLB, -, -, hamp, -, hfib⟩ := hP
  obtain ⟨ψ, hψ, hiso⟩ := hfib K x s t hgood
  obtain ⟨e, he, hcomp⟩ := grpPullback_iso (isGrpPullback_pullback_fst A (spMap x)) hψ.1
  haveI := he
  have hLB' : (L.pull (pullback.fst A.hom (spMap x))).IsLB := pull_isLB hLB _
  have hLt : (t.L.pull e.hom.left).IsLB := pull_isLB t.isLB _
  have hψL : (L.pull ψ).IsLB := pull_isLB hLB ψ
  have hcls : LBIso (L.pull (pullback.fst A.hom (spMap x))) (t.L.pull e.hom.left) := by
    rw [← GlobalTheory.CechPic.cls_eq_iff hLB' hLt, GlobalTheory.CechPic.cls_pull hLB _ hLB', GlobalTheory.CechPic.cls_pull t.isLB _ hLt,
      ← hcomp, GlobalTheory.CechPic.pull_comp, ← GlobalTheory.CechPic.cls_pull hLB ψ hψL,
      ← (GlobalTheory.CechPic.cls_eq_iff t.isLB hψL).2 hiso]
  have hfibK := (amplePt (Sp K) K (𝟙 _) t.A _ e.hom.left (isGrpPullback_of_iso e) t.L _ t.isLB hLB' hcls
    t.ample t.ktriv).2
  obtain ⟨f, hf, hk⟩ := kTriv_away_of_kTriv_fibre globalFns_holds R A L K x hab hLB hamp hfibK
  refine ⟨f, fun h => hf ?_, hk⟩
  rw [← hker, RingHom.mem_ker] at h
  exact h

end GlobalTheory.ZM.NearBuild
