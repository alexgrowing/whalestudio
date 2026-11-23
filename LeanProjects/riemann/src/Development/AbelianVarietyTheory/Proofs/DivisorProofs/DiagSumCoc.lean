import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsCharZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigOfOmegaInjectiveOfEqZero
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CocycleTensorLiftApplyEqTwoPointValue

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

theorem Dat.diagSum_coc : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (p : ℕ) (G : PDivGroup p R) (t : G.TorsionTower A) (c : primDR A) (d : Dat t c) (N : ℕ), (p : R) ^ N = 0 → diagSum R (G.A N) (p ^ N) (d.coc N) = chi (p ^ N) d.g (G.A N) (t.y N) := by
  intro R _ A _ p G t c d N hN
  let e : ℕ → (G.A N →ₐ[R] G.A N) := fun j ↦ (toConv (AlgHom.id R (G.A N)) ^ j).ofConv
  let K : ℕ → G.A N := fun j ↦ fv d.f (G.A N) (G.A N) (e j) (t.y N) + e j (d.h N)
  have hm : ∀ j, (mulBy R (G.A N) j : G.A N →ₐ[R] G.A N) = e j := fun j ↦ by
    have h := comp_mulBy_pts (AlgHom.id R (G.A N)) j
    rwa [AlgHom.id_comp] at h
  have hy : ∀ j, spOver (e j) ≫ t.y N = t.y N ^ j := fun j ↦ by
    rw [← hm]; exact t.mulBy_y N j
  have he1 : e 1 = AlgHom.id R (G.A N) := by simp only [e, pow_one, ofConv_toConv]
  have hes : ∀ i, (toConv (e i) * toConv (AlgHom.id R (G.A N))).ofConv = e (i + 1) := fun i ↦ by
    simp only [e, toConv_ofConv, pow_succ]
  have hterm : ∀ i, Algebra.TensorProduct.lift (mulBy R (G.A N) i : G.A N →ₐ[R] G.A N) (AlgHom.id R (G.A N))
      (fun _ _ ↦ Commute.all _ _) (d.coc N) = d.g (G.A N) (t.y N ^ i) (t.y N) - (K (i + 1) - K i - K 1) := by
    intro i
    rw [hm i, Dat.lift_coc R A p G t c d N (G.A N) (e i) (AlgHom.id R _), hy, spOver_id, Category.id_comp, hes]
    simp only [K, he1]
  have hq : e (p ^ N) = e 0 := t.inj N (G.A N) _ _ (by rw [hy, hy, t.y_pow, pow_zero])
  have hz : ((p ^ N : ℕ) : G.A N) = 0 := by
    rw [Nat.cast_pow, ← map_natCast (algebraMap R (G.A N)), ← map_pow, hN, map_zero]
  rw [diagSum, LinearMap.sum_apply]
  simp only [AlgHom.toLinearMap_apply, hterm]
  rw [chi, Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_range_sub (fun j ↦ K j), Finset.sum_const,
    Finset.card_range, nsmul_eq_mul, hz, zero_mul, sub_zero]
  have : K (p ^ N) = K 0 := by simp only [K, hq]
  rw [this, sub_self, sub_zero]

end GlobalTheory.PtExt
