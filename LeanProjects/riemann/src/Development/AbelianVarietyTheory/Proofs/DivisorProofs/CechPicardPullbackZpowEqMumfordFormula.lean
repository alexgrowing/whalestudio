import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiMapFst
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHeckeQuotientTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulPullOfRigOfSym
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsAffineOfQuasiAffine

set_option autoImplicit false

noncomputable section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AmpleGen
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PowPull

theorem tri_succ (n : ℤ) : tri (n + 1) = tri n + (n + 1) := by
  unfold tri
  have : (n + 1) * (n + 1) + (n + 1) = n * n + n + (n + 1) * 2 := by ring
  rw [this, Int.add_mul_ediv_right _ _ two_ne_zero]

theorem tri_neg (n : ℤ) : tri (-n) = tri n - n := by
  unfold tri
  have : n * n + n = -n * -n + -n + n * 2 := by ring
  rw [this, Int.add_mul_ediv_right _ _ two_ne_zero]
  ring

theorem eq_of_rec {M : Type*} [AddCommGroup M] (f : ℤ → M) (a l : M) (h0 : f 0 = 0)
    (hs : ∀ n, f (n + 1) = f n + a + n • l) (n : ℤ) : f n = n • a + tri (-n) • l := by
  have step : ∀ n : ℤ, tri (-(n + 1)) = tri (-n) + n := fun n => by
    rw [tri_neg, tri_neg, tri_succ]; ring
  induction n using Int.induction_on with
  | zero => simp [h0, tri]
  | succ n ih => rw [hs, ih, step]; module
  | pred n ih =>
    have h := hs (-(n : ℤ) - 1)
    have h' := step (-(n : ℤ) - 1)
    rw [sub_add_cancel] at h h'
    rw [ih, h'] at h
    rw [eq_sub_of_add_eq (eq_sub_of_add_eq h.symm)]
    module

open GlobalTheory.CechPic in

theorem pull_zpow : ∀ (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → ∀ (L : LB A.left) (hL : L.IsLB) (T : Over (Sp K)) (z : T ⟶ A) (n : ℤ), GlobalTheory.CechPic.pull (z ^ n).left (GlobalTheory.CechPic.cls L hL) = tri n • GlobalTheory.CechPic.pull z.left (GlobalTheory.CechPic.cls L hL) + tri (-n) • GlobalTheory.CechPic.pull (z⁻¹).left (GlobalTheory.CechPic.cls L hL) := by
  intro K _ A _ hA L hL T z n
  have := hA.comm
  have hΘ : ∃ t : LB.Gen (Theta A L), t.IsGen :=
    GlobalTheory.SymMulPull.hasGen_theta GlobalTheory.CubeTop.cubeTheorem hA hL
  have h1 : pull (1 : T ⟶ A).left (cls L hL) = 0 := by
    rw [Hom.one_def, Over.comp_left, pull_comp, GlobalTheory.AmpleStabFinite.pull_spec_local, map_zero]
  let φ : (T ⟶ A) →* Multiplicative (Pic T.left) :=
    MonoidHom.mk' (fun x => Multiplicative.ofAdd (lam (cls L hL) x z)) fun x y => by
      rw [lam_mul_left hL hΘ, ofAdd_add]
  have hz : ∀ m : ℤ, lam (cls L hL) (z ^ m) z = m • lam (cls L hL) z z := fun m =>
    congrArg Multiplicative.toAdd (map_zpow φ z m)
  have key := eq_of_rec (fun m => pull (z ^ m).left (cls L hL)) (pull z.left (cls L hL)) (lam (cls L hL) z z)
    (by rw [zpow_zero, h1]) (fun m => by
      rw [← hz, zpow_add_one, lam, h1]; abel)
  have k1 := key (-1)
  have t1 : tri (- -1) = 1 := by decide
  rw [zpow_neg_one, t1] at k1
  rw [key n, k1, tri_neg]
  module

end GlobalTheory.PowPull
