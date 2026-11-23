import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosVec
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.TensBalLat

open GlobalTheory.TensBal

section Calc

variable {M : Type} [CommGroup M] {α : Type}

def logHom (f : α → M) : (α →₀ ℤ) →+ Additive M :=
  Finsupp.liftAddHom fun v => zmultiplesHom (Additive M) (Additive.ofMul (f v)⁻¹)

theorem logHom_single (f : α → M) (v : α) : logHom f (Finsupp.single v 1) = Additive.ofMul (f v)⁻¹ := by
  simp [logHom]

theorem prod_eq_logHom (f : α → M) (c : α →₀ ℤ) :
    ∏ v ∈ c.support, f v ^ (-(c v)) = Additive.toMul (logHom f c) := by
  simp [logHom, Finsupp.liftAddHom_apply, Finsupp.sum, toMul_sum, toMul_zsmul, inv_zpow']

end Calc

variable {R : Type} [CommRing R] [IsDomain R] {D D' : DegPre R} {r : ℕ} {W : Matrix (Fin r) (Fin r) ℤ}

theorem vecLat_add (T : Tens D D' W) (u v : Vec r) (y y' : D'.X) :
    vecLat T (u + v) y y' = vecLat T u y y' + vecLat T v y y' := by
  simp only [vecLat, Pi.add_apply, add_smul, Finset.sum_add_distrib]; abel

theorem vecLat_zero (T : Tens D D' W) (y y' : D'.X) : vecLat T 0 y y' = 0 := by
  simp [vecLat]

theorem vecLat_rosVec (T : Tens D D' W) (A A' : Matrix (Fin r) (Fin r) ℤ) (y y' : D'.X) (a : Fin 6) (i : Fin r) :
    vecLat T (rosVec A A' a i) y y' = T.xe (rosLat T A A' y y' a) i := by
  fin_cases a <;>
    simp [vecLat, rosVec, rosLat, axv, azv, xv, zv, GlobalTheory.TensAct.xe_latAct, map_add, Pi.single_apply,
      Finset.sum_add_distrib, add_smul, ite_smul]

theorem logHom_lam (T : Tens D D' W) (hB : D.TauBimult) {z : (TK R).left} {J} (hJ : Good D.P.L z J)
    (y y' : D'.X) (u v : Vec r) :
    logHom (fun w => val (D.psi (vecLat T w y y')) (𝟙 _) z J) (lam u v) =
      Additive.ofMul (val (D.tau (vecLat T u y y') (vecLat T v y y')) (𝟙 _) z J)⁻¹ := by
  have hk : val (D.psi 0) (𝟙 _) z J = (val D.rigK (𝟙 _) z J)⁻¹ := by
    have e := (GlobalTheory.TauBalBox.tau_val D hJ 0 0 (𝟙 _)).symm.trans (GlobalTheory.TauBalElem.tau_zero_left hB hJ 0)
    rw [add_zero, mul_inv_cancel, _root_.one_mul] at e
    exact inv_mul_eq_one.mp e
  have h0 : vecLat T (0 : Vec r) y y' = 0 := vecLat_zero T y y'
  simp only [lam, map_add, map_sub, logHom_single, vecLat_add]
  rw [h0, vecLat_add]
  rw [GlobalTheory.TauBalBox.tau_val D hJ, hk]
  simp only [ofMul_mul, ofMul_inv, inv_inv]
  abel

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] (D D' : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ)
    (T : Tens D D' W), D.TauBimult → ∀ (A A' : Matrix (Fin r) (Fin r) ℤ) (z : (TK R).left)
    (J : ((TK R).left ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L z J → ∀ y y' : D'.X,
    ∏ v ∈ (GlobalTheory.TensBal.sig W A A').support,
        val (D.psi (GlobalTheory.TensBal.vecLat T v y y')) (𝟙 _) z J ^ (-(GlobalTheory.TensBal.sig W A A' v)) =
      ∏ a, GlobalTheory.TensBal.qv T z J (GlobalTheory.TensBal.rosLat T A A' y y' a) ^ (-(rosatiε a)) := by
  intro R _ _ D D' r W T hB A A' z J hJ y y'
  rw [prod_eq_logHom (fun w => val (D.psi (vecLat T w y y')) (𝟙 _) z J)]
  apply Additive.ofMul.injective
  rw [ofMul_toMul]
  simp only [sig, map_sum, map_zsmul, logHom_lam T hB hJ, vecLat_rosVec, qv, ofMul_prod, ofMul_zpow,
    Finset.smul_sum, ofMul_inv, smul_neg, smul_smul]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← neg_smul, neg_mul, vecLat_rosVec, vecLat_rosVec]

end GlobalTheory.TensBalLat
