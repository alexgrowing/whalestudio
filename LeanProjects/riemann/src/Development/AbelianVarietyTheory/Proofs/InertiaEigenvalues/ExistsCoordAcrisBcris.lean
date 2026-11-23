import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.CoordTW

variable {l : ℕ} [Fact l.Prime] {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [Field K] [Algebra ℚ_[l] K]
  [Algebra O K] [TopologicalSpace K] {G : Type} [Group G] [TopologicalSpace G]
  (T : LocLat G ℚ_[l] K O) (φ : ↥T.L.T →+ ℤ_[l])
  (hφ : ∀ (z : ℤ_[l]) (t : ↥T.L.T), φ (algebraMap ℤ_[l] O z • t) = z * φ t)
  (R : Type) [CommRing R] [Algebra ℤ_[l] R]

def inner (t : ↥T.L.T) : O ⊗[ℤ_[l]] R →+ R :=
  TensorProduct.liftAddHom
    { toFun := fun o => AddMonoidHom.mulLeft (algebraMap ℤ_[l] R (φ (o • t)))
      map_zero' := by ext r; simp
      map_add' := by intro a b; ext r; simp [add_smul, add_mul] }
    (fun z o r => by
      simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk, AddMonoidHom.coe_mulLeft]
      rw [Algebra.smul_def z o, mul_smul, hφ, Algebra.smul_def z r, map_mul]; ring)

theorem inner_tmul (t : ↥T.L.T) (o : O) (r : R) :
    inner T φ hφ R t (o ⊗ₜ[ℤ_[l]] r) = algebraMap ℤ_[l] R (φ (o • t)) * r := by
  simp [inner]

theorem inner_add (t t' : ↥T.L.T) (w : O ⊗[ℤ_[l]] R) :
    inner T φ hφ R (t + t') w = inner T φ hφ R t w + inner T φ hφ R t' w := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul o r => simp only [inner_tmul, smul_add, map_add, add_mul]
  | add x y hx hy => simp only [map_add, hx, hy]; ring

theorem inner_zero (w : O ⊗[ℤ_[l]] R) : inner T φ hφ R 0 w = 0 := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul o r => simp [inner_tmul]
  | add x y hx hy => simp only [map_add, hx, hy, add_zero]

theorem inner_smul (o : O) (t : ↥T.L.T) (w : O ⊗[ℤ_[l]] R) :
    inner T φ hφ R t (o • w) = inner T φ hφ R (o • t) w := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul o' r =>
    rw [TensorProduct.smul_tmul', inner_tmul, inner_tmul, smul_eq_mul, mul_smul, smul_comm o o' t]
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]

def coord : TW (O ⊗[ℤ_[l]] R) T →+ R :=
  TensorProduct.liftAddHom
    { toFun := fun w =>
        { toFun := fun t => inner T φ hφ R t w
          map_zero' := inner_zero T φ hφ R w
          map_add' := fun t t' => inner_add T φ hφ R t t' w }
      map_zero' := by ext t; simp
      map_add' := by intro a b; ext t; simp }
    (fun o w t => by simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk]; exact inner_smul T φ hφ R o t w)

theorem coord_tmul (w : O ⊗[ℤ_[l]] R) (t : ↥T.L.T) :
    coord T φ hφ R (w ⊗ₜ[O] t) = inner T φ hφ R t w := by
  simp [coord]

theorem coord_mul (a : R) (w : TW (O ⊗[ℤ_[l]] R) T) :
    coord T φ hφ R (((1 : O) ⊗ₜ[ℤ_[l]] a : O ⊗[ℤ_[l]] R) • w) = a * coord T φ hφ R w := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul x t =>
    rw [TensorProduct.smul_tmul', coord_tmul, coord_tmul, smul_eq_mul]
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul o r =>
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, inner_tmul, inner_tmul]; ring
    | add x y hx hy => simp only [mul_add, map_add, hx, hy]
  | add x y hx hy => simp only [smul_add, map_add, hx, hy, mul_add]

theorem coord_one_tmul (t : ↥T.L.T) :
    coord T φ hφ R ((1 : O ⊗[ℤ_[l]] R) ⊗ₜ[O] t) = algebraMap ℤ_[l] R (φ t) := by
  rw [coord_tmul, Algebra.TensorProduct.one_def, inner_tmul, one_smul, mul_one]

theorem coord_algebraMap_smul (z : ℤ_[l]) (w : TW (O ⊗[ℤ_[l]] R) T) :
    coord T φ hφ R ((algebraMap ℤ_[l] O z) • w) = algebraMap ℤ_[l] R z * coord T φ hφ R w := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul x t =>
    rw [TensorProduct.smul_tmul', coord_tmul, coord_tmul, inner_smul]
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul o r =>
      rw [inner_tmul, inner_tmul, smul_comm o (algebraMap ℤ_[l] O z) t, hφ, map_mul]; ring
    | add x y hx hy => simp only [mul_add, map_add, hx, hy]
  | add x y hx hy => simp only [smul_add, map_add, hx, hy, mul_add]

theorem coord_toOB (w : TW (OCr l O) T) :
    coord T φ hφ (Per.Bcris l) (TWincl (toOB l O) T w) = acrisToBcris l (coord T φ hφ (Per.Acris l) w) := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul x t =>
    simp only [TWincl, TensorProduct.map_tmul, AlgHom.toLinearMap_apply, LinearMap.id_coe, id_eq,
      coord_tmul]
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul o r =>
      simp only [toOB, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, inner_tmul, map_mul,
        AlgHom.commutes]
    | add x y hx hy => simp only [map_add, hx, hy]
  | add x y hx hy => simp only [map_add, hx, hy]

end GlobalTheory.CoordTW

namespace GlobalTheory

open GlobalTheory.CoordTW in

theorem exists_coord_acris_bcris : ∀ {l : ℕ} [Fact l.Prime] {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [Field K] [Algebra ℚ_[l] K] [Algebra O K] [TopologicalSpace K] {G : Type} [Group G] [TopologicalSpace G] (T : LocLat G ℚ_[l] K O) (φ : ↥T.L.T →+ ℤ_[l]), (∀ (z : ℤ_[l]) (t : ↥T.L.T), φ (algebraMap ℤ_[l] O z • t) = z * φ t) → ∃ (ΦA : TW (OCr l O) T →+ Per.Acris l) (ΦB : TW (OB l O) T →+ Per.Bcris l), (∀ (a : Per.Acris l) (w : TW (OCr l O) T), ΦA (((1 : O) ⊗ₜ[ℤ_[l]] a : OCr l O) • w) = a * ΦA w) ∧ (∀ (y : Per.Bcris l) (w : TW (OB l O) T), ΦB (((1 : O) ⊗ₜ[ℤ_[l]] y : OB l O) • w) = y * ΦB w) ∧ (∀ x : ↥T.L.T, ΦB ((1 : OB l O) ⊗ₜ[O] x) = algebraMap ℤ_[l] (Per.Bcris l) (φ x)) ∧ (∀ (N : ℕ) (w : TW (OCr l O) T), ΦA (((l : O) ^ N) • w) = (l : Per.Acris l) ^ N * ΦA w) ∧ (∀ w : TW (OCr l O) T, ΦB (TWincl (toOB l O) T w) = acrisToBcris l (ΦA w)) := by
  intro l _ O K _ _ _ _ _ _ G _ _ T φ hφ
  refine ⟨coord T φ hφ (Per.Acris l), coord T φ hφ (Per.Bcris l), coord_mul T φ hφ _,
    coord_mul T φ hφ _, coord_one_tmul T φ hφ _, fun N w => ?_, coord_toOB T φ hφ⟩
  have h : ((l : O) ^ N) = algebraMap ℤ_[l] O ((l : ℤ_[l]) ^ N) := by simp
  rw [h, coord_algebraMap_smul]
  simp

end GlobalTheory
