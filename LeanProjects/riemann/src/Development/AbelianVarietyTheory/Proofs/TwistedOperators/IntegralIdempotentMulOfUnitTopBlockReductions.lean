import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConstMemBddAut
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIntegralInverseAtSplitPlacesOfUnitsStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HalfUnit

variable {D : D7}

local notation "SI" => Formalism.L2.Herm.intAf D.host.F D.host.E

def liftI {b a : ℕ} (N : Matrix (Fin b) (Fin a) (EAf D)) (h : IsIntM N) : Matrix (Fin b) (Fin a) SI :=
  Matrix.of fun i j => ⟨N i j, h i j⟩

theorem liftI_map {b a : ℕ} (N : Matrix (Fin b) (Fin a) (EAf D)) (h : IsIntM N) :
    (liftI N h).map (SI).subtype = N := by
  ext i j
  rw [Matrix.map_apply]
  rfl

theorem isIntM_map {b a : ℕ} (X : Matrix (Fin b) (Fin a) SI) : IsIntM (X.map (SI).subtype) := fun i j => by
  rw [Matrix.map_apply]
  exact (X i j).2

open Classical in

def redE (PP : Formalism.L2.DIV.Pl D.host.E) (x : EAf D) : Formalism.L2.DIV.kP PP :=
  if h : x ∈ SI then Formalism.L2.DIV.resS D.host.F PP ⟨x, h⟩ else 0

theorem redM_apply (PP : Formalism.L2.DIV.Pl D.host.E) {b a : ℕ} (N : Matrix (Fin b) (Fin a) (EAf D)) (i : Fin b) (j : Fin a) :
    redM PP N i j = redE PP (N i j) := rfl

theorem redE_of_mem (PP : Formalism.L2.DIV.Pl D.host.E) {x : EAf D} (hx : x ∈ SI) :
    redE PP x = Formalism.L2.DIV.resS D.host.F PP ⟨x, hx⟩ := by
  unfold redE
  exact dif_pos hx

theorem redE_zero (PP : Formalism.L2.DIV.Pl D.host.E) : redE (D := D) PP 0 = 0 := by
  rw [redE_of_mem PP (Subring.zero_mem _)]
  exact map_zero (Formalism.L2.DIV.resS D.host.F PP)

theorem topL_pos {κ : Type} [Zero κ] {b a k : ℕ} (y : Matrix (Fin b) (Fin a) κ) {i j : Fin k}
    (h : i.val < b ∧ j.val < a) : topL k y i j = y ⟨i.val, h.1⟩ ⟨j.val, h.2⟩ := by
  unfold topL
  exact dif_pos h

theorem topL_neg {κ : Type} [Zero κ] {b a k : ℕ} (y : Matrix (Fin b) (Fin a) κ) {i j : Fin k}
    (h : ¬ (i.val < b ∧ j.val < a)) : topL k y i j = 0 := by
  unfold topL
  exact dif_neg h

theorem redM_map (PP : Formalism.L2.DIV.Pl D.host.E) {b a : ℕ} (X : Matrix (Fin b) (Fin a) SI) :
    redM PP (X.map (SI).subtype) = X.map (Formalism.L2.DIV.resS D.host.F PP) := by
  ext i j
  rw [redM_apply, Matrix.map_apply, Matrix.map_apply]
  exact redE_of_mem PP (X i j).2

theorem isIntM_mul {c b a : ℕ} {A : Matrix (Fin c) (Fin b) (EAf D)} {B : Matrix (Fin b) (Fin a) (EAf D)}
    (hA : IsIntM A) (hB : IsIntM B) : IsIntM (A * B) := fun i j => by
  rw [Matrix.mul_apply]
  exact Subring.sum_mem _ fun k _ => Subring.mul_mem _ (hA i k) (hB k j)

theorem redM_mul (PP : Formalism.L2.DIV.Pl D.host.E) {c b a : ℕ} {A : Matrix (Fin c) (Fin b) (EAf D)}
    {B : Matrix (Fin b) (Fin a) (EAf D)} (hA : IsIntM A) (hB : IsIntM B) :
    redM PP (A * B) = redM PP A * redM PP B := by
  rw [← liftI_map A hA, ← liftI_map B hB, ← Matrix.map_mul, redM_map, redM_map, redM_map, Matrix.map_mul]

theorem isIntM_smul {b a : ℕ} {c : EAf D} (hc : c ∈ SI) {A : Matrix (Fin b) (Fin a) (EAf D)} (hA : IsIntM A) :
    IsIntM (c • A) := fun i j => by
  rw [Matrix.smul_apply, smul_eq_mul]
  exact Subring.mul_mem _ hc (hA i j)

theorem isIntM_adjugate {n : ℕ} {A : Matrix (Fin n) (Fin n) (EAf D)} (hA : IsIntM A) : IsIntM A.adjugate := by
  have key := isIntM_map (liftI A hA).adjugate
  rwa [← RingHom.mapMatrix_apply, RingHom.map_adjugate, RingHom.mapMatrix_apply, liftI_map] at key

theorem det_mem {n : ℕ} {A : Matrix (Fin n) (Fin n) (EAf D)} (hA : IsIntM A) : A.det ∈ SI := by
  have key := RingHom.map_det (SI).subtype (liftI A hA)
  rw [RingHom.mapMatrix_apply, liftI_map] at key
  rw [← key]
  exact ((liftI A hA).det).2

theorem topL_isIntM {m n : ℕ} {A : Matrix (Fin m) (Fin n) (EAf D)} (hA : IsIntM A) : IsIntM (topL n A) := fun i j => by
  by_cases h : i.val < m ∧ j.val < n
  · rw [topL_pos _ h]
    exact hA _ _
  · rw [topL_neg _ h]
    exact Subring.zero_mem _

theorem topL_redM (PP : Formalism.L2.DIV.Pl D.host.E) {m n : ℕ} (A : Matrix (Fin m) (Fin n) (EAf D)) :
    topL n (redM PP A) = redM PP (topL n A) := by
  ext i j
  by_cases h : i.val < m ∧ j.val < n
  · rw [topL_pos _ h, redM_apply, redM_apply, topL_pos _ h]
  · rw [topL_neg _ h, redM_apply, topL_neg _ h, redE_zero]

theorem topL_mul {m n : ℕ} (hnm : n ≤ m) (A : Matrix (Fin m) (Fin n) (EAf D)) (M : Matrix (Fin n) (Fin n) (EAf D)) :
    topL n (A * M) = topL n A * M := by
  ext i j
  have hi : i.val < m := lt_of_lt_of_le i.2 hnm
  rw [topL_pos _ ⟨hi, j.2⟩, Matrix.mul_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [topL_pos _ ⟨hi, k.2⟩]

theorem topL_smul {m n : ℕ} (c : EAf D) (A : Matrix (Fin m) (Fin n) (EAf D)) : topL n (c • A) = c • topL n A := by
  ext i j
  by_cases h : i.val < m ∧ j.val < n
  · rw [topL_pos _ h, Matrix.smul_apply, Matrix.smul_apply, topL_pos _ h]
  · rw [topL_neg _ h, Matrix.smul_apply, topL_neg _ h, smul_zero]

end GlobalTheory.HalfUnit

namespace GlobalTheory.HalfUnit

theorem isUnit_res_det {D : D7} (PP : Formalism.L2.DIV.Pl D.host.E) {n : ℕ} {A : Matrix (Fin n) (Fin n) (EAf D)} (hA : IsIntM A)
    (h : IsUnit (redM PP A).det) : IsUnit (Formalism.L2.DIV.resS D.host.F PP ⟨A.det, det_mem hA⟩) := by
  have e1 : (⟨A.det, det_mem hA⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) = (liftI A hA).det := by
    apply Subtype.ext
    have key := RingHom.map_det (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype (liftI A hA)
    rw [RingHom.mapMatrix_apply, liftI_map] at key
    exact key.symm
  have e2 := redM_map PP (liftI A hA)
  rw [liftI_map] at e2
  rw [e1, RingHom.map_det, RingHom.mapMatrix_apply, ← e2]
  exact h

theorem adj_eq {R : Type} [CommRing R] {n : ℕ} (A B G : Matrix (Fin n) (Fin n) R) (f w : R) (hB : B = A * G)
    (hw : A.det * w * f = f) (hfB : f • B = B) : f • G = (w • A.adjugate) * B := by
  rw [← hfB, hB, Matrix.mul_smul, Matrix.smul_mul, ← Matrix.mul_assoc, Matrix.adjugate_mul, Matrix.smul_mul,
    Matrix.one_mul, smul_smul, smul_smul]
  conv_lhs => rw [← hw]
  congr 1
  ring

theorem smul_mul_fix {R : Type} [CommRing R] {a b c : ℕ} (A : Matrix (Fin a) (Fin b) R) (G : Matrix (Fin b) (Fin c) R)
    (f : R) (h : f • A = A) : f • (A * G) = A * G := by
  rw [← Matrix.smul_mul, h]

theorem mul_smul_fix {R : Type} [CommRing R] {n : ℕ} (A B G : Matrix (Fin n) (Fin n) R) (f : R) (hB : B = A * G)
    (h : f • B = B) : A * (f • G) = B := by
  rw [Matrix.mul_smul, ← hB, h]

theorem int_of_unit_tops : ∀ {D : D7} (m n : ℕ), n ≤ m → ∀ (Z : Finset (Pl D.host.E)) (e : AE D), IsIdemSum e Z → ∀ (u : Matrix (Fin m) (Fin n) (EAf D)) (γ : GL (Fin n) (EAf D)), IsIntM u → IsIntM (HMul.hMul u (γ⁻¹ : GL (Fin n) (EAf D)).1) → (∀ i j, toEAf D e * u i j = u i j) → (∀ PP ∈ Z, IsUnit (topL n (redM PP u)).det) → (∀ PP ∈ Z, IsUnit (topL n (redM PP (HMul.hMul u (γ⁻¹ : GL (Fin n) (EAf D)).1))).det) → IsIntM (toEAf D e • γ.1) ∧ IsIntM (toEAf D e • (γ⁻¹ : GL (Fin n) (EAf D)).1) ∧ ∀ PP ∈ Z, topL n (redM PP (HMul.hMul u (γ⁻¹ : GL (Fin n) (EAf D)).1)) * redM PP (toEAf D e • γ.1) = topL n (redM PP u) := by
  intro D m n hnm Z e he u γ hu hv hfu hU hV
  have hUi : IsIntM (topL n u) := topL_isIntM hu
  have hVi : IsIntM (topL n (u * (γ⁻¹ : GL (Fin n) (EAf D)).1)) := topL_isIntM hv
  have hVeq : topL n (u * (γ⁻¹ : GL (Fin n) (EAf D)).1) = topL n u * (γ⁻¹ : GL (Fin n) (EAf D)).1 :=
    topL_mul hnm _ _
  have hUeq : topL n u = topL n (u * (γ⁻¹ : GL (Fin n) (EAf D)).1) * γ.1 := by
    rw [hVeq, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
  have hfU : toEAf D e • topL n u = topL n u := by
    ext i j
    by_cases h : i.val < m ∧ j.val < n
    · rw [Matrix.smul_apply, topL_pos _ h, smul_eq_mul, hfu]
    · rw [Matrix.smul_apply, topL_neg _ h, smul_zero]
  have hfV : toEAf D e • topL n (u * (γ⁻¹ : GL (Fin n) (EAf D)).1) = topL n (u * (γ⁻¹ : GL (Fin n) (EAf D)).1) := by
    rw [hVeq]
    exact smul_mul_fix _ _ _ hfU
  obtain ⟨w, hw, hwe⟩ := GlobalTheory.T.exists_integral_inverse_at_splitPlaces_of_units Z e he _ (det_mem hUi) fun PP hPP =>
    isUnit_res_det PP hUi (by rw [← topL_redM]; exact hU PP hPP)
  obtain ⟨w', hw', hwe'⟩ := GlobalTheory.T.exists_integral_inverse_at_splitPlaces_of_units Z e he _ (det_mem hVi) fun PP hPP =>
    isUnit_res_det PP hVi (by rw [← topL_redM]; exact hV PP hPP)
  have hγ := adj_eq _ _ _ (toEAf D e) w' hUeq hwe' hfU
  have hγi := adj_eq _ _ _ (toEAf D e) w hVeq hwe hfV
  have hfγ : IsIntM (toEAf D e • γ.1) := by
    rw [hγ]
    exact isIntM_mul (isIntM_smul hw' (isIntM_adjugate hVi)) hUi
  refine ⟨hfγ, ?_, ?_⟩
  · rw [hγi]
    exact isIntM_mul (isIntM_smul hw (isIntM_adjugate hUi)) hVi
  · intro PP _
    rw [topL_redM, topL_redM, ← redM_mul PP hVi hfγ, mul_smul_fix _ _ _ _ hUeq hfU]

end GlobalTheory.HalfUnit
