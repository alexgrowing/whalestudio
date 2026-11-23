import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.IsCoordA
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimilitudeActionAdelicLattice
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoprimeNsmulEndomorphismPreservesCompletio
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeCompletionEqLatticeVectorAddNsmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntDvdOfEqNatMulIntegralAdeleAwayFromP

noncomputable section

open NumberField
open GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo
open scoped TensorProduct

namespace UpperTheory.Gal.W2.Wit

variable {p : ℕ} [Fact p.Prime]

theorem actQ_tmul {D : Datum p} (b : D.O) (q : ℚ) (x : D.La) : actQ D b (q ⊗ₜ x) = q ⊗ₜ (b • x) := by
  simp only [actQ, LinearMap.baseChange_tmul]; rfl

theorem actQ_one (D : Datum p) (w : VQ D) : actQ D 1 w = w := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul q x => rw [actQ_tmul, one_smul]
  | add u v hu hv => rw [map_add, hu, hv]

theorem actQ_mul (D : Datum p) (a b : D.O) (w : VQ D) : actQ D (a * b) w = actQ D a (actQ D b w) := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul q x => rw [actQ_tmul, actQ_tmul, actQ_tmul, mul_smul]
  | add u v hu hv => rw [map_add, hu, hv, map_add, map_add]

theorem actQ_add (D : Datum p) (a b : D.O) (w : VQ D) : actQ D (a + b) w = actQ D a w + actQ D b w := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul q x => rw [actQ_tmul, actQ_tmul, actQ_tmul, add_smul, TensorProduct.tmul_add]
  | add u v hu hv => rw [map_add, hu, hv, map_add, map_add]; abel

theorem actQ_zero (D : Datum p) (w : VQ D) : actQ D 0 w = 0 := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul q x => rw [actQ_tmul, zero_smul, TensorProduct.tmul_zero]
  | add u v hu hv => rw [map_add, hu, hv, add_zero]

structure Sys (D : Datum p) where
  T : Module.End (AfP p) (AfP p ⊗[ℚ] VQ D)
  S : Module.End (AfP p) (AfP p ⊗[ℚ] VQ D)
  ST : S * T = 1
  comm : ∀ c : D.O, T * (actQ D c).baseChange (AfP p) = (actQ D c).baseChange (AfP p) * T
  B : LinearMap.BilinForm ℚ (VQ D)
  alt : ∀ u, B u u = 0
  nondeg : ∀ u, (∀ w, B u w = 0) → u = 0
  adj : ∀ (c : D.O) u w, B (actQ D c u) w = B u (actQ D (D.inv c) w)
  M : AddSubgroup (VQ D)
  hM : UpperTheory.Gal.W2.IsPLat D M
  s : ℚ
  s_pos : 0 < s
  perf : ∀ w, w ∈ M ↔ ∀ u ∈ M, (s * B w u).den.Coprime p
  ε : (AfP p)ˣ
  ε_int : IsIntAf (ε : AfP p)
  ε_inv : IsIntAf ((ε⁻¹ : (AfP p)ˣ) : AfP p)
  form : ∀ u w, algebraMap ℚ (AfP p) (s * B u w) =
    (ε : AfP p) * (D.EF.baseChange ℚ).baseChange (AfP p) (T ((1 : AfP p) ⊗ₜ u)) (T ((1 : AfP p) ⊗ₜ w))
  dense : ∀ n : ℕ, 0 < n → ∀ z, ∃ w, ∃ e ∈ LaHat D, z = T ((1 : AfP p) ⊗ₜ w) + n • e

namespace Sys

variable {D : Datum p} (X : Sys D)

def r : VQ D →ₗ[ℚ] AfP p ⊗[ℚ] VQ D :=
  (X.T.restrictScalars ℚ) ∘ₗ (TensorProduct.mk ℚ (AfP p) (VQ D) 1)

theorem r_apply (w : VQ D) : X.r w = X.T ((1 : AfP p) ⊗ₜ w) := rfl

theorem r_act (c : D.O) (w : VQ D) : X.r (actQ D c w) = (actQ D c).baseChange (AfP p) (X.r w) := by
  rw [r_apply, r_apply]
  have h := LinearMap.congr_fun (X.comm c) ((1 : AfP p) ⊗ₜ w)
  rw [Module.End.mul_apply, Module.End.mul_apply, LinearMap.baseChange_tmul] at h
  exact h

def lat : AddSubgroup (VQ D) where
  carrier := {w | w ∈ X.M ∧ X.r w ∈ LaHat D}
  zero_mem' := ⟨zero_mem _, by rw [map_zero]; exact zero_mem _⟩
  add_mem' := fun h h' => ⟨add_mem h.1 h'.1, by rw [map_add]; exact add_mem h.2 h'.2⟩
  neg_mem' := fun h => ⟨neg_mem h.1, by rw [map_neg]; exact neg_mem h.2⟩

theorem mem_lat {w : VQ D} : w ∈ X.lat ↔ w ∈ X.M ∧ X.r w ∈ LaHat D := Iff.rfl

theorem act_mem (c : D.O) {w : VQ D} (hw : w ∈ X.lat) : actQ D c w ∈ X.lat :=
  ⟨X.hM.1 c w hw.1, by rw [r_act]; exact GlobalTheory.AdelicSim.bc_mem D c hw.2⟩

instance : Module D.O X.lat where
  smul c w := ⟨actQ D c w.1, X.act_mem c w.2⟩
  one_smul w := Subtype.ext (actQ_one D w.1)
  mul_smul a b w := Subtype.ext (actQ_mul D a b w.1)
  smul_zero c := Subtype.ext (map_zero (actQ D c))
  smul_add c u v := Subtype.ext (map_add (actQ D c) u.1 v.1)
  add_smul a b w := Subtype.ext (actQ_add D a b w.1)
  zero_smul w := Subtype.ext (actQ_zero D w.1)

theorem coe_smul (c : D.O) (w : X.lat) : ((c • w : X.lat) : VQ D) = actQ D c w := rfl

end Sys

end UpperTheory.Gal.W2.Wit
