import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.SigmaSplit
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.InvMemLatMonoidOfMemAwaySupp
open UpperTheory.Gal.LocalSmoothExtension

theorem UpperTheory.Gal.LocalSmoothExtension.kNNormal_of :
    KNNormal := by
  intro p _ D G L M
  have key : ∀ k ∈ L.KN 1, ∀ u, L.CongOne M u → L.CongOne M (k * u * k⁻¹) := by
    intro k hk u hu v hv
    obtain ⟨w, hw, e⟩ := hu _ (UpperTheory.Gal.Int.Geo.integ_of_mem (inv_mem hk) v hv)
    refine ⟨L.actG k w, UpperTheory.Gal.Int.Geo.integ_of_mem hk w hw, ?_⟩
    have h1 : L.actG k (L.actG k⁻¹ v) = v := by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, e, map_add, map_nsmul, h1]
  refine ⟨fun k hk u hu => ⟨key k hk u hu.1, ?_⟩, fun hM => GlobalTheory.W2.relIndex_KN_ne_zero L one_pos hM⟩
  have e : (k * u * k⁻¹)⁻¹ = k * u⁻¹ * k⁻¹ := by group
  rw [e]
  exact key k hk _ hu.2
