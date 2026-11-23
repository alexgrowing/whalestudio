import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LengthQuotientSmulSupLeIntermediate
import Mathlib
open Pointwise
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.length_quotient_smul_sup_le_intermediate : ∀ (O A : Type) [CommRing O] [AddCommGroup A] [Module O A] (Z B B' : Submodule O A) (a : O), B ≤ B' → Module.length O (↥Z ⧸ (Z.map (a • (LinearMap.id : A →ₗ[O] A)) ⊔ B).comap Z.subtype) ≤ Module.length O ((↥Z ⧸ B'.comap Z.subtype) ⧸ LinearMap.range (a • (LinearMap.id : (↥Z ⧸ B'.comap Z.subtype) →ₗ[O] (↥Z ⧸ B'.comap Z.subtype)))) + Module.length O (↥(Z ⊓ B') ⧸ B.comap (Z ⊓ B').subtype) := by
  first | exact @GlobalTheory.length_quotient_smul_sup_le | exact GlobalTheory.length_quotient_smul_sup_le | (intros; apply GlobalTheory.length_quotient_smul_sup_le <;> assumption)
