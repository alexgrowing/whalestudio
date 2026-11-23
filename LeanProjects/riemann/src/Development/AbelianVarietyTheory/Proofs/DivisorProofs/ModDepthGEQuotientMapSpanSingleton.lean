import Mathlib
import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.ModDepthGE
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PurityFree
import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.ExistsIsRegularAppendOfModDepthGE
import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.Bridge
open IsLocalRing

namespace GlobalTheory

open Pointwise in

theorem modDepthGE_quotient_map_span_singleton :
    ∀ (R A : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [CommRing A] [Algebra R A]
      [Module.Finite R A] (f : R), f ∈ maximalIdeal R → ∀ [IsLocalRing (R ⧸ Ideal.span {f})],
      IsSMulRegular A f → ∀ n : ℕ, ReciprocityTheory.CA.ModDepthGE R A (n + 1) →
      ReciprocityTheory.CA.ModDepthGE (R ⧸ Ideal.span {f}) (A ⧸ (Ideal.span {f}).map (algebraMap R A)) n := by
  intro R A _ _ _ _ _ _ f hf _ hreg n hd
  have h1 : ReciprocityTheory.CA.ModDepthGE R (QuotSMulTop f A) n := ReciprocityTheory.CA.ModDepthGE.quotSMulTop hf hreg hd
  have heq : (f • (⊤ : Submodule R A)) =
      ((Ideal.span {f}).map (algebraMap R A)).restrictScalars R := by
    ext x
    simp [Submodule.mem_smul_pointwise_iff_exists, Ideal.map_span, Ideal.mem_span_singleton',
      Algebra.smul_def, mul_comm]
  let e : QuotSMulTop f A ≃ₗ[R] (A ⧸ (Ideal.span {f}).map (algebraMap R A)) :=
    (Submodule.quotEquivOfEq _ _ heq).trans
      (Submodule.Quotient.restrictScalarsEquiv R ((Ideal.span {f}).map (algebraMap R A)))
  obtain ⟨rs, hl, hm, hr⟩ := (ReciprocityTheory.CA.modDepthGE_congr e n).mp h1
  refine ⟨rs.map (algebraMap R (R ⧸ Ideal.span {f})), by simp [hl], ?_, ?_⟩
  · intro r hr'
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hr'
    exact ReciprocityTheory.CA.mk_mem_maximalIdeal_quot _ (hm a ha)
  · exact (ReciprocityTheory.CA.isRegular_map_algebraMap_iff' rs).mpr hr

end GlobalTheory
