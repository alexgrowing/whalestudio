import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.HodgeTateFromSandwich
import GroundTheory.GlobalFields.Adele.Approximation

open NumberField IsDedekindDomain

namespace UpperTheory.V.Z.Sym.Glob

theorem apx {F : Type} [Field F] [NumberField F] (d : F) (hd : d ≠ 0) (y : ∀ v : Pl F, Kv v)
    (hy : ∀ v, cv v d * y v ∈ v.adicCompletionIntegers F) : ∃ x : F, ∀ v, y v - cv v x ∈ v.adicCompletionIntegers F := by
  classical
  have hinv : ∀ᶠ v in Filter.cofinite, cv v d⁻¹ ∈ (v : Pl F).adicCompletionIntegers F :=
    (algebraMap F (FiniteAdeleRing (𝓞 F) F) d⁻¹).2
  have hev : ∀ᶠ v in Filter.cofinite, y v ∈ (v : Pl F).adicCompletionIntegers F := by
    refine hinv.mono fun v hv => ?_
    have e : y v = cv v d⁻¹ * (cv v d * y v) := by
      rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hd, map_one, one_mul]
    rw [e]
    exact mul_mem hv (hy v)
  obtain ⟨k, hk⟩ := GroundTheory.Global.exists_sub_mem_integralFiniteAdeles (R := 𝓞 F) (K := F)
    (RestrictedProduct.mk y hev : FiniteAdeleRing (𝓞 F) F)
  exact ⟨k, fun v => GroundTheory.Global.mem_integralFiniteAdeles.mp hk v⟩

end UpperTheory.V.Z.Sym.Glob
