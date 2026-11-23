import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.UniformizerIntegrality.PtTopOf

noncomputable section

open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4

namespace UpperTheory.V.Z.Kato.Sym.PT

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

private theorem isIntegral_of_mem_overY (X : Tower Ω ε) (x : X.K) (h : ∀ W, X.OverY W → x ∈ W) :
    IsIntegral (Algebra.adjoin Ω {X.jK}) x := by
  by_contra hx
  obtain ⟨V, hRV, hxV⟩ := Subring.exists_le_valuationSubring_of_isIntegrallyClosedIn
    (K := X.K) (x := x) (R := (integralClosure (Algebra.adjoin Ω {X.jK}) X.K).toSubring)
    (fun hm => hx hm)
  apply hxV
  refine h V ⟨fun c => hRV ?_, hRV ?_⟩
  · change algebraMap Ω X.K c ∈ integralClosure (Algebra.adjoin Ω {X.jK}) X.K
    have : algebraMap Ω X.K c = algebraMap (Algebra.adjoin Ω {X.jK}) X.K (algebraMap Ω _ c) := rfl
    rw [this]
    exact isIntegral_algebraMap
  · change X.jK ∈ integralClosure (Algebra.adjoin Ω {X.jK}) X.K
    have : X.jK = algebraMap (Algebra.adjoin Ω {X.jK}) X.K ⟨X.jK, Algebra.subset_adjoin rfl⟩ := rfl
    rw [this]
    exact isIntegral_algebraMap

theorem intU : IntU := by
  intro Ω _ _ _ ε X M u hu
  refine ⟨isIntegral_of_mem_overY X u fun W hW => ?_, isIntegral_of_mem_overY X u⁻¹ fun W hW => ?_⟩
  · exact (ValuationSubring.valuation_le_one_iff W u).1 (hu.2 W hW).le
  · refine (ValuationSubring.valuation_le_one_iff W u⁻¹).1 ?_
    rw [map_inv₀, hu.2 W hW, inv_one]

end UpperTheory.V.Z.Kato.Sym.PT

end
