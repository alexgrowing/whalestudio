import Formalism.SharpRestriction.CuspSpanNormBounds.CntPartners

noncomputable section

namespace Formalism.MainNotions.BridgeRowsGenus

open NumberField Module Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
  {V : Type} [AddCommGroup V] [Module E V] [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V]

def IsTypeT (h : V →ₗ⋆[E] V →ₗ[E] E) (T : ℕ) (L : Submodule (𝓞 E) V) : Prop :=
  Submodule.IsLattice E L ∧ Formalism.HermitianLatticesTheory.IsIntegralLat h L ∧
    latDetH h L = ((T ^ Module.finrank ℚ F : ℕ) : ℝ) ∧ DiscGen h L 1 ∧
    ∀ p : Ideal (𝓞 F), p.IsMaximal → ((T : ℕ) : 𝓞 F) ∈ p → eP h L p = 1

end Gen

def TypeGenus : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E],
    Formalism.BasicNotions.CMData F E → ∀ (S : Formalism.BasicNotions.HSpace E) (T : ℕ), T.Prime → 3 ≤ T → Formalism.MainNotions.S.SplitsCompl E T →
    ∀ L M : Submodule (𝓞 E) S.V, IsTypeT (F := F) S.hT T L → IsTypeT (F := F) S.hT T M →
      M ∈ Formalism.HermitianLatticesTheory.genus S.hT L

end Formalism.MainNotions.BridgeRowsGenus

end
