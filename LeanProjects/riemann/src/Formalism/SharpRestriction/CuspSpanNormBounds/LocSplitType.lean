import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeRowsGenus

noncomputable section

namespace Formalism.MainNotions.BridgeRowsGenus

open NumberField Formalism.HermitianLatticesTheory

section Loc

variable {E : Type} [Field E] [NumberField E] [StarRing E]
  {V : Type} [AddCommGroup V] [Module E V] [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V]

def LocTypeAt (h : V →ₗ⋆[E] V →ₗ[E] E) (p : Ideal (𝓞 E)) (L : Submodule (𝓞 E) V) : Prop :=
  Nonempty ((↥(loc (K := E) p (dual h L)) ⧸ (loc (K := E) p L).comap (loc (K := E) p (dual h L)).subtype) ≃ₗ[𝓞 E]
    (𝓞 E ⧸ (p * conjIdeal (K := E) p)))

end Loc

def ArithType : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E],
    Formalism.BasicNotions.CMData F E → ∀ (S : Formalism.BasicNotions.HSpace E) (T : ℕ), T.Prime → 3 ≤ T → Formalism.MainNotions.S.SplitsCompl E T →
    ∀ L : Submodule (𝓞 E) S.V, IsTypeT (F := F) S.hT T L →
      (∀ p : Ideal (𝓞 E), p.IsMaximal → ((T : ℕ) : 𝓞 E) ∉ p → IsUnimodularAt S.hT p L) ∧
      (∀ p : Ideal (𝓞 E), p.IsMaximal → ((T : ℕ) : 𝓞 E) ∈ p → conjIdeal (K := E) p ≠ p ∧ LocTypeAt S.hT p L)

def LocUnimod : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E],
    Formalism.BasicNotions.CMData F E → ∀ (S : Formalism.BasicNotions.HSpace E) (L M : Submodule (𝓞 E) S.V),
    Submodule.IsLattice E L → Submodule.IsLattice E M →
    ∀ p : Ideal (𝓞 E), p.IsMaximal → IsUnimodularAt S.hT p L → IsUnimodularAt S.hT p M →
      ∃ g ∈ isom S.hT, gmap g (loc (K := E) p L) = loc (K := E) p M

def LocSplitType : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E],
    Formalism.BasicNotions.CMData F E → ∀ (S : Formalism.BasicNotions.HSpace E) (L M : Submodule (𝓞 E) S.V),
    Submodule.IsLattice E L → Submodule.IsLattice E M → IsIntegralLat S.hT L → IsIntegralLat S.hT M →
    ∀ p : Ideal (𝓞 E), p.IsMaximal → conjIdeal (K := E) p ≠ p → LocTypeAt S.hT p L → LocTypeAt S.hT p M →
      ∃ g ∈ isom S.hT, gmap g (loc (K := E) p L) = loc (K := E) p M

end Formalism.MainNotions.BridgeRowsGenus

end
