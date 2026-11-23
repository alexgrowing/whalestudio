import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LevGapFacts
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GapAtLeast
import Formalism.SatakeDualWeyl.DefsCS
import Formalism.ThetaLiftIndependence.Statement
import Formalism.HermitianLattices.StatementMass

noncomputable section

namespace Formalism.MainNotions.Gaps.CC

open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.MainNotions.StandardLattice Formalism.MainNotions.Gaps.LG
open scoped TensorProduct

def FibCount : Prop :=
  ∀ (G : Type) [Group G] (Γ U K : Subgroup G), U ≤ K → U.relIndex K ≠ 0 → Finite (ClassSet Γ K) →
    (∀ g : G, Finite (stabAt Γ K g)) → (∀ (g : G) (γ : Γ), g⁻¹ * (γ : G) * g ∈ U → γ = 1) →
    ∀ s : ClassSet Γ K → G, (∀ c, DoubleCoset.mk Γ K (s c) = c) →
      (Nat.card (ClassSet Γ U) : ℝ) =
        (U.relIndex K : ℝ) * ∑ᶠ c : ClassSet Γ K, ((Nat.card (stabAt Γ K (s c)) : ℕ) : ℝ)⁻¹

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {k : ℕ}
  (σ : E →ₐ[F] E) (J : Matrix (Fin k) (Fin k) E)

abbrev GAf : Subgroup (GL (Fin k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) := UPts σ J (FiniteAdeleRing (𝓞 F) F)

def Kstd : Subgroup (GL (Fin k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) := levelAfL σ J (stdLat E k)

abbrev GamG : Subgroup (GAf σ J) := (ratPts σ J (FiniteAdeleRing (𝓞 F) F)).subgroupOf (GAf σ J)

abbrev KstdG : Subgroup (GAf σ J) := (Kstd σ J).subgroupOf (GAf σ J)

abbrev latOfG (g : GL (Fin k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) : Submodule (𝓞 E) (Fin k → E) :=
  CS.globLat g (stdLat E k)

def KFinite : Prop :=
  Finite (ClassSet (GamG σ J) (KstdG σ J)) ∧ ∀ g : GAf σ J, Finite (stabAt (GamG σ J) (KstdG σ J) g)

variable [StarRing E]

def GenusIn : Prop :=
  ∀ g ∈ GAf σ J, latOfG (F := F) g ∈ Formalism.HermitianLatticesTheory.genus (stdForm E k) (stdLat E k)

def GenusSurj : Prop :=
  ∀ M ∈ Formalism.HermitianLatticesTheory.genus (stdForm E k) (stdLat E k), ∃ g ∈ GAf σ J, latOfG (F := F) g = M

def StabAut : Prop :=
  ∀ g : GAf σ J, Nat.card (stabAt (GamG σ J) (KstdG σ J) g) =
    Nat.card (Formalism.ThetaLiftIndependence.autL (stdForm E k) (latOfG (F := F) (g : GL (Fin k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))))

def MassSum : Prop :=
  ∀ s : ClassSet (GamG σ J) (KstdG σ J) → GAf σ J, (∀ c, DoubleCoset.mk (GamG σ J) (KstdG σ J) (s c) = c) →
    Formalism.HermitianLatticesTheory.mass (stdForm E k) (stdLat E k) =
      ∑ᶠ c : ClassSet (GamG σ J) (KstdG σ J), ((Nat.card (stabAt (GamG σ J) (KstdG σ J) (s c)) : ℕ) : ℝ)⁻¹

end Gen

section ParS

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {k : ℕ} (P : Par F E k)

def IdxOK (f : ℕ) : Prop :=
  ∀ S : P.Splits, P.U S ≤ Kstd P.σ P.J ∧
    (((P.U S).relIndex (Kstd P.σ P.J) : ℕ) : ℝ) =
      idxColLoc (P.gp 0) k ^ f * idxColLoc (P.gp 1) k ^ f * ((P.T : ℝ) ^ k - 1) ^ f

end ParS

end Formalism.MainNotions.Gaps.CC

end
