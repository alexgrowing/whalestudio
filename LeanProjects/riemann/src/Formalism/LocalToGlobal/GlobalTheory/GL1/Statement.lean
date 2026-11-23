import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.ParConsts
import Formalism.SharpRestriction.GlobalSchurBounds.CMFieldLemmas
import Formalism.SatakeDualWeyl.StatementC

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion

open NumberField IsDedekindDomain TensorProduct

def CompactFixesLattice : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (k : ℕ),
  letI := Formalism.MainNotions.UnusedSlot33.tensTop (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
  ∀ U : Subgroup (GL (Fin k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)),
    IsCompact (U : Set (GL (Fin k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))) →
    ∃ Λ : Submodule (𝓞 E) (Fin k → E), Module.Finite (𝓞 E) Λ ∧
      Submodule.span E (Λ : Set (Fin k → E)) = ⊤ ∧
      U ≤ Formalism.UG.stabGL (Formalism.UG.latS (F := F) (FiniteAdeleRing (𝓞 F) F)
        (Formalism.UG.tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (Formalism.UG.intOE E) (Formalism.UG.intAd F)) Λ)

def AdelicLatticeLink : Prop :=
  ∀ D : Formalism.BasicNotions.D7, CompactFixesLattice → Formalism.MainNotions.UnusedSlot33.division_rows_rational_lattice D

def AdelicLatticeLinkFamily : Prop :=
  ∀ (eps : ℝ) (Fm : Formalism.MainNotions.FamP eps), CompactFixesLattice →
    ∀ x : ℝ, Fm.x1 < x → ∀ i : Fm.Ix x, Formalism.MainNotions.UnusedSlot33.division_rows_rational_lattice (Fm.D x i)

end Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion

end
