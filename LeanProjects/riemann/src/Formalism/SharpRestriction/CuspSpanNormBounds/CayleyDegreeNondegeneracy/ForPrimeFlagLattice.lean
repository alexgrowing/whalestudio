import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.MinkowskiDividesFactorialOfBound
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.NcardPrimesOverOfSplitsCompl
import Formalism.FlagUnipotentLattices.CardSubgroupsOfIndexLe

noncomputable section

namespace Formalism.MainNotions.BridgeLemma₂

open NumberField Module Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def ForPrimeFlagLattice (D : D7) (u : D.what₂.Word)
    (Q : (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) → LatV D → Prop) : Prop :=
  (Tu D u).Prime → 3 ≤ Tu D u → SplitsCompletely (E := D.host.E) (Tu D u) →
  ∀ F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E), F0.e = D.sp.hypE → F0.z = D.zmOf u →
  ∀ Λ : LatV D, IsRowLat D F0 Λ → Q F0 Λ

def BaseLatticeStructure (D : D7) (u : D.what₂.Word) : Prop :=
  ForPrimeFlagLattice D u fun F0 Λ =>
    Submodule.IsLattice D.host.E (L0X D Λ (lf D F0)) ∧
    Formalism.HermitianLatticesTheory.IsIntegralLat (D.sp.X 0).hT (L0X D Λ (lf D F0)) ∧
    latDetH (D.sp.X 0).hT (L0X D Λ (lf D F0)) = ((Tu D u ^ D.R.f : ℕ) : ℝ) ∧
    DiscGen (D.sp.X 0).hT (L0X D Λ (lf D F0)) 1 ∧
    ∀ p : Ideal (𝓞 D.host.F), p.IsMaximal → ((Tu D u : ℕ) : 𝓞 D.host.F) ∈ p →
      eP (D.sp.X 0).hT (L0X D Λ (lf D F0)) p = 1

def BaseLatticeLevel (D : D7) (u : D.what₂.Word) : Prop :=
  ForPrimeFlagLattice D u fun F0 Λ =>
    levelIdx (D.sp.X 0).hT (L0X D Λ (lf D F0)) (Tu D u ^ D.R.f) = (Tu D u - 1) ^ D.R.f

def WordRowsGluing (D : D7) (u : D.what₂.Word) : Prop :=
  ForPrimeFlagLattice D u fun F0 Λ => ∀ s : Finset (LatV D), IsRowReps D F0 s →
    massRows D F0 s = Formalism.HermitianLatticesTheory.mass (D.sp.X 0).hT (L0X D Λ (lf D F0)) * ((Tu D u : ℝ) - 1) ^ D.R.f

end Formalism.MainNotions.BridgeLemma₂

end
