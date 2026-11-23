import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.PrimitiveMeanOverWords
import Formalism.SharpRestriction.CuspSpanNormBounds.AutLzFiniteOfLoop

noncomputable section

open scoped Classical

namespace Formalism.MainNotions.BridgeLemma₂

open NumberField Module Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt
open scoped ENNReal

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section FreeSingleHomotopyEquivDiscreteChains

variable (D : D7)

def SamePairEquivalence (Λ : LatV D) {T : D.host.E} (T' : D.host.E) (F : LFlag (hS D) D.R.rS T) : Prop :=
  (∀ p q : Trip D T', PEqv D Λ F p q → PEqv D Λ F q p) ∧
    ∀ p q t : Trip D T', PEqv D Λ F p q → PEqv D Λ F q t → PEqv D Λ F p t

variable (large₂ : SizeData₂ D) (u u' : D.what₂.Word)

def PairsModuloNormFixedQuadruple (C' Cl Cg cb Cu cT CT C0 A : ℝ) : Prop :=
  Hyp D large₂ u u' C' Cl Cg cb Cu cT CT C0 A →
  ∀ F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E), F0.e = D.sp.hypE → F0.z = D.zmOf u →
  ∀ Λ : LatV D, IsRowLat D F0 Λ → ∀ (Z' Z'' : GramM D) (s : ℕ) (De : ℝ), 1 ≤ s →
  ∀ p₀ ∈ PairSet D Λ ((Tu D u' : ℕ) : D.host.E) (lf D F0) Z' Z'' s De,
    (cntCl {p | p ∈ PairSet D Λ ((Tu D u' : ℕ) : D.host.E) (lf D F0) Z' Z'' s De ∧
        quadrupleOfTriple D Λ (lf D F0) p = quadrupleOfTriple D Λ (lf D F0) p₀ ∧
        TEqv D Λ (lf D F0) p₀.1 p.1 ∧ TEqv D Λ (lf D F0) p₀.2.1 p.2.1} (PEqv D Λ (lf D F0)) : ℝ≥0∞) ≤
      (((4 * D.R.f * s).factorial : ℕ) : ℝ≥0∞)

end FreeSingleHomotopyEquivDiscreteChains

end Formalism.MainNotions.BridgeLemma₂

end
