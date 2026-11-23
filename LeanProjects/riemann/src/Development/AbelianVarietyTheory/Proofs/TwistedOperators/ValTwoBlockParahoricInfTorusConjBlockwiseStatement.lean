import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ValTwoBlockParahoricInfTorusConjBlockwise
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BorelParam
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.val_twoBlockParahoric_inf_torusConj_blockwise : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ϖ : kˣ),
    valuation k (ϖ : k) = uniformizer k →
    ∀ (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (e : D → ℤ),
    Units.val '' (((parahoric k A D).map (MulAut.conj (mtor (A := A) ϖ e)).toMonoidHom ⊓ parahoric k A D :
        Subgroup (GL (A ⊕ D) k)) : Set (GL (A ⊕ D) k)) =
      {x | x.toBlocks₁₁ ∈ Units.val '' (KO k A : Set (GL A k)) ∧
        x.toBlocks₁₂ ∈ {y : Matrix A D k | ∀ i j, valuation k (y i j) ≤ valuation k ((ϖ : k) ^ max 0 (-e j))} ∧
        x.toBlocks₂₁ ∈ {y : Matrix D A k | ∀ i j, valuation k (y i j) ≤ valuation k ((ϖ : k) ^ (1 + max 0 (e i)))} ∧
        x.toBlocks₂₂ ∈ Units.val '' (((KO k D).map (MulAut.conj (torusElt k D ϖ e)).toMonoidHom ⊓ KO k D :
          Subgroup (GL D k)) : Set (GL D k))} := by
  first | exact @GlobalTheory.ParahoricConjBlocks.blockset | exact GlobalTheory.ParahoricConjBlocks.blockset | (intros; apply GlobalTheory.ParahoricConjBlocks.blockset <;> assumption)
