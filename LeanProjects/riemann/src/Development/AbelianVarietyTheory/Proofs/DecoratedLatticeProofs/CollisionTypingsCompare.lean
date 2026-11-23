import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.VanishingGramTermsBoundParams
import Development.AbelianVarietyTheory.BlockTheory.SiegelEisenstein.WordData
import Formalism.LocalToGlobal.SiegelLatticeTheory.ResidEvFree
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
import Formalism.SharpRestriction.CuspSpanNormBounds.KappaEndpoints
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.FirstPacketUnfoldedOfNongenericUnit

noncomputable section

open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2

namespace GlobalTheory.CollCompare

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.Core.Deg GlobalTheory.IndefiniteRowSideFullHecke.WordCollisionBound

theorem uOne_last (D : D7) (u w : D.what₂.Word) (τ : D.what₂.Tau) : uOne D w τ D.R.k = uOne D u τ D.R.k := by
  have hk : 0 < D.R.k := by have := D.R.m_add_three_le_k; omega
  have h : 1 ≤ D.R.k ∧ D.R.k ≤ D.R.k := ⟨hk, le_rfl⟩
  simp only [uOne, dif_pos h, uS]
  have a := D.hcW_last w τ hk
  have b := D.hcW_last u τ hk
  exact congrArg (fun q : ℚ => (q : ℝ)) (a.trans b.symm)

theorem splits_level (D : D7) (w : D.what₂.Word) : SplitsE D (D.mem w).A.T :=
  S.splitsCompl_of_ncard _ _ (D.mem w).A.T_prime
    (Formalism.L2.GlobalTheoryTheory.FiltrationCocycleLiftCriterion.split_clause _ Formalism.L2.SG.ResidEvFree.cycSplit_holds _ (D.mem w).A.T_prime (S.level_norm_one_mod_conductor _ w)).2

def CappedBound : Prop :=
  ∀ Cg cb Cu cT CT CW : ℝ, 0 < cb → 0 < cT →
    ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
      ∀ (D : D7) (L : ℝ) (X : HidaSetting D) (Y : Full X) (hF : FinX Y) (u : D.what₂.Word),
        (∀ w, Tr D w ≤ Real.exp L ^ (CW * D.R.m)) →
        1 < L → WordData D u → Sizes D L u C' Cl Cg cb Cu cT CT →
        Formalism.BasicNotions.Ties D → Formalism.MainNotions.LocalBesselAndTopKernel.FamilyMidVolume D → Nonempty (SIso D.s (sOf hF)) →
        ConcTie X Y → (Y.tO u u).AbsConv →
        (Y.tO u u).pairAbs ((Y.tO u u).big (Y.tO u u).nzSet) ≤
          Real.exp (-((1 / 3 : ℝ) * D.R.k * D.R.f * Real.log D.R.k)) *
            (duC X Y u ^ 2 / DstC X + duC X Y u)

end GlobalTheory.CollCompare
