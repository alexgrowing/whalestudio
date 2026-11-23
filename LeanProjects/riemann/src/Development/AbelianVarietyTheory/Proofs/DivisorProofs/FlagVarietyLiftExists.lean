import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StalkStepMono
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvMulApplyEqZeroOfMinor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchubertCellOpenImmersion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagPointInSomeCell
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEqFlagPtOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColSec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TautologicalFlagUniversalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TautologicalSubbundleRankStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoInclLastStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackFlagSectionsFrame
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.FlagZ GlobalTheory.FlagZ.Univ
open GlobalTheory.QCoh (freeModule)

noncomputable section

namespace GlobalTheory.FlagZ.Univ

def univFlag (ι : Type) [Fintype ι] (N : ℕ) (τ : ι) :
    Vert.Flag ((Scheme.Modules.pullback (flStr ι N)).obj (GlobalTheory.FlagZ.Taut.stdE N)) N where
  F := F ι N τ
  ι := incl ι N τ
  isSubbundle i := (GlobalTheory.T.tautological_subbundle_rank ι N τ i).2
  isVB i := (GlobalTheory.T.tautological_subbundle_rank ι N τ i).1
  step := step ι N τ
  step_ι := step_incl ι N τ
  isIso_last := GlobalTheory.T.isIso_incl_last' ι N τ

theorem isTaut_univFlag (ι : Type) [Fintype ι] (N : ℕ) : GlobalTheory.FlagZ.Taut.IsTaut ι N (univFlag ι N) :=
  fun A _ g a l => GlobalTheory.T.pullback_flag_sections_frame ι N A g a l

theorem exists_lifts (ι : Type) [Fintype ι] (N : ℕ) (T : Scheme.{0}) (g : T ⟶ Sp ℤ)
    (fl' : ι → Vert.Flag ((Scheme.Modules.pullback g).obj (freeModule (Sp ℤ) (Fin N))) N) : ∃ g', Lifts g fl' g' := by
  obtain ⟨g', w, h⟩ := GlobalTheory.T.tautological_flag_universal ι N (univFlag ι N) (isTaut_univFlag ι N) T g fl'
  exact ⟨g', w, h⟩

end GlobalTheory.FlagZ.Univ
