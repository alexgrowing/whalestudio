import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.LocalGramMatrixCorankOne
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.OmVBadTOfRestX

noncomputable section

namespace PI.OmVg

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocVol Formalism.L2.SG.TypedSets Formalism.L2.SG.Sub Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  NumberField IsDedekindDomain PI.OmLocU PI.OmVd Formalism.L2.SG.Pf.NcVal.OmVSt

variable {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ)

theorem redP_holds : ∀ v : PlX X, ((Tw u' : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal →
    RedP X.B.I.cm.sig X.B.I.J ψ v (abelian₂ X) (D.R.rS + 1 + D.R.rS) (yTup X u' v) := fun v hv =>
  redP_of_gramCor X.B.I.cm.sig X.B.I.J ψ v (abelian₂ X) _ _ (fun ϖ hϖ => by
    rw [OmW.omVGram_holds X u' v]
    exact local_gram_matrix_corank_one X u' v hv hϖ)

theorem omVBadT_of_ff (hStd : OmVStd X ψ) (hLat : OmVLat X) (hGram : OmVGram X u')
    (hFI : FFInertB) (hFS : FFSplitB) : OmVBadT X u' ψ :=
  PI.OmVf.omVBadT_of_rest X u' ψ hStd hLat hGram (redP_holds X u' ψ) hFI hFS

theorem omVBadT_of_ffX (hStd : Formalism.L2.SG.Pf.NcX.OmVSt.OmVStd X ψ) (hLat : Formalism.L2.SG.Pf.NcX.OmVSt.OmVLat X)
    (hGram : Formalism.L2.SG.Pf.NcX.OmVSt.OmVGram X u') (hFI : FFInertB) (hFS : FFSplitB) :
    Formalism.L2.SG.Pf.NcX.OmVSt.OmVBadT X u' ψ :=
  PI.OmVf.omVBadT_of_restX X u' ψ hStd hLat hGram (redP_holds X u' ψ) hFI hFS

end PI.OmVg
