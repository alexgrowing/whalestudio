import Formalism.LocalToGlobal.Columns.ChainOneOk
import Formalism.LocalToGlobal.Columns.OneCosetSymmetricAndNonvanishing
import Formalism.LocalToGlobal.Columns.BlockTriangularMulVecMemPartialFlag
import Formalism.LocalToGlobal.Columns.ReducedMatrixExtensionEntry
import Formalism.LocalToGlobal.Columns.FrameEntryAuxiliarySuperdiagonal
import Formalism.LocalToGlobal.Columns.ColumnsProofs.SymLevEnt

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section Closed

variable {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m}
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ)

theorem oneIdx_ok_closed (hX : X.Ok) (hPr : Pr.Ok) (hCh : Ch.Ok) (h4 : ∀ w ∈ Pr.vGs, qOf w % 4 = 1) (G : ChGlob X R.m)
    {e : Fin R.m → X.Tau → ℚ} {eta : Formalism.L2.Host.HChar X.E} (hT : Ch.Tied G.σ₀ e G.mu0 eta) (hW : Ch.WeilTied G.σ₀ G.xi0)
    (hval : ∀ (j : Fin R.m) (w : HeightOneSpectrum (𝓞 X.E)), w ∈ Pr.vGs →
      ∃ y : X.K, G.σ₀ y = ((((G.mu0 j).locK w (ciQU w)) : ℂˣ) : ℂ)⁻¹)
    {m2 : ℕ} (hm : R.m = m2 + 2) :
    (oneIdx (colLevSym Ch) (QE sel ((mu0 X.F X.E X.K S : Tup X.F X.E X.K S) : Chr X.F X.E X.K)) m2).Ok Ch sel (mu0 X.F X.E X.K S)
      (ookCstR Ch sel S G) G m2 := by
  have hB := ookCstR_base sel S hX hPr hCh h4 G hm
  have hJ := oneCosetSymmetric_and_nonvanishing G.σ₀ hB (ciMemG sel S) (liftFromResidueParabolicProduct_holds Ch sel _ _ m2) (ocbGrpGLoc_holds Ch sel _ _ m2)
    (ocbChrGLoc_holds Ch sel _ _ m2) (closedLevels_by_entries_holds X Pr R Ch m2 hm)
  exact oneIdx_ok sel S hX hPr hCh h4 G hT hW hval hm hJ.1 hJ.2

end Closed

end Formalism.L2.Col
