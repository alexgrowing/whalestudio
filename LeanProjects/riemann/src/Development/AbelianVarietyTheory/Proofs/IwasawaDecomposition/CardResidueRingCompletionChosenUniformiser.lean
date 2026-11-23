import Mathlib
import Formalism.LocalToGlobal.Divisibility.QLocTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.HostPins
import Formalism.DoubleCosetMeasures.LatticeCoset
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HaarModulusProductFormulaTotallyReal
open MeasureTheory Matrix NumberField IsDedekindDomain Formalism.BasicNotions Formalism.DoubleCosetMeasures Formalism.L2.Host Formalism.L2.DIV Formalism.L2.DIV.QLoc GlobalTheory.Mem.HD

namespace GlobalTheory.ResidueCardUnif

theorem card_kF_piP : ∀ (L : Type) [Field L] [NumberField L] (P : HeightOneSpectrum (𝓞 L)) (h : ((piP P : (P.adicCompletion L)ˣ) : P.adicCompletion L) ∈ OP P), Nat.card (kF (OP P) ((piP P : (P.adicCompletion L)ˣ) : P.adicCompletion L) h) = qP P := by
  intro L _ _ P h
  have ha : Valued.v ((piP P : (P.adicCompletion L)ˣ) : P.adicCompletion L) = WithZero.exp (-1 : ℤ) :=
    unif_spec P
  have h1 : ((piP P : (P.adicCompletion L)ˣ) : P.adicCompletion L) ∈ P.adicCompletionIntegers L := h
  have e : IsLocalRing.maximalIdeal (P.adicCompletionIntegers L) = Ideal.span {⟨_, h1⟩} := by
    ext y
    rw [GlobalTheory.CNorm.mem_span_singleton_adicCompletionIntegers P
      (by rw [ha]; exact WithZero.exp_ne_zero)]
    rw [ha, ← GlobalTheory.HaarLatticeScale.lt_one_iff_le_exp]
    exact Valuation.mem_maximalIdeal_iff _ _
  have c := GlobalTheory.GaugeProdFormula.card_residue L P
  rw [IsLocalRing.ResidueField, e] at c
  exact c

end GlobalTheory.ResidueCardUnif
