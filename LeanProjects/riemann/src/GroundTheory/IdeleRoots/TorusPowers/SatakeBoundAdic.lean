import Mathlib
import Formalism.UnipotentAdelicQuotients.ThmBInSatake
import GroundTheory.IdeleRoots.TorusPowers.SatakeBoundReps
import GroundTheory.GlobalFields.LocalFieldAtPlace
import GroundTheory.GlobalFields.KummerTheory.LocalIndexAtPlace
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.BlockD

namespace SatakeBound

open HeckeCharacterZeroLocus.ThmBIn IsDedekindDomain NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Spherical GLnLocal Iwasawa
  Finset Matrix
open scoped ValuativeRel

attribute [local instance] GroundTheory.Automorphic.Spherical.fintypeResidue

variable {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K))

theorem valued_uniformizer_eq :
    Valued.v (uniformizer (w.adicCompletion K) : w.adicCompletion K) = WithZero.exp (-1 : ℤ) := by
  have hS : (Valuation.integer (ValuativeRel.valuation (w.adicCompletion K))) =
      (w.adicCompletionIntegers K).toSubring := by
    ext x
    exact GroundTheory.Global.mem_valuationInteger_iff w x
  let e := RingEquiv.subringCongr hS
  have hirr : Irreducible (e (uniformizer (w.adicCompletion K))) :=
    (MulEquiv.irreducible_iff e).2 (irreducible_uniformizer _)
  have := GroundTheory.Global.valued_of_irreducible (v := w) (K := K)
    (ϖ := ⟨(e (uniformizer (w.adicCompletion K)) : w.adicCompletion K), (e _).2⟩) (by exact hirr)
  simpa [e] using this

theorem valued_le_one_of_mem {x : w.adicCompletion K} (hx : x ∈ 𝒪[w.adicCompletion K]) :
    Valued.v x ≤ 1 :=
  (HeightOneSpectrum.mem_adicCompletionIntegers (R := 𝓞 K) K w).1
    ((GroundTheory.Global.mem_valuationInteger_iff w x).1 hx)

theorem mem_of_valued_le_one {x : w.adicCompletion K} (hx : Valued.v x ≤ 1) :
    x ∈ 𝒪[w.adicCompletion K] :=
  (GroundTheory.Global.mem_valuationInteger_iff w x).2
    ((HeightOneSpectrum.mem_adicCompletionIntegers (R := 𝓞 K) K w).2 hx)

variable {w}

def diagU {n : ℕ} (a : (w.adicCompletion K)ˣ) (d : Fin n → ℤ) : GL (Fin n) (w.adicCompletion K) :=
  diagGL (w.adicCompletion K) n fun i => a ^ d i

end SatakeBound

end GroundTheory.BlockD
