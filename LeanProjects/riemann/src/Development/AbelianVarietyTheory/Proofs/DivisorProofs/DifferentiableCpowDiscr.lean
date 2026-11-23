import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeRatioPosOfPublished
import GroundTheory.GlobalFields.TateThesis.DedekindContinuation

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.LFun GlobalTheory.HeckeOne Filter Topology
open Formalism.L2.Host (aboveF)
open Formalism.MainNotions.SchurIrreducible (IsSplit IsUnram)
open GroundTheory.Global Complex

namespace GlobalTheory.EtaEven

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem sum_ef (v : HeightOneSpectrum (𝓞 F)) :
    ∑ w ∈ aboveF (L := E) F v, w.asIdeal.ramificationIdx (𝓞 F) * w.asIdeal.inertiaDeg (𝓞 F) =
      Module.finrank F E := by
  have := v.isPrime
  have := v.isMaximal
  have hfin : Fintype (v.asIdeal.primesOver (𝓞 E)) := (IsDedekindDomain.primesOver_finite v.asIdeal (𝓞 E)).fintype
  have h := Ideal.sum_ramification_inertia_eq_finrank v.asIdeal (𝓞 E)
  rw [← Algebra.IsAlgebraic.finrank_of_isFractionRing (𝓞 F) F (𝓞 E) E] at h
  rw [← h]
  refine Finset.sum_bij (fun w hw => ⟨w.asIdeal, w.isPrime, ⟨by rw [← mem_aboveF.1 hw]; rfl⟩⟩)
    (fun _ _ => Finset.mem_univ _) (fun a _ b _ e => HeightOneSpectrum.ext (congrArg Subtype.val e)) ?_
    (fun _ _ => rfl)
  rintro ⟨q, hq, hq'⟩ -
  refine ⟨⟨q, hq, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot q⟩, mem_aboveF.2 (HeightOneSpectrum.ext hq'.over.symm), rfl⟩

end GlobalTheory.EtaEven

end
