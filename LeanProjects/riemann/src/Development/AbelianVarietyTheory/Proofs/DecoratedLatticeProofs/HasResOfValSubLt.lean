import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsIsComOfOf
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValDetSubOneLt
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms
open NumberField IsDedekindDomain Matrix MeasureTheory ValuativeRel GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.AdForm GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.BaseFn

open Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem.Col2.DetSpec

section Loc

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

variable [StarRing E] {n : ℕ}

variable {hc : Formalism.BasicNotions.CMData F E} {ST SG Q : Finset (HeightOneSpectrum (𝓞 E))}

theorem fn_eq {p : DecoF E n ST SG Q} {k : GL (Fin n) (AfE F E)} (h : IsPtOf hc k p) (hN : p.deco.1.N = Formalism.L2.Col.stdLat E n) (P : ST)
    (r : Fin n) (hr : r.1 + 1 = n) (c : 𝓞 E)
    (hrow : ∀ i, HasRes P.1 (adAt F P.1 ((k⁻¹ : GL (Fin n) (AfE F E)).1 r i)) (if i = r then Ideal.Quotient.mk P.1.asIdeal c else 0))
    (x : Fin n → 𝓞 E) : p.deco.1.f P (fun i => (x i : E)) = Ideal.Quotient.mk P.1.asIdeal (c * x r) := by
  refine HasRes.unique (h.f P _ (hN ▸ (Formalism.L2.Col.mem_stdLat _).2 fun i => ⟨x i, rfl⟩) r hr) ?_
  choose ρ hρ hv using hrow
  refine ⟨∑ i, ρ i * x i, ?_, ?_⟩
  · simp only [map_sum, map_mul, hρ, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  · simp only [Col2.pullV, Matrix.mulVec, dotProduct, map_sum, map_mul, adAt_inclE]
    rw [← Finset.sum_sub_distrib]
    refine Valuation.map_sum_lt _ one_ne_zero fun i _ => ?_
    show Valued.v (_ * algebraMap E (P.1.adicCompletion E) (algebraMap (𝓞 E) E (x i)) - _) < 1
    rw [← _root_.sub_mul, map_mul, valued_algebraMap]
    exact (mul_le_of_le_one_right' (P.1.valuation_le_one (x i))).trans_lt (hv i)

end Loc

end GlobalTheory.BaseFn

end
