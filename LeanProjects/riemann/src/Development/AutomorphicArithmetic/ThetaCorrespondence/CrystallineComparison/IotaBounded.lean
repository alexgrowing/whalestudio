import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.Comparison
import GroundTheory.PAdicHodge.ACrisBdRGalois

noncomputable section

namespace Formalism.BasicNotions.CmpTie.Incl

open GroundTheory.PAdicHodge

variable (l : ℕ) [Fact l.Prime]

abbrev NC : Type := ↥(normInteger ℂ_[l])

def iotaF : ACris.ACris ℂ_[l] l →+* Reformulated.AutPerF.BdRPlus l (NC l) := ACris.iota ℂ_[l] l

theorem iota_bounded (n : ℕ) : ∃ N : ℕ, ∀ x : ACris.ACris ℂ_[l] l, ∃ a : Reformulated.AutPerF.Ainf l (NC l),
    Reformulated.AutPerF.BdRPlus.eval l (NC l) n (((l : ℕ) : Reformulated.AutPerF.BdRPlus l (NC l)) ^ N * iotaF l x) =
      Ideal.Quotient.mk _ (algebraMap (Reformulated.AutPerF.Ainf l (NC l)) (Reformulated.AutPerF.AinfInv l (NC l)) a) := by
  refine ⟨(n - 1).factorial.factorization l, fun x => ?_⟩
  obtain ⟨w, hw⟩ := ACris.pow_mul_mem_latticeQ n _ (ACris.embedding₂ ℂ_[l] l n x).2
  refine ⟨w, ?_⟩
  have h1 : Reformulated.AutPerF.BdRPlus.eval l (NC l) n (iotaF l x) =
      ((ACris.embedding₂ ℂ_[l] l n x : ACris.acrisQ ℂ_[l] l n) : Localization.Away ((l : ℕ) : AInf ℂ_[l] l) ⧸ ACris.kerAway ℂ_[l] l ^ n) := by
    have := ACris.evalₐ_iota (K := ℂ_[l]) (p := l) n x
    rw [ACris.iotaQ.eq_1] at this
    exact this
  rw [map_mul, map_pow, map_natCast, h1]
  exact hw.symm

end Formalism.BasicNotions.CmpTie.Incl
