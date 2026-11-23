import Mathlib
import Formalism.LocalToGlobal.KernelLattices.ThDistC
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.IndexExponentDegree
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EmbHInjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemDivsOfMem
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnderEqOfMapEq

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions Formalism.L2.Th1.H GlobalTheory.ThetaMove GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree

namespace GlobalTheory.ThetaMove

theorem split_of_conj_ne₂ : ∀ (X : Fields) (P : HeightOneSpectrum (𝓞 X.E)) (v : HeightOneSpectrum (𝓞 X.F)),
    X.Ok → conjPrime₂ P ≠ P → P.asIdeal.under (𝓞 X.F) = v.asIdeal →
    Ideal.map (algebraMap (𝓞 X.F) (𝓞 X.E)) v.asIdeal = P.asIdeal * (conjPrime₂ P).asIdeal ∧
    ∀ Q : HeightOneSpectrum (𝓞 X.E), Q.asIdeal.under (𝓞 X.F) = v.asIdeal ↔ (Q = P ∨ Q = conjPrime₂ P) := by
  intro X P v hX hP hv
  obtain rfl : P.under (𝓞 X.F) = v := HeightOneSpectrum.ext hv
  have key := GlobalTheory.MuConj.mem_above_iff hX.star_F hX.rankE P hP
  refine ⟨GlobalTheory.Mem.GoodPlace.map_eq_mul hX.rankE hP.symm ((key _).2 (Or.inr rfl)), fun Q => ?_⟩
  rw [← key Q]
  exact ⟨fun h => HeightOneSpectrum.ext h, fun h => congrArg HeightOneSpectrum.asIdeal h⟩

end GlobalTheory.ThetaMove
