import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameBoundSpaces.FrameBound

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT

namespace PositivityTheory.Rg.BcB.F.Small

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem countable_pl (E : Type) [Field E] [NumberField E] : Countable (HeightOneSpectrum (𝓞 E)) := by
  classical
  have hinj : Function.Injective fun v : HeightOneSpectrum (𝓞 E) => v.asIdeal :=
    fun v v' h => HeightOneSpectrum.ext h
  haveI : Countable (𝓞 E) := (RingOfIntegers.basis E).equivFun.injective.countable
  haveI : Countable (Ideal (𝓞 E)) :=
    Function.Injective.countable (f := fun I : Ideal (𝓞 E) => (IsNoetherian.noetherian I).choose)
      (fun I J h => by
        rw [← (IsNoetherian.noetherian I).choose_spec, ← (IsNoetherian.noetherian J).choose_spec]
        simp only at h
        rw [h])
  exact hinj.countable

end PositivityTheory.Rg.BcB.F.Small

end
