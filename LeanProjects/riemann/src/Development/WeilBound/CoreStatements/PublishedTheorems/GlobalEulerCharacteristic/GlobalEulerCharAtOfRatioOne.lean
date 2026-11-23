import Development.WeilBound.CoreStatements.PublishedTheorems.GlobalEulerCharacteristic.Narrow
import Development.WeilBound.CoreStatements.PublishedTheorems.GlobalEulerCharacteristic.RatioOneKilled
import Development.WeilBound.CoreStatements.PublishedTheorems.GlobalFiniteness.Transport
import Development.WeilBound.CoreStatements.PublishedTheorems.GlobalEulerCharacteristic.WorkDictfwdA

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh GroundTheory.Global ReciprocityTheory.Gal Formalism.ConjugateSelfDual

namespace PositivityTheory.Lit1.GEN

theorem globalEulerCharAt_of_ratioOne {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] {r : ℕ} {M : Type} [AddCommGroup M]
    [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M]
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (rhoS : Representation (ZMod (l ^ r)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M)
    (h : RatioOne l (fun _ => True)) : GlobalEulerCharAt S rhoS :=
  W_dictfwd_a.globalEulerCharAt_of_ratioOne S rhoS h

end PositivityTheory.Lit1.GEN
