import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ShortLatticeUnitarize.CompactBoxLattices.CentChar
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.ExistsContRep

open NumberField UpperTheory.V UpperTheory.V.TR
open private main sc_comm fin_sc from Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ShortLatticeUnitarize.CompactBoxLattices.CentChar

theorem UpperTheory.V.Af.Rn.centChar : UpperTheory.V.Sd.Wc.CentChar := by
  intro F _ _ _ π
  obtain ⟨ω, hω⟩ := main UpperTheory.V.Af.admissibleReal π
  refine ⟨ω, fun z φ hφ g => ?_, fun z x => Subtype.ext ?_⟩
  · exact (congrArg φ.1 (sc_comm z g)).symm.trans (congrArg (fun ψ : Sm F 2 => ψ.1 g) (hω z φ hφ))
  · have := hω (GlobalTheory.CuspRep.finId F z) x.1 x.2
    rw [← fin_sc] at this
    exact this
