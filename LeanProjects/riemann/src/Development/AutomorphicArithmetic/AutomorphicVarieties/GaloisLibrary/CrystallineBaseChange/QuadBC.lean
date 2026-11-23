import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.NormQuad
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.SelfIso
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.WeakEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.SplitOf

open NumberField UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published

theorem UpperTheory.V.Br.quadBCw_of_cyclic (hN : GlobalTheory.Mem.LiteralAutomorphy.LitN) (smo : StrongMultOneReal) (cyc : CyclicBaseChange) (hC : ExC) (hR : ExR) :
    UpperTheory.V.Br.QuadBCw := by
  intro F E _ _ _ _ _ _ _ h2 a _ ha π _
  rcases Br.weakEx cyc F E h2 a ha π with ⟨η, hη, ht⟩ | ⟨P, hP⟩
  · exact Or.inl ⟨η, Br.normQuad hN.aut.art F E h2 η hη, Br.selfIso smo F a ha π η (h2 ▸ hη.2.1) ht⟩
  · refine Or.inr ⟨P, hP, fun hreg ⟨χ, hχ⟩ => ?_⟩
    haveI : Algebra.IsQuadraticExtension F E := { finrank_eq_two' := h2 }
    haveI : IsCMField E := IsCMField.ofCMExtension F E
    exact Br.splitOf hN hC hR F E h2 a ha π χ P hreg hχ hP
