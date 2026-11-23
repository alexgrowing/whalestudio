import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.SplitPlaceTypes
import Development.AbelianVarietyTheory.Counterexamples.NonGaloisSurvey.SplitRowIffOfIsEmpty
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinrankMaxUnramifiedSubfieldPadicFinExtPos
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SqrtNegPrimeMemKur

open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.FrobeniusOrbits GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceTypes

namespace GlobalTheory.HubLoc

theorem localField_unramified : ∀ (D : D7) (i : D.nd.Loc), D.nd.l i ∉ D.host.small → D.nd.l i ≠ D.host.q → D.nd.l i ≠ D.host.d → ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)), Loc.K0 (D.nbr i w hw).Kw = (D.nbr i w hw).Kw.1 ∧ (D.nbr i w hw).Kw.1 ≤ Loc.Ks (D.nbr i w hw).Kw 1 ∧ Loc.Good (D.nbr i w hw).Kw 1 (D.nbr i w hw).LL := by
  intro D i hs hq hd w hw
  have h2 : D.nd.l i ≠ 2 := fun e => hs (e ▸ D.host.toHostRaw.two_mem_small)
  have hN : ¬ D.nd.l i ∣ D.host.condN := fun h => by
    rcases (D.host.toHostRaw.dvd_condN_iff_small (Fact.out : (D.nd.l i).Prime)).1 h with h | h | h
    exacts [hs h, hq h, hd h]
  have hK := kw_le_Kur_of_ne i hN w hw
  have h1 := le_Ks_one_of_Kur _ hK
  exact ⟨inf_eq_left.2 hK, h1, (D.self_good i w hw).good_one (D.nbr i w hw).LL_split h2 h1⟩

end GlobalTheory.HubLoc
