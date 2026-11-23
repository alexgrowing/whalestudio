import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimeOverTypePrimeFixedPlaceOrConj
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RunModel

open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares GlobalTheory.ShareOn

attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prime_over_typePrime_fixedPlace_or_conj : ∀ (D : D7) (k : Fin 2) (P : Ideal (𝓞 D.host.E)), P.IsPrime → ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ P →
    ∃ v : D.nd.PlG k, P = (D.naut.plGw k v).asIdeal ∨
      P = (D.naut.plGw k v).asIdeal.map
        ((RingOfIntegers.mapRingEquiv (IsCMField.complexConj D.host.E).toRingEquiv : 𝓞 D.host.E ≃+* 𝓞 D.host.E) :
          𝓞 D.host.E →+* 𝓞 D.host.E) := by
  first | exact @GlobalTheory.TypePrimesOnto.prime_eq_plGw_or_conj | exact GlobalTheory.TypePrimesOnto.prime_eq_plGw_or_conj | (intros; apply GlobalTheory.TypePrimesOnto.prime_eq_plGw_or_conj <;> assumption)
