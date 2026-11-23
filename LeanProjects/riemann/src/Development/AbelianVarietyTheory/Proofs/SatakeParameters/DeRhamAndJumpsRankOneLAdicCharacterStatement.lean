import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DeRhamAndJumpsRankOneLAdicCharacter
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.WdOfMono0L
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CharAbove
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalWdSpace
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.TripleGal GlobalTheory.Pst
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.deRham_jumps_of_continuous_lAdic_char : ∀ (D : D7) (T : WDTie D.nd D.naut) (W : WDSide D T) (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (μ : G D.host.E D.nd.Om →* (Qbar l)ˣ), Continuous μ → ∀ (J : (D.host.E →+* Qbar l) → Multiset ℤ) (w : HeightOneSpectrum (𝓞 D.host.E)), w ∈ placesOver D.host.E l → (∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l D.host.E D.nd.Om (Dec (F := D.host.E) (D.nd.plOm.1 w)) O), Induces Bw → IsdRAt (D.loc l) Bw ((rk1 μ).comp (Dec (F := D.host.E) (D.nd.plOm.1 w)).subtype) ∧ ∀ (τ : D.host.E →+* Qbar l) (LL' : FinExt l) (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1), IsInduced Bw τ τ' → IsJumpsAt (D.loc l) Bw ((rk1 μ).comp (Dec (F := D.host.E) (D.nd.plOm.1 w)).subtype) τ (J τ)) → W.IsdRW l ι (rk1 μ) w ∧ ∀ τ : D.host.E →+* Qbar l, (∀ x : 𝓞 D.host.E, ‖τ (x : D.host.E)‖ < 1 ↔ x ∈ w.asIdeal) → W.jumpsW l ι (rk1 μ) τ = J τ := by
  first | exact @GlobalTheory.CharAboveRead.deRham_and_jumps_rankOne_lAdic_character | exact GlobalTheory.CharAboveRead.deRham_and_jumps_rankOne_lAdic_character | (intros; apply GlobalTheory.CharAboveRead.deRham_and_jumps_rankOne_lAdic_character <;> assumption)
