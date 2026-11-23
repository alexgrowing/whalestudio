import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjugatePlacesCompletion
import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTypeGroupBlockLift
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodIdempotentFixesOfOnlySeriesOfLabelActs
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroInertia
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjGenTransportExists
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RankOneLocalComponentDetStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharLocalComponentExistsUniqueUnitaryStatement
import Formalism.LocalToGlobal.UnitaryNorms.CharTransport
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFixedIff
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.CuspRep GlobalTheory.SmGL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugate_places_completion : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {A A' : ValuationSubring Ω} {w w' : HeightOneSpectrum (𝓞 E)} (h : IsPlaceOver A w) (h' : IsPlaceOver A' w') (c : Ω ≃+* Ω) (j : E →+* E) (i : w.adicCompletion E ≃+* w'.adicCompletion E), (∀ z, c z ∈ A' ↔ z ∈ A) → (∀ x, c (algebraMap E Ω x) = algebraMap E Ω (j x)) → Continuous i → (∀ x, i (algebraMap E _ x) = algebraMap E _ (j x)) → ∀ {a : Weil h →* (w.adicCompletion E)ˣ} {ha : IsLocalArtin h a} {ε : EpsFamily A}, Laws a ha ε (ParLaws.locRec hL h) → ∀ {a' : Weil h' →* (w'.adicCompletion E)ˣ} {ha' : IsLocalArtin h' a'} {ε' : EpsFamily A'}, Laws a' ha' ε' (ParLaws.locRec hL h') → ∀ (ξ : (w'.adicCompletion E)ˣ →* ℂˣ), IsSmoothChar ξ → ∀ (σ : Weil h) (σ' : Weil h'), (∀ z, c ((σ : G E Ω) z) = (σ' : G E Ω) (c z)) → ξ (Units.map i.toRingHom.toMonoidHom (a σ)) = ξ (a' σ') := by
  first | exact @GlobalTheory.LocLanglands.artin_transport | exact GlobalTheory.LocLanglands.artin_transport | (intros; apply GlobalTheory.LocLanglands.artin_transport <;> assumption)
