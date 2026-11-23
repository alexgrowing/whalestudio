import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjSelfDualHeckeCharConjugatePlaceComponentInv
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
theorem _root_.GlobalTheory.T.conjSelfDual_heckeChar_conjugatePlace_component_inv : ∀ {R : Ranks} (Hs : Host R) (μ : HChar Hs.E), IsCSD Hs μ → ∀ (w w' : HeightOneSpectrum (𝓞 Hs.E)), IsConjPl Hs w w' → ∃ i : w.adicCompletion Hs.E ≃+* w'.adicCompletion Hs.E, Continuous i ∧ (∀ x, i (algebraMap Hs.E _ x) = algebraMap Hs.E _ (Hs.conj x)) ∧ ∀ x, μ.loc w' (Units.map i.toRingHom.toMonoidHom x) = (μ.loc w x)⁻¹ := by
  first | exact @GlobalTheory.ConjLocCsd.main | exact GlobalTheory.ConjLocCsd.main | (intros; apply GlobalTheory.ConjLocCsd.main <;> assumption)
