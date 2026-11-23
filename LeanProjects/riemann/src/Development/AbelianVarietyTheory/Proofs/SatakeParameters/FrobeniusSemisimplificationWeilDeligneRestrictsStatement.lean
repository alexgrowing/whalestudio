import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FrobeniusSemisimplificationWeilDeligneRestricts
import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RestrictsSelf
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CharpolyEqOfIsNilpotentSub
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormVZpowDegEq
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsWeilGroupRestrictExtensionStatement
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobeniusSemisimplification_weilDeligne_restricts : ∀ (K L Ω : Type) [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω] [Field L] [NumberField L] [Algebra L Ω] [IsAlgClosure L Ω] [Algebra K L] [IsScalarTower K L Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K)) (v' : HeightOneSpectrum (𝓞 L)) (h : IsPlaceOver A v) (h' : IsPlaceOver A v') (X Y : Type) [AddCommGroup X] [Module ℂ X] [FiniteDimensional ℂ X] [AddCommGroup Y] [Module ℂ Y] [FiniteDimensional ℂ Y] (ρ : Representation ℂ (Weil h) X) (N : Module.End ℂ X) (a : WDRep h X) (ρ' : Representation ℂ (Weil h') Y) (N' : Module.End ℂ Y) (b : WDRep h' Y), IsSmooth ρ → IsSmooth ρ' → IsFrobSS ⇑ρ N a → IsFrobSS ⇑ρ' N' b → ∀ e : X ≃ₗ[ℂ] Y, (∀ (σ : Weil h) (σ' : Weil h'), (∀ z : Ω, (σ : G K Ω) z = (σ' : G L Ω) z) → ∀ x, e (ρ σ x) = ρ' σ' (e x)) → (∀ x, e (N x) = N' (e x)) → Restricts (WD.mk a) (WD.mk b) := by
  first | exact @GlobalTheory.AboveL.restricts_of_isFrobSS | exact GlobalTheory.AboveL.restricts_of_isFrobSS | (intros; apply GlobalTheory.AboveL.restricts_of_isFrobSS <;> assumption)
