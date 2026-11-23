import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CosetSumTransferAlongSurjectionPreimage
import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinIso
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RecProdRecSatakeLL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
import Formalism.SharpRestriction.LevelLetterCocycles.SphericalInertData
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnramifiedOfSphericalVectorDictionary
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertHeckeOperatorIndepOfInertDatum
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cosetSum_transfer_along_surjection_preimage : ∀ {G H V : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V] (U0 : Subgroup G) (K : Subgroup H) (T : Subgroup G) (ψ : T →* H), Function.Surjective ψ → (∀ t : T, ψ t ∈ K ↔ (t : G) ∈ U0) → ∀ (a φ' : H → ℂ) (β : G → V) (lam : V →ₗ[ℂ] ℂ), (∀ x, ∀ k ∈ K, a (x * k) = a x) → (Function.support fun d : H ⧸ K => a d.out).Finite → (∀ x, ∀ u ∈ U0, β (x * u) = β x) → (∀ t : T, φ' (ψ t) = lam (β t)) → ∑ᶠ d : H ⧸ K, a d.out * φ' d.out = lam (∑ᶠ c : G ⧸ U0, if hc : ∃ x : G, (x : G ⧸ U0) = c ∧ x ∈ T then a (ψ ⟨hc.choose, hc.choose_spec.2⟩) • β hc.choose else 0) := by
  first | exact @GlobalTheory.cosetSum_transfer_surj | exact GlobalTheory.cosetSum_transfer_surj | (intros; apply GlobalTheory.cosetSum_transfer_surj <;> assumption)
