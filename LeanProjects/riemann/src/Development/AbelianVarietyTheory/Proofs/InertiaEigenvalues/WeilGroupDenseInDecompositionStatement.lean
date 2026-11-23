import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilGroupDenseInDecomposition
import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharZeroAdicCompletion
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DecompositionGroupLocalGaloisIso
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import GroundTheory.LocalFields.ConductorReciprocity
import GroundTheory.LocalFields.LubinTateReciprocity
open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict GroundTheory.LocalField GroundTheory.LocalField.FormalGroup
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_group_dense_in_decomposition : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (ι : Ω →ₐ[E] Kbar w),
    IsLocEmb A w ι → ∀ (g : Dec (F := E) A) (τ : GalLoc w), Lifts ι τ (g : G E Ω) →
    ∀ (U : Subgroup (GalLoc w)), IsOpen (U : Set (GalLoc w)) → ∀ (V : Set (Dec (F := E) A)), IsOpen V → g ∈ V →
    ∃ (σ : Weil h) (τ' : GalLoc w), Lifts ι τ' (σ : G E Ω) ∧ τ⁻¹ * τ' ∈ U ∧
      (⟨σ, Weil_le_Dec h σ.2⟩ : Dec (F := E) A) ∈ V := by
  first | exact @GlobalTheory.WeilDense.weil_dense | exact GlobalTheory.WeilDense.weil_dense | (intros; apply GlobalTheory.WeilDense.weil_dense <;> assumption)
