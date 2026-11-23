import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsAbelianTotallyRealExtPrescribedCompletion
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RegPolOfRepOf
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.ArthurClozel
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_abelian_totallyReal_ext_prescribedCompletion : ∀ (Ω : Type) [Field Ω] (F : Type) [Field F] [NumberField F] [Algebra F Ω] [IsAlgClosure F Ω] [IsTotallyReal F] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)) (h : IsPlaceOver A v) (V : Subgroup (Dec (F := F) A)), IsOpen (V : Set (Dec (F := F) A)) → commutator (Dec (F := F) A) ≤ V → ∀ T : Finset (HeightOneSpectrum (𝓞 F)), v ∉ T → ∃ F₁ : IntermediateField F Ω, FiniteDimensional F F₁ ∧ IsAbelianGalois F F₁ ∧ (∀ φ : F₁ →+* ℂ, ComplexEmbedding.IsReal φ) ∧ (∀ g : Dec (F := F) A, (g : G F Ω) ∈ F₁.fixingSubgroup ↔ g ∈ V) ∧ ∀ u ∈ T, ∀ A' : ValuationSubring Ω, IsPlaceOver A' u → Dec (F := F) A' ≤ F₁.fixingSubgroup := by
  first | exact @GlobalTheory.AbStep.exists_abelian_real_field | exact GlobalTheory.AbStep.exists_abelian_real_field | (intros; apply GlobalTheory.AbStep.exists_abelian_real_field <;> assumption)
