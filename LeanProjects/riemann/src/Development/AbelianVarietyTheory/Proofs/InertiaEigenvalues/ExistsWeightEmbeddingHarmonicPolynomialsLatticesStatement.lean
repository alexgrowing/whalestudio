import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWeightEmbeddingHarmonicPolynomialsLattices
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoFormsOff
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SubsetTwistExceptionalPlaces
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrameEquivApply
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleTwistOfTwistingCharacter
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.StandardLattice Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
open Formalism.MainNotions.IntegralHeckeForms (TwOK)
open Formalism.AUTREP (GAf)
open GlobalTheory.FormInner (frameEquiv)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MtRead
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_weightEmbedding_harmonicPolynomials_lattices : ∀ (D : D7) (S T : HSp D) (B : GlobalTheory.ExportSeries.Base S T), B.Good → ∀ (n : ℕ) (hF : D.host.F = maximalRealSubfield D.host.E) (P : principalLevelFrame.RowPsi S n), IdFrame hF P → ∀ (hn : S.rank = n) (K₀ : Type) [Field K₀] (R : Type) [CommRing R] [IsDomain R] (e : FractionRing R →+* ℂ) (f : K₀ →+* FractionRing R) (s : ↥D.LL0 →+* K₀), (∀ x, e (f (s x)) = embLL0 D x) → IsCoefRing (embLL0 D) (labLL0 D) (e.comp (algebraMap R (FractionRing R))).range → ∀ (W₀ : Type) [AddCommGroup W₀] [Module K₀ W₀] (ρ₀ : Representation K₀ (ReciprocityTheory.Aut.GQ D.host.E n) W₀) (lam : D.what₂.Tau → DomWeight n), (∀ τ a, (lam τ).w (Fin.cast hn a) = (B.w.lam τ).w a) → ∀ T₀ : W₀ ≃ₗ[K₀] VV K₀ lam, (∀ (γ : ReciprocityTheory.Aut.GQ D.host.E n) (γ₀ : GL (Fin n) D.host.E), (((γ : GAf D.host.E n) : GL (Fin n) (ReciprocityTheory.Aut.AL D.host.E)) : Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL D.host.E)) = (γ₀ : Matrix (Fin n) (Fin n) D.host.E).map Algebra.TensorProduct.includeLeftRingHom → ∀ x, T₀ (ρ₀ γ x) = rhoVr (fun τ => s.comp (labLL0 D τ)) lam γ₀ (T₀ x)) → ∀ (W : Type) [AddCommGroup W] [Module (FractionRing R) W] (ρ : Representation (FractionRing R) (ReciprocityTheory.Aut.GQ D.host.E n) W), (∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (b₀ : Module.Basis ι K₀ W₀) (b₁ : Module.Basis ι (FractionRing R) W), ∀ γ : ReciprocityTheory.Aut.GQ D.host.E n, LinearMap.toMatrix b₁ b₁ (ρ γ) = (LinearMap.toMatrix b₀ b₀ (ρ₀ γ)).map f) → ∃ ω : W →ₛₗ[e] PolF D T.rank S.rank, WtMap B (frameEquiv P) R e ρ ω := by
  first | exact @GlobalTheory.MtRead.WtEmb.exists_wtMap | exact GlobalTheory.MtRead.WtEmb.exists_wtMap | (intros; apply GlobalTheory.MtRead.WtEmb.exists_wtMap <;> assumption)
