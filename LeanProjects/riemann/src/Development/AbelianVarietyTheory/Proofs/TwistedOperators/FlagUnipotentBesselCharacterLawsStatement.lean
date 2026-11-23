import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentBesselCharacterLaws
import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.MixModel GlobalTheory.MixPer
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_unipotent_bessel_character_laws : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ (S S₀ A L : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (o : OrthDec S₀ A L) (ζ : Fin L.rank → D.host.E) (θ : D.host.E), (∀ z, Continuous (psiBes ψ d θ z)) ∧ (∀ z, ∀ γ ∈ GQ S, psiBes ψ d θ z γ = 1) ∧ (∀ n h, psiBes ψ d θ (vecB o ζ) (embA d o h * n * (embA d o h)⁻¹) = psiBes ψ d θ (vecB o ζ) n) ∧ (∀ n h, psiFlag ψ d (d.emb0 h * n * (d.emb0 h)⁻¹) = psiFlag ψ d n) ∧ (∀ g, g ∈ besGrp d o ↔ ∃ n ∈ flagN d, ∃ h, g = n * embA d o h) ∧ ∀ ι : A.V →ₗ[D.host.E] S.V, frameMat S A ι = d.i₀ * o.iA → ∀ h, EmbRel S A ι (embA d o h) h := by
  first | exact @GlobalTheory.MixPer.charLaws | exact GlobalTheory.MixPer.charLaws | (intros; apply GlobalTheory.MixPer.charLaws <;> assumption)
