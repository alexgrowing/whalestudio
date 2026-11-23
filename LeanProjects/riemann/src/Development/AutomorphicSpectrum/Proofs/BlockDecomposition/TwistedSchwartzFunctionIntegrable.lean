import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaPartD
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoundUnitary
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermInf
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRing
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ContinuousIntegrableOfIsSchwartzBruhat
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Phase

def flat (S : Type) [AddCommGroup S] [TopologicalSpace S] (n M : ℕ) :
    (Fin n → Fin M → S) ≃ₜ+ (Fin 1 → Fin (n * M) → S) where
  toFun X _ p := X (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm p).2
  invFun Y a i := Y 0 (finProdFinEquiv (a, i))
  left_inv X := by
    funext a i
    simp
  right_inv Y := by
    funext a p
    rw [Subsingleton.elim a 0]
    exact congrArg (Y 0) (finProdFinEquiv.apply_symm_apply p)
  map_add' X Y := by
    funext a p
    rfl
  continuous_toFun := continuous_pi fun _ => continuous_pi fun p =>
    (continuous_apply _).comp (continuous_apply _)
  continuous_invFun := continuous_pi fun _ => continuous_pi fun _ =>
    (continuous_apply _).comp (continuous_apply _)

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

theorem projInf_flat_symm {n M : ℕ} (Y : Fin 1 → Fin (n * M) → AF F ⊗[F] E) :
    projInf ((flat _ n M).symm Y) = (flat _ n M).symm (projInf Y) := rfl

theorem projFin_flat_symm {n M : ℕ} (Y : Fin 1 → Fin (n * M) → AF F ⊗[F] E) :
    projFin ((flat _ n M).symm Y) = (flat _ n M).symm (projFin Y) := rfl

theorem isSchwartzBruhat_flat {n M : ℕ} {Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ}
    (hΦ : GlobalTheory.Published.SiegelOneVector.IsSchwartzBruhat Φ) :
    GlobalTheory.Published.SiegelOneVector.IsSchwartzBruhat (Φ ∘ (flat _ n M).symm) := by
  obtain ⟨k, P, Q, hP, hQ, hs⟩ := hΦ
  refine ⟨k, fun i => P i ∘ (flat _ n M).symm, fun i => Q i ∘ (flat _ n M).symm, fun i => ?_,
    fun i => ⟨(hQ i).1.comp_continuous (flat _ n M).symm.continuous,
      (hQ i).2.comp_homeomorph (flat _ n M).symm.toHomeomorph⟩, fun Y => ?_⟩
  · obtain ⟨N, e, c1, c2, f, hf⟩ := hP i
    refine ⟨N, (flat (Ainf F ⊗[F] E) n M).symm.toAddEquiv.trans e, c1.comp (flat _ n M).symm.continuous,
      (flat _ n M).continuous.comp c2, f, fun X => ?_⟩
    exact hf _
  · simp only [Function.comp_apply, hs, projInf_flat_symm, projFin_flat_symm]

theorem continuous_integrable [NumberField E] (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) {n M : ℕ}
    (dx : Measure (Fin n → Fin M → AF F ⊗[F] E)) (hdx : dx.IsAddHaarMeasure)
    {Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ} (hΦ : GlobalTheory.Published.SiegelOneVector.IsSchwartzBruhat Φ) :
    Continuous Φ ∧ Integrable Φ dx := by
  obtain ⟨h1, -, -, -, -, -, -, hBor, -, -⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hCM (AF F)
  haveI := h1
  haveI := hBor n M
  haveI := hBor 1 (n * M)
  let e := flat (AF F ⊗[F] E) n M
  haveI : (dx.map e).IsAddHaarMeasure :=
    Measure.isAddHaarMeasure_map _ e.toAddEquiv.toAddMonoidHom e.continuous e.surjective
      e.toHomeomorph.isClosedEmbedding.tendsto_cocompact
  obtain ⟨c, hi⟩ := GlobalTheory.CompanionTheory.Hypotheses₂.OneV.PoiInt.continuous_integrable_of_isSchwartzBruhat F E σ hCM (n * M)
    (dx.map e) inferInstance _ (isSchwartzBruhat_flat hΦ)
  have hcomp : (Φ ∘ e.symm) ∘ e = Φ := by
    funext X
    simp
  refine ⟨hcomp ▸ c.comp e.continuous, ?_⟩
  have := (e.toHomeomorph.measurableEmbedding.integrable_map_iff).1 hi
  rwa [show (Φ ∘ (flat _ n M).symm) ∘ e.toHomeomorph = Φ from hcomp] at this

theorem integrable_mul_phase : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
  IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (n : ℕ) (ψ : AddChar (AF F) ℂ), IsCharAF F ψ →
  ∀ dx : Measure (Fin n → Fin M → AF F ⊗[F] E), dx.IsAddHaarMeasure →
  ∀ Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ, GlobalTheory.Published.SiegelOneVector.IsSchwartzBruhat Φ →
  ∀ b : HermR (AF F) σ n, Integrable (fun X => Φ X * ψ (algebraMap F (AF F) (1 / 2) * Algebra.trace (AF F) (AF F ⊗[F] E)
      (Matrix.trace ((b : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) * gramR (AF F) σ J X)))) dx := by
  intro F E _ _ _ _ _ σ hCM M J n ψ hψ dx hdx Φ hΦ b
  obtain ⟨h1, -, -, -, -, htr, -, hBor, -, hgram⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hCM (AF F)
  haveI := h1
  haveI := hBor n M
  obtain ⟨hc, hi⟩ := continuous_integrable σ hCM dx hdx hΦ
  have hph : Continuous fun X : Fin n → Fin M → AF F ⊗[F] E =>
      ψ (algebraMap F (AF F) (1 / 2) * Algebra.trace (AF F) (AF F ⊗[F] E)
        (Matrix.trace ((b : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) * gramR (AF F) σ J X))) := by
    refine hψ.1.comp (continuous_const.mul (htr.comp ?_))
    exact (continuous_const.matrix_mul (hgram n M J)).matrix_trace
  refine hi.mono (hc.mul hph).aestronglyMeasurable (Filter.Eventually.of_forall fun X => ?_)
  rw [norm_mul, hψ.2.1, mul_one]

end GlobalTheory.CompanionTheory.SiegelND.Integ.Phase
