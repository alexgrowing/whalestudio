import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GramNear
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelWeilConvergentRangeStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ContinuousIntegrableOfIsSchwartzBruhat
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelesLocallyCompactSecondCountableStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WhitFree
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.SiegelND.CoefSum

open GlobalTheory.Published.SiegelOneVector

def flat (S : Type) [AddCommGroup S] [TopologicalSpace S] (n M : ℕ) :
    (Fin n → Fin M → S) ≃ₜ+ (Fin 1 → Fin (n * M) → S) where
  toFun X _ k := X (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2
  invFun Y a i := Y 0 (finProdFinEquiv (a, i))
  left_inv X := by
    funext a i
    simp
  right_inv Y := by
    funext a k
    rw [Subsingleton.elim a 0]
    show Y 0 (finProdFinEquiv ((finProdFinEquiv.symm k).1, (finProdFinEquiv.symm k).2)) = Y 0 k
    rw [Prod.mk.eta, Equiv.apply_symm_apply]
  map_add' X Y := by
    funext a k
    simp
  continuous_toFun := continuous_pi fun _ => continuous_pi fun k =>
    (continuous_apply _).comp (continuous_apply _)
  continuous_invFun := continuous_pi fun a => continuous_pi fun i =>
    (continuous_apply _).comp (continuous_apply 0)

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

theorem isSchwartzBruhat_flat {n M : ℕ} {Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ}
    (hΦ : IsSchwartzBruhat Φ) : IsSchwartzBruhat (Φ ∘ (flat (AF F ⊗[F] E) n M).symm) := by
  obtain ⟨k, Φinf, Φf, hi, hf, hs⟩ := hΦ
  refine ⟨k, fun i => Φinf i ∘ (flat (Ainf F ⊗[F] E) n M).symm,
    fun i => Φf i ∘ (flat (Af F ⊗[F] E) n M).symm, fun i => ?_, fun i => ?_, fun Y => ?_⟩
  · obtain ⟨N, e, c1, c2, f, hfe⟩ := hi i
    let a : (Fin 1 → Fin (n * M) → Ainf F ⊗[F] E) ≃+ (Fin n → Fin M → Ainf F ⊗[F] E) :=
      (flat (Ainf F ⊗[F] E) n M).symm
    exact ⟨N, a.trans e, c1.comp (flat (Ainf F ⊗[F] E) n M).symm.continuous,
      (flat (Ainf F ⊗[F] E) n M).continuous.comp c2, f, fun X => hfe _⟩
  · exact ⟨(hf i).1.comp_continuous (flat (Af F ⊗[F] E) n M).symm.continuous,
      (hf i).2.comp_homeomorph (flat (Af F ⊗[F] E) n M).symm.toHomeomorph⟩
  · exact hs _

theorem continuous_integrable_tuple (σ : E →ₐ[F] E) [NumberField E] (hCM : IsCMExt F E σ) (M n : ℕ)
    (dx : Measure (Fin n → Fin M → AF F ⊗[F] E)) (hdx : dx.IsAddHaarMeasure)
    (Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ) (hΦ : IsSchwartzBruhat Φ) :
    Continuous Φ ∧ Integrable Φ dx := by
  obtain ⟨⟨_, _, _⟩, -⟩ := GlobalTheory.T.adeles_locally_compact_second_countable F
  obtain ⟨_, _, _, _, -, -, -, hB, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hCM (AF F)
  haveI := hB n M
  haveI := hB 1 (n * M)
  let c := flat (AF F ⊗[F] E) n M
  haveI : (dx.map c).IsAddHaarMeasure :=
    Measure.isAddHaarMeasure_map _
      (c : (Fin n → Fin M → AF F ⊗[F] E) ≃+ (Fin 1 → Fin (n * M) → AF F ⊗[F] E)).toAddMonoidHom
      c.continuous c.surjective
      c.toHomeomorph.isClosedEmbedding.tendsto_cocompact
  obtain ⟨h1, h2⟩ := GlobalTheory.CompanionTheory.Hypotheses₂.OneV.PoiInt.continuous_integrable_of_isSchwartzBruhat F E σ hCM
    (n * M) (dx.map c) inferInstance _ (isSchwartzBruhat_flat hΦ)
  have hcomp : (Φ ∘ c.symm) ∘ c = Φ := by
    funext X
    simp
  refine ⟨?_, ?_⟩
  · have h : Continuous ((Φ ∘ c.symm) ∘ c) := h1.comp c.continuous
    rwa [hcomp] at h
  · have h := (c.toHomeomorph.measurableEmbedding.integrable_map_iff).1 h2
    rwa [show (Φ ∘ c.symm) ∘ c.toHomeomorph = Φ from hcomp] at h

theorem coefN_finset_sum : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ n : ℕ, 0 < n → 2 * n < M → ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ → ∀ dx : Measure (Fin n → Fin M → AF F ⊗[F] E), SdW F E σ M J (AF F) ψ n dx → ∀ db : Measure (HermR (AF F) σ n), SdHerm F E σ (AF F) ψ n db → ∀ (T : Matrix (Fin n) (Fin n) E) (k : ℕ) (Φ : Fin k → (Fin n → Fin M → AF F ⊗[F] E) → ℂ), (∀ i, GlobalTheory.Published.SiegelOneVector.IsSchwartzBruhat (Φ i)) → coefN σ J ψ dx db (fun X => ∑ i, Φ i X) T = ∑ i, coefN σ J ψ dx db (Φ i) T := by
  intro F E _ _ _ _ _ σ hCM M J hJ n _ hM ψ hψ dx hdx db hdb T k Φ hΦ
  obtain ⟨⟨_, _, _⟩, -⟩ := GlobalTheory.T.adeles_locally_compact_second_countable F
  obtain ⟨_, _, _, _, -, ht, -, hB, -, hG⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hCM (AF F)
  haveI := hB n M
  obtain ⟨hψc, hψn, -⟩ := id hψ
  have hstar : ∀ b, starN σ J ψ dx (fun X => ∑ i, Φ i X) b = ∑ i, starN σ J ψ dx (Φ i) b := by
    intro b
    unfold starN
    simp_rw [Finset.sum_mul]
    refine integral_finset_sum _ fun i _ => ?_
    obtain ⟨hc, hi⟩ := continuous_integrable_tuple σ hCM M n dx hdx.1 (Φ i) (hΦ i)
    have hq : Continuous fun X : Fin n → Fin M → AF F ⊗[F] E =>
        algebraMap F (AF F) (1 / 2) * Algebra.trace (AF F) (AF F ⊗[F] E)
          (Matrix.trace ((b : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) * gramR (AF F) σ J X)) :=
      continuous_const.mul (ht.comp (continuous_const.matrix_mul (hG n M J)).matrix_trace)
    refine hi.norm.mono' (hc.mul (hψc.comp hq)).aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall fun x => ?_
    rw [norm_mul, hψn, mul_one]
  unfold coefN
  simp_rw [hstar, Finset.sum_mul]
  refine integral_finset_sum _ fun i _ => ?_
  have hI := GlobalTheory.T.siegel_weil_convergent_range F E σ hCM M J hJ n hM ψ hψ dx hdx db hdb (Φ i) (hΦ i)
  have hc : Continuous fun b : HermR (AF F) σ n =>
      ψ (-(algebraMap F (AF F) (1 / 2) * Algebra.trace (AF F) (AF F ⊗[F] E)
        (Matrix.trace (T.map (inclR (AF F)) * (b : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)))))) :=
    hψc.comp (continuous_const.mul
      (ht.comp (continuous_const.matrix_mul continuous_subtype_val).matrix_trace)).neg
  haveI : BorelSpace (HermR (AF F) σ n) := ⟨rfl⟩
  refine hI.norm.mono' (hI.1.mul hc.aestronglyMeasurable) ?_
  refine Filter.Eventually.of_forall fun b => ?_
  rw [norm_mul, hψn, mul_one]

end GlobalTheory.CompanionTheory.SiegelND.CoefSum
