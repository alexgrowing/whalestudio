import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.NDDefs
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HypOneZeroZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DensityUnitLattice
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LocalDensitiesBoundedAlmostAll
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.EulerProductLocalDensitiesConverges
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.GoodMassLt

open GlobalTheory.CompanionTheory.SW.GoodMass

section Main

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E}

theorem key (hcm : IsCMExt F E σ) : ∀ (n M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
    n < M → ∀ (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a b, σ (T b a) = T a b),
    T.det ≠ 0 → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∃ C : ℝ,
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ lam, IsStdV v lam → ∀ m,
      IsGramFib (Fv F v) σ J n (coordW (Fv F v) b lam n M) (coordHerm (Fv F v) σ b lam n) m →
      |(m (hermOf (Fv F v) σ T hT) (latV b v)).toReal - 1| ≤
        C / (Ideal.absNorm v.asIdeal : ℝ) ^ 2 := by
  intro n
  induction n with
  | zero =>
    intro M J hJ _ T hT _ d b
    refine ⟨0, Filter.Eventually.of_forall ?_⟩
    intro v lam hl m hm
    haveI : BorelSpace (Fv F v) := ⟨rfl⟩
    have h0 := GlobalTheory.T.rank_zero_gram_fiber_measure F E σ hcm M J hJ (Fv F v) (GlobalTheory.T.completion_is_local_ring F v) d b lam hl.1 m hm
      (hermOf (Fv F v) σ T hT)
    have hU : (latV b v : Set (Fin 0 → Fin M → Fv F v ⊗[F] E)) = Set.univ := by
      ext Y
      simp [latV]
    rw [h0, hU, measure_univ]
    simp
  | succ n ih =>
    intro M J hJ hn T hT hdet d b
    obtain ⟨M₁, rfl⟩ : ∃ M₁, M = M₁ + 1 := ⟨M - 1, by omega⟩
    obtain ⟨x, t, ht, hx⟩ := exists_aniso hcm T hT hdet
    obtain ⟨g, T₁, hT₁, hblock, -⟩ :=
      AlgSplit.split_anisotropic F E σ hcm n T ⟨hT, hdet⟩ t x ht hx
    have hbh : ∀ a b, σ (blockOne (algebraMap F E t) T₁ b a) = blockOne (algebraMap F E t) T₁ a b :=
      blockOne_herm _ (σ.commutes t) _ hT₁.1
    have hgdet : (g : Matrix (Fin (n + 1)) (Fin (n + 1)) E).det ≠ 0 :=
      ((Matrix.isUnit_iff_isUnit_det _).1 g.isUnit).ne_zero
    have hone : IsHermND σ (1 : Matrix (Fin M₁) (Fin M₁) E) := one_hermND M₁
    have hJ' : IsHermND σ (blockOne (algebraMap F E t) (1 : Matrix (Fin M₁) (Fin M₁) E)) :=
      blockOne_hermND t ht
    obtain ⟨C₁, hC₁⟩ := ih M₁ 1 hone (by omega) T₁ hT₁.1 hT₁.2 d b
    refine ⟨3 * |C₁| + 2, ?_⟩
    have e1 := GlobalTheory.T.local_densities_congruent_target_almost_all F E σ hcm (M₁ + 1) J hJ (n + 1) T hT hdet g hgdet _ hbh hblock d b
    have e2 := GlobalTheory.T.local_gram_fiber_measures_agree_almost_all F E σ hcm (M₁ + 1) J hJ _ hJ' d b (n + 1)
    have e3 := GlobalTheory.T.local_densities_block_one_almost_all F E σ hcm M₁ 1 hone t ht n T₁ hT₁.1 hT₁.2 hbh d b
    have e4 := GlobalTheory.CompanionTheory.SW.UnitVal.density_unit_lattice F E σ hcm (M₁ + 1) _ hJ' (by omega) d b
    have e5 := (GlobalTheory.T.integral_almost_all_places F E σ hcm d b).2 t ht
    filter_upwards [e1, e2, e3, e4, e5, hC₁] with v h1 h2 h3 h4 h5 h6 lam hl m hm
    obtain ⟨m', hm'⟩ := exists_family hcm hJ' b v lam hl (n + 1)
    obtain ⟨m₁, hm₁⟩ := exists_family hcm hJ' b v lam hl 1
    obtain ⟨m₂, hm₂⟩ := exists_family hcm hone b v lam hl n
    have a1 := h1 lam hl m hm
    have a2 := h2 lam hl m m' hm hm' (hermOf (Fv F v) σ _ hbh)
    have a3 := h3 lam hl m' m₁ m₂ hm' hm₁ hm₂
    have a4 := h4 lam hl m₁ hm₁ _ h5
    have a6 := h6 lam hl m₂ hm₂
    have hq1 := absNorm_one_le (F := F) v
    have a4' : |(m₁ (hermScal (Fv F v) σ (algebraMap F (Fv F v) t)) (latV b v)).toReal - 1| ≤
        2 / (Ideal.absNorm v.asIdeal : ℝ) ^ (M₁ + 1) :=
      a4.trans (div_le_div_of_nonneg_right (by norm_num) (by positivity))
    rw [← a1, a2, a3, ENNReal.toReal_mul]
    exact arith hq1 (by omega) a4' a6

end Main

end GlobalTheory.CompanionTheory.SW.GoodMassLt

namespace GlobalTheory.CompanionTheory.SW

end GlobalTheory.CompanionTheory.SW
