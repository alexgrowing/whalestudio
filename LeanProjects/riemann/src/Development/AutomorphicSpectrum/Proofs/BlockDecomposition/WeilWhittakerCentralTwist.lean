import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.RationalPrimesBelowPlaces
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.SquareIntegrable.SSmooth
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TemperedBoundGL2
import GroundTheory.LocalFields.QuadraticAbelian.WeilRepQuadratic
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSmoothCharCompNorm
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WcEqZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilWhittakerBoundQuadraticExtensionStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilWhittakerSupportQuadraticExtensionStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilCharacterTwistNontrivialGaloisStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilWhittakerGaloisConjugateStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilWhittakerNontrivialGaloisIntegralStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactTranslateEntriesBoundedStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsOpenNormImageUnitsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormImageNeighbourhoodEventuallyStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilWhittakerContinuityQuadraticExtensionStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilWhittakerMeasureIndependenceStatement
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open scoped ValuativeRel
open GlobalTheory.CompanionTheory.DualHol
open GlobalTheory.CompanionTheory.WcB
open scoped Topology

namespace GlobalTheory.CompanionTheory.WcB

theorem Wc_continuousOn_of_wS : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] [MeasurableSpace E] [BorelSpace E] [Algebra F E] [ValuativeExtension F E] [FiniteDimensional F E] [Algebra.IsSeparable F E] [Fact (Module.finrank F E = 2)] (χ : AddChar F Circle) (σ : E ≃ₐ[F] E) (μ : Measure E) (lam : ℂ) (c : Eˣ →* ℂˣ) (Φ : E → ℂ), Φ ∈ GL2LocalData.SBc F E c → ∀ A : Set (GL (Fin 2) F), ContinuousOn (fun p : GL (Fin 2) F × Eˣ => wS χ σ μ lam c Φ p.1 p.2) {p | p.1 ∈ A} → ContinuousOn (GL2LocalData.Wc χ σ μ lam c Φ) (A ∩ {g | ∃ t : Eˣ, Algebra.norm F (t : E) = (g.val).det}) := by
  intro F _ _ _ _ _ _ E _ _ _ _ _ _ _ _ _ _ _ χ σ μ lam c Φ hΦ A hc g₀ hg₀
  obtain ⟨hgA, t₀, ht₀⟩ := hg₀
  have key : ∀ (g : GL (Fin 2) F) (t : Eˣ), Algebra.norm F (t : E) = (g.val).det →
      GL2LocalData.Wc χ σ μ lam c Φ g = wS χ σ μ lam c Φ g t := by
    intro g t ht
    have h : ∃ t : Eˣ, Algebra.norm F (t : E) = (g.val).det := ⟨t, ht⟩
    rw [Wc_eq_wS χ σ μ lam c Φ g h]
    exact GlobalTheory.T.weil_whittaker_measure_independence F E χ σ μ lam c Φ hΦ g _ t (h.choose_spec.trans ht.symm)
  rw [ContinuousWithinAt, key g₀ t₀ ht₀]
  intro V hV
  have h2 := (hc (g₀, t₀) hgA) hV
  obtain ⟨u, hu, hsub⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.1 h2
  rw [nhds_prod_eq] at hu
  obtain ⟨U, hU, T, hT, hprod⟩ := Filter.mem_prod_iff.1 hu
  have hev := GlobalTheory.T.norm_image_neighbourhood_eventually F E t₀ T hT
  rw [ht₀] at hev
  have hdet : Continuous (fun g : GL (Fin 2) F => (g.val).det) :=
    Continuous.matrix_det Units.continuous_val
  have hev' : ∀ᶠ g in 𝓝 g₀, ∃ t ∈ T, Algebra.norm F (t : E) = (g.val).det :=
    hdet.continuousAt.eventually hev
  refine Filter.mem_map.2 ?_
  filter_upwards [mem_nhdsWithin_of_mem_nhds hU, mem_nhdsWithin_of_mem_nhds hev',
    self_mem_nhdsWithin] with g hgU hgt hgS
  obtain ⟨t, htT, ht⟩ := hgt
  show GL2LocalData.Wc χ σ μ lam c Φ g ∈ V
  rw [key g t ht]
  have hp : ((g, t) : GL (Fin 2) F × Eˣ) ∈ u ∩ {p | p.1 ∈ A} :=
    ⟨hprod (Set.mk_mem_prod hgU htT), hgS.1⟩
  exact hsub hp

end GlobalTheory.CompanionTheory.WcB
