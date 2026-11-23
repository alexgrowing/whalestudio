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

theorem nsg_continuousOn_ne_zero (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] [MeasurableSpace E] [BorelSpace E] [Algebra F E] [ValuativeExtension F E] [FiniteDimensional F E] [Algebra.IsSeparable F E] [Fact (Module.finrank F E = 2)] :
    ContinuousOn (GL2LocalData.nsg E : F → ℂ) {a | a ≠ 0} := by
  classical
  obtain ⟨h1, h2⟩ := GlobalTheory.T.isOpen_norm_image_units F E
  intro a ha
  apply ContinuousAt.continuousWithinAt
  by_cases h : ∃ t : Eˣ, Algebra.norm F (t : E) = a
  · have hev : (GL2LocalData.nsg E : F → ℂ) =ᶠ[𝓝 a] fun _ => 1 := by
      filter_upwards [h1.mem_nhds h] with x hx
      unfold GL2LocalData.nsg
      exact if_pos hx
    exact continuousAt_const.congr hev.symm
  · have hev : (GL2LocalData.nsg E : F → ℂ) =ᶠ[𝓝 a] fun _ => -1 := by
      filter_upwards [h2.mem_nhds ⟨ha, h⟩] with x hx
      unfold GL2LocalData.nsg
      exact if_neg hx.2
    exact continuousAt_const.congr hev.symm

theorem wS_continuousOn_lower_zero : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] [MeasurableSpace E] [BorelSpace E] [Algebra F E] [ValuativeExtension F E] [FiniteDimensional F E] [Algebra.IsSeparable F E] [Fact (Module.finrank F E = 2)] (χ : AddChar F Circle) (σ : E ≃ₐ[F] E) (μ : Measure E) (lam : ℂ) (c : Eˣ →* ℂˣ) (Φ : E → ℂ), Continuous χ → Continuous (algebraMap F E) → IsUnit1 c → IsLocallyConstant Φ → ContinuousOn (fun p : GL (Fin 2) F × Eˣ => wS χ σ μ lam c Φ p.1 p.2) {p | p.1.val 1 0 = 0} := by
  intro F _ _ _ _ _ _ E _ _ _ _ _ _ _ _ _ _ _ χ σ μ lam c Φ hχ hal hc hΦ
  set S : Set (GL (Fin 2) F × Eˣ) := {p | p.1.val 1 0 = 0} with hS
  have hent : ∀ i j : Fin 2, Continuous fun p : GL (Fin 2) F × Eˣ => p.1.val i j := fun i j =>
    (Units.continuous_val.comp continuous_fst).matrix_elem i j
  have hdetc : Continuous fun p : GL (Fin 2) F × Eˣ => (p.1.val).det :=
    (Units.continuous_val.comp continuous_fst).matrix_det
  have hd0 : ∀ p : GL (Fin 2) F × Eˣ, (p.1.val).det ≠ 0 := fun p =>
    ((Matrix.isUnit_iff_isUnit_det _).1 p.1.isUnit).ne_zero
  have ha0 : ∀ p ∈ S, p.1.val 0 0 / (p.1.val).det ≠ 0 := by
    intro p hp
    have hp' : p.1.val 1 0 = 0 := hp
    have h00 : p.1.val 0 0 ≠ 0 := by
      intro h0
      apply hd0 p
      rw [Matrix.det_fin_two, hp', h0]; ring
    exact div_ne_zero h00 (hd0 p)
  have hac : ContinuousOn (fun p : GL (Fin 2) F × Eˣ => p.1.val 0 0 / (p.1.val).det) S :=
    (hent 0 0).continuousOn.div hdetc.continuousOn fun p _ => hd0 p
  have hmod : Continuous fun x : F => ((modulus x : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (NNReal.continuous_coe.comp continuous_modulus)
  have hcc : Continuous fun p : GL (Fin 2) F × Eˣ => ((c p.2 : ℂˣ) : ℂ) :=
    Units.continuous_val.comp (hc.1.comp continuous_snd)
  have hpow : ContinuousOn (fun p : GL (Fin 2) F × Eˣ =>
      (((modulus (p.1.val).det : ℝ) : ℂ)) ^ (1 / 2 : ℂ)) S := by
    refine ContinuousOn.cpow (hmod.comp hdetc).continuousOn continuousOn_const ?_
    intro p _
    have hpos : (0 : ℝ) < (modulus (p.1.val).det : ℝ) := by
      exact_mod_cast modulus_pos (hd0 p)
    exact Complex.ofReal_mem_slitPlane.2 hpos
  have hχc : ContinuousOn (fun p : GL (Fin 2) F × Eˣ =>
      ((χ (p.1.val 0 0 / (p.1.val).det * p.1.val 0 1) : Circle) : ℂ)) S :=
    ((continuous_induced_dom : Continuous ((↑) : Circle → ℂ)).comp hχ).comp_continuousOn (hac.mul (hent 0 1).continuousOn)
  have hnc : ContinuousOn (fun p : GL (Fin 2) F × Eˣ =>
      GL2LocalData.nsg E (p.1.val 0 0 / (p.1.val).det)) S :=
    (nsg_continuousOn_ne_zero F E).comp hac ha0
  have hmc : ContinuousOn (fun p : GL (Fin 2) F × Eˣ =>
      ((modulus (p.1.val 0 0 / (p.1.val).det) : ℝ) : ℂ)) S :=
    hmod.comp_continuousOn hac
  have hΦc : ContinuousOn (fun p : GL (Fin 2) F × Eˣ =>
      Φ (algebraMap F E (p.1.val 0 0 / (p.1.val).det) * (p.2 : E))) S :=
    hΦ.continuous.comp_continuousOn ((hal.comp_continuousOn hac).mul
      (Units.continuous_val.comp continuous_snd).continuousOn)
  have key := ((hcc.continuousOn.mul hpow).mul (((hχc.mul hnc).mul hmc).mul hΦc))
  refine key.congr ?_
  intro p hp
  have hp' : p.1.val 1 0 = 0 := hp
  simp only [wS, GL2LocalData.rW, hp', zero_div, if_true, map_one, mul_one, Pi.mul_apply]

end GlobalTheory.CompanionTheory.WcB
