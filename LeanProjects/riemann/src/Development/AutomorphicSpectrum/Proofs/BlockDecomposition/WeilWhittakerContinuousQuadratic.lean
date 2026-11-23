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

namespace GlobalTheory.CompanionTheory.WcB.ContNe

theorem continuousOn_nsg (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] [MeasurableSpace E] [BorelSpace E] [Algebra F E] [ValuativeExtension F E] [FiniteDimensional F E] [Algebra.IsSeparable F E] [Fact (Module.finrank F E = 2)] :
    ContinuousOn (GL2LocalData.nsg E : F → ℂ) {a | a ≠ 0} := by
  obtain ⟨h1, h2⟩ := GlobalTheory.T.isOpen_norm_image_units F E
  intro a ha
  apply ContinuousAt.continuousWithinAt
  by_cases h : ∃ t : Eˣ, Algebra.norm F (t : E) = a
  · have hev : (GL2LocalData.nsg E : F → ℂ) =ᶠ[𝓝 a] fun _ => 1 := by
      filter_upwards [h1.mem_nhds h] with b hb
      unfold GL2LocalData.nsg
      exact if_pos hb
    exact continuousAt_const.congr hev.symm
  · have hev : (GL2LocalData.nsg E : F → ℂ) =ᶠ[𝓝 a] fun _ => -1 := by
      filter_upwards [h2.mem_nhds ⟨ha, h⟩] with b hb
      unfold GL2LocalData.nsg
      exact if_neg hb.2
    exact continuousAt_const.congr hev.symm

theorem continuousOn_pair {A B C X : Type} [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
    [TopologicalSpace X] {S : Set X} (G : A → B → C) (h : Continuous fun p : A × B => G p.1 p.2)
    {κ : X → A} {ξ : X → B} (hk : ContinuousOn κ S) (hx : ContinuousOn ξ S) :
    ContinuousOn (fun x => G (κ x) (ξ x)) S :=
  h.comp_continuousOn (hk.prodMk hx)

theorem continuousOn_wS : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] [MeasurableSpace E] [BorelSpace E] [Algebra F E] [ValuativeExtension F E] [FiniteDimensional F E] [Algebra.IsSeparable F E] [Fact (Module.finrank F E = 2)] (χ : AddChar F Circle), Continuous χ → Continuous (algebraMap F E) → ∀ σ : E ≃ₐ[F] E, σ ≠ AlgEquiv.refl → ∀ (μ : Measure E) [μ.IsAddHaarMeasure] (lam : ℂ) (c : Eˣ →* ℂˣ), IsUnit1 c → ∀ Φ : E → ℂ, IsLocallyConstant Φ → HasCompactSupport Φ → ContinuousOn (fun p : GL (Fin 2) F × Eˣ => wS χ σ μ lam c Φ p.1 p.2) {p | p.1.val 1 0 ≠ 0} := by
  intro F _ _ _ _ _ _ E _ _ _ _ _ _ _ _ _ _ _ χ hχ halg σ hσ μ _ lam c hc Φ hΦ hΦc
  let S : Set (GL (Fin 2) F × Eˣ) := {p | p.1.val 1 0 ≠ 0}
  have hent : ∀ i j, Continuous fun p : GL (Fin 2) F × Eˣ => p.1.val i j := fun i j =>
    (continuous_id.matrix_elem i j).comp (Units.continuous_val.comp continuous_fst)
  have hdet : Continuous fun p : GL (Fin 2) F × Eˣ => (p.1.val).det :=
    Continuous.matrix_det (Units.continuous_val.comp continuous_fst)
  have hdet0 : ∀ p : GL (Fin 2) F × Eˣ, (p.1.val).det ≠ 0 := fun p =>
    ((Matrix.isUnit_iff_isUnit_det _).1 p.1.isUnit).ne_zero
  have hcc : ContinuousOn (fun p : GL (Fin 2) F × Eˣ => p.1.val 1 0 / (p.1.val).det) S :=
    (hent 1 0).continuousOn.div hdet.continuousOn fun p _ => hdet0 p
  have hcc0 : ∀ p ∈ S, p.1.val 1 0 / (p.1.val).det ≠ 0 := fun p hp => div_ne_zero hp (hdet0 p)
  have ht : Continuous fun p : GL (Fin 2) F × Eˣ => (p.2 : E) :=
    Units.continuous_val.comp continuous_snd
  have hN : Continuous fun p : GL (Fin 2) F × Eˣ => Algebra.norm F (p.2 : E) :=
    (GlobalTheory.LBC.Inh.continuous_algNorm halg).comp ht
  have hN0 : ∀ p : GL (Fin 2) F × Eˣ, Algebra.norm F (p.2 : E) ≠ 0 := fun p =>
    Algebra.norm_ne_zero_iff.2 p.2.ne_zero
  have hmodF : Continuous fun x : F => (modulus x : ℝ) :=
    NNReal.continuous_coe.comp continuous_modulus
  have hmodE : Continuous fun x : E => (modulus x : ℝ) :=
    NNReal.continuous_coe.comp continuous_modulus
  have hC : Continuous fun p : GL (Fin 2) F × Eˣ => ((c p.2 : ℂˣ) : ℂ) :=
    Units.continuous_val.comp (hc.1.comp continuous_snd)
  have hD : ContinuousOn (fun p : GL (Fin 2) F × Eˣ =>
      (((modulus (p.1.val).det : ℝ) : ℂ) ^ (1 / 2 : ℂ))) S :=
    ((Complex.continuous_ofReal.comp (hmodF.comp hdet)).continuousOn).cpow continuousOn_const
      fun p _ => Complex.ofReal_mem_slitPlane.2 (NNReal.coe_pos.2 (modulus_pos (hdet0 p)))
  have hnsg : ContinuousOn (fun p : GL (Fin 2) F × Eˣ =>
      GL2LocalData.nsg E (-(p.1.val 1 0 / (p.1.val).det))) S :=
    (continuousOn_nsg F E).comp hcc.neg fun p hp => neg_ne_zero.2 (hcc0 p hp)
  have hmc : ContinuousOn (fun p : GL (Fin 2) F × Eˣ =>
      (((modulus (p.1.val 1 0 / (p.1.val).det) : ℝ)⁻¹ : ℝ) : ℂ)) S :=
    Complex.continuous_ofReal.comp_continuousOn ((hmodF.comp_continuousOn hcc).inv₀ fun p hp =>
      NNReal.coe_ne_zero.2 (modulus_ne_zero (hcc0 p hp)))
  have hmt : Continuous fun p : GL (Fin 2) F × Eˣ => (((modulus (p.2 : E) : ℝ)⁻¹ : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp ((hmodE.comp ht).inv₀ fun p =>
      NNReal.coe_ne_zero.2 (modulus_ne_zero p.2.ne_zero))
  have hchi : ContinuousOn (fun p : GL (Fin 2) F × Eˣ =>
      (χ ((p.1.val 0 0 / (p.1.val).det) / (p.1.val 1 0 / (p.1.val).det)) : ℂ)) S :=
    ((continuous_induced_dom : Continuous ((↑) : Circle → ℂ)).comp hχ).comp_continuousOn
      (((hent 0 0).continuousOn.div hdet.continuousOn fun p _ => hdet0 p).div hcc hcc0)
  have hkap : ContinuousOn (fun p : GL (Fin 2) F × Eˣ =>
      p.1.val 1 1 / ((p.1.val 1 0 / (p.1.val).det) * Algebra.norm F (p.2 : E))) S :=
    (hent 1 1).continuousOn.div (hcc.mul hN.continuousOn) fun p hp =>
      mul_ne_zero (hcc0 p hp) (hN0 p)
  have hxi : ContinuousOn (fun p : GL (Fin 2) F × Eˣ =>
      (algebraMap F E (p.1.val 1 0 / (p.1.val).det))⁻¹ * (p.2 : E)⁻¹) S :=
    ((halg.comp_continuousOn hcc).inv₀ fun p hp =>
      (map_ne_zero (algebraMap F E)).2 (hcc0 p hp)).mul
      (ht.continuousOn.inv₀ fun p _ => p.2.ne_zero)
  have hG : ContinuousOn (fun p : GL (Fin 2) F × Eˣ => gaussI χ μ Φ
      (p.1.val 1 1 / ((p.1.val 1 0 / (p.1.val).det) * Algebra.norm F (p.2 : E)))
      ((algebraMap F E (p.1.val 1 0 / (p.1.val).det))⁻¹ * (p.2 : E)⁻¹)) S :=
    continuousOn_pair (gaussI χ μ Φ) (GlobalTheory.T.weil_whittaker_continuity_quadratic_extension F E χ hχ μ Φ hΦ hΦc) hkap hxi
  have key := (hC.continuousOn.mul hD).mul
    (((((continuousOn_const (c := lam)).mul hnsg).mul hmc).mul hmt.continuousOn |>.mul hchi).mul hG)
  show ContinuousOn _ S
  refine key.congr fun p hp => ?_
  simp only [wS, Pi.mul_apply]
  rw [GlobalTheory.T.weil_whittaker_nontrivial_galois_integral F E χ σ hσ μ lam Φ _ _ _ _ (hcc0 p hp) p.2]

end GlobalTheory.CompanionTheory.WcB.ContNe
