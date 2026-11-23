import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocalWhittakerDuality.WhittakerFunctionalEquationAdditive
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GodementJacquetMinusOne
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PhdEqPhk
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData
open scoped ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.GJMeas

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

theorem continuous_detUnit : Continuous (GeneralLinearGroup.det : GL (Fin 2) F → Fˣ) := by
  rw [Units.continuous_iff]
  constructor
  · exact Continuous.matrix_det Units.continuous_val
  · have : Continuous fun g : GL (Fin 2) F => ((g⁻¹ : GL (Fin 2) F).val).det :=
      Continuous.matrix_det (Units.continuous_val.comp continuous_inv)
    convert this using 2 with g
    rw [← map_inv]
    rfl

theorem continuous_of_rightInvariant (W : GL (Fin 2) F → ℂ) (U : OpenSubgroup (GL (Fin 2) F))
    (h : ∀ g, ∀ u ∈ U, W (g * u) = W g) : Continuous W := by
  rw [continuous_iff_continuousAt]
  intro g
  have hopen : IsOpen ((fun x : GL (Fin 2) F => g⁻¹ * x) ⁻¹' (U : Set (GL (Fin 2) F))) :=
    U.isOpen.preimage (continuous_const.mul continuous_id)
  have hmem : ((fun x : GL (Fin 2) F => g⁻¹ * x) ⁻¹' (U : Set (GL (Fin 2) F))) ∈ nhds g :=
    hopen.mem_nhds (by simpa using U.one_mem)
  have hev : (fun _ : GL (Fin 2) F => W g) =ᶠ[nhds g] W := by
    filter_upwards [hmem] with x hx
    have := h g (g⁻¹ * x) hx
    simpa using this.symm
  exact (continuousAt_const).congr hev

theorem continuous_mp_det (z : ℂ) :
    Continuous fun g : GL (Fin 2) F => mp (GeneralLinearGroup.det g) z := by
  have h1 : Continuous fun g : GL (Fin 2) F =>
      ((modulus (((GeneralLinearGroup.det g : Fˣ)) : F) : ℝ) : ℂ) := by
    have h2 : Continuous fun g : GL (Fin 2) F => modulus (((GeneralLinearGroup.det g : Fˣ)) : F) :=
      continuous_modulus.comp (Units.continuous_val.comp continuous_detUnit)
    exact Complex.continuous_ofReal.comp (NNReal.continuous_coe.comp h2)
  refine h1.cpow continuous_const fun g => ?_
  refine Complex.ofReal_mem_slitPlane.2 ?_
  exact_mod_cast modulus_pos (Units.ne_zero _)

theorem continuous_phd (ψ : AddChar F Circle) (hψ : Continuous ψ)
    (Φ : Matrix (Fin 2) (Fin 2) F → ℂ) (hΦ : SB2 Φ) : Continuous (phd ψ Φ) := by
  obtain ⟨hlc, hcs⟩ := hΦ
  have hΦc : Continuous Φ := hlc.continuous
  obtain ⟨C, hC⟩ := hcs.exists_bound_of_continuous hΦc
  have hrow : Continuous fun X : Matrix (Fin 2) (Fin 2) F => (X 0 : Fin 2 → F) :=
    continuous_pi fun j => continuous_id.matrix_elem 0 j
  set K : Set (Fin 2 → F) := (fun X : Matrix (Fin 2) (Fin 2) F => (X 0 : Fin 2 → F)) '' tsupport Φ
    with hKdef
  have hK : IsCompact K := hcs.isCompact.image hrow
  have hcoe : Continuous fun z : Circle => (z : ℂ) := by
    first
      | fun_prop
      | exact continuous_subtype_val
      | exact continuous_induced_dom
  have hψi : Continuous fun x : F => ((ψ⁻¹ x : Circle) : ℂ) := by
    have : (fun x : F => ((ψ⁻¹ x : Circle) : ℂ)) = fun x : F => ((ψ (-x) : Circle) : ℂ) := by
      funext x
      rw [AddChar.inv_apply]
    rw [this]
    exact hcoe.comp (hψ.comp continuous_neg)
  have hrows : ∀ r : Fin 2 → F, Continuous fun g : GL (Fin 2) F =>
      what₂ r (fun j => g.val 0 j / (g.val).det) := by
    intro r
    refine continuous_matrix fun i j => ?_
    fin_cases i
    · simpa [what₂] using continuous_const
    · have hdet : Continuous fun g : GL (Fin 2) F => (g.val).det :=
        Continuous.matrix_det Units.continuous_val
      have hent : Continuous fun g : GL (Fin 2) F => g.val 0 j :=
        Units.continuous_val.matrix_elem 0 j
      have h : Continuous fun g : GL (Fin 2) F => g.val 0 j / (g.val).det :=
        hent.div hdet fun g => (Matrix.GeneralLinearGroup.det g).ne_zero
      simpa [what₂] using h
  have hcont2 : ∀ g : GL (Fin 2) F, Continuous fun r : Fin 2 → F =>
      Φ (what₂ r (fun j => g.val 0 j / (g.val).det)) *
        ((ψ⁻¹ (r 0 * g.val 1 1 - r 1 * g.val 1 0) : Circle) : ℂ) := by
    intro g
    refine (hΦc.comp ?_).mul (hψi.comp ?_)
    · refine continuous_matrix fun i j => ?_
      fin_cases i
      · simpa [what₂] using continuous_apply j
      · simpa [what₂] using continuous_const
    · exact ((continuous_apply 0).mul continuous_const).sub ((continuous_apply 1).mul continuous_const)
  unfold phd
  refine continuous_of_dominated (bound := K.indicator fun _ => C) ?_ ?_ ?_ ?_
  · exact fun g => (hcont2 g).aestronglyMeasurable
  · refine fun g => Filter.Eventually.of_forall fun r => ?_
    by_cases hr : r ∈ K
    · rw [Set.indicator_of_mem hr, norm_mul, Circle.norm_coe, mul_one]
      exact hC _
    · rw [Set.indicator_of_notMem hr]
      have h0 : Φ (what₂ r (fun j => g.val 0 j / (g.val).det)) = 0 := by
        by_contra hne
        exact hr ⟨_, subset_tsupport _ hne, rfl⟩
      simp [h0]
  · haveI : IsFiniteMeasureOnCompacts (LFS.vol2 ψ) := by
      unfold LFS.vol2; infer_instance
    refine (integrable_indicator_iff hK.measurableSet).2 ?_
    exact integrableOn_const hK.measure_lt_top.ne
  · refine Filter.Eventually.of_forall fun r => ?_
    refine (hΦc.comp (hrows r)).mul (hψi.comp ?_)
    exact (continuous_const.mul (Units.continuous_val.matrix_elem 1 1)).sub
      (continuous_const.mul (Units.continuous_val.matrix_elem 1 0))

theorem continuous_gjdI (ψ : AddChar F Circle) (hψ : Continuous ψ)
    (Φ : Matrix (Fin 2) (Fin 2) F → ℂ) (hΦ : SB2 Φ) (W : GL (Fin 2) F → ℂ) (hW : Continuous W)
    (ω μ : Fˣ →* ℂˣ) (hω : Continuous ω) (hμ : Continuous μ) (s : ℂ) :
    Continuous (gjdI ψ Φ W ω μ s) := by
  have hc : Continuous fun g : GL (Fin 2) F =>
      ((((ω * μ) (GeneralLinearGroup.det g))⁻¹ : ℂˣ) : ℂ) := by
    have hωμ : Continuous (ω * μ : Fˣ →* ℂˣ) := by
      have : ((ω * μ : Fˣ →* ℂˣ) : Fˣ → ℂˣ) = fun a => ω a * μ a := rfl
      rw [this]
      exact hω.mul hμ
    exact Units.continuous_val.comp (continuous_inv.comp (hωμ.comp continuous_detUnit))
  unfold gjdI
  exact (((continuous_phd ψ hψ Φ hΦ).mul hW).mul hc).mul (continuous_mp_det _)

theorem aestronglyMeasurable_gjdI : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (ψ : AddChar F Circle),
    IsStd ψ → ∀ (ω : Fˣ →* ℂˣ) (G : (Fˣ →* ℂˣ) → ℂ → ℂ) (V' : Submodule ℂ (GL (Fin 2) F → ℂ)),
    IsUnit1 ω → WhT ψ⁻¹ ω G V' → ∀ W ∈ V', ∀ μ : Fˣ →* ℂˣ, IsUnit1 μ → ∀ Φ, SB2 Φ → ∀ s : ℂ,
    AEStronglyMeasurable (gjdI ψ Φ W ω μ s) (LFS.hG ψ) := by
  intro F _ _ _ _ _ _ ψ hψ ω G V' hω hV W hWV μ hμ Φ hΦ s
  obtain ⟨U, hU⟩ := hV.smooth W hWV
  exact (continuous_gjdI ψ hψ.1 Φ hΦ W (continuous_of_rightInvariant W U hU) ω μ hω.1 hμ.1
    s).aestronglyMeasurable

end GlobalTheory.CompanionTheory.GJMeas
