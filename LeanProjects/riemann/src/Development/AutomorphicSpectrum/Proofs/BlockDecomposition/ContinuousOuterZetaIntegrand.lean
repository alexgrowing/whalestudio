import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocalWhittakerDuality.WhittakerFunctionalEquationAdditive
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Aq
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrableIwasawaPullback
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DampedWhittakerLimitAsTwistVanishes
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData GlobalTheory.CompanionTheory.DampedZetaMajorant GlobalTheory.CompanionTheory.GL2Unfolding GlobalTheory.CompanionTheory.GJTwo
open scoped ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.GL2Unfolding.AqCont

section D

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

theorem cont_det : Continuous (fun h : GL (Fin 2) F => (GeneralLinearGroup.det h : Fˣ)) := by
  have hd : Continuous (Matrix.detMonoidHom : Matrix (Fin 2) (Fin 2) F →* F) := by
    show Continuous fun A : Matrix (Fin 2) (Fin 2) F => A.det
    exact continuous_id.matrix_det
  exact Continuous.units_map _ hd

theorem continuous_second_vector_GL2 : Continuous (e2r : GL (Fin 2) F → Fin 2 → F) := by
  refine continuous_pi fun i => ?_
  have hv : Continuous fun h : GL (Fin 2) F => (h.val : Matrix (Fin 2) (Fin 2) F) := Units.continuous_val
  have he : ∀ a b : Fin 2, Continuous fun h : GL (Fin 2) F => h.val a b := fun a b =>
    (continuous_apply_apply a b).comp hv
  fin_cases i
  · simpa [e2r] using he 1 0
  · simpa [e2r] using he 1 1

theorem cont_wR : Continuous (wR : Fˣ × Fˣ × GL (Fin 2) F → ℝ) := by
  have hc : Continuous fun p : Fˣ × Fˣ × GL (Fin 2) F => (modulus (p.1 : F) : ℝ) :=
    NNReal.continuous_coe.comp (continuous_modulus.comp (Units.continuous_val.comp continuous_fst))
  refine hc.inv₀ fun p => ?_
  have h0 : (0 : ℝ) < (modulus (p.1 : F) : ℝ) := by exact_mod_cast modulus_pos p.1.ne_zero
  exact h0.ne'

theorem continuous_Aq : ForS fun F _ _ _ _ _ _ ψ => ∀ (W₀ W' : GL (Fin 2) F → ℂ) (Φ : Matrix (Fin 2) (Fin 3) F → ℂ) (s : ℂ),
  Continuous W₀ → Continuous W' → Continuous (fun q : Matrix (Fin 2) (Fin 2) F × (Fin 2 → F) => pFT ψ Φ q.1 q.2) →
  Continuous (Aq ψ W₀ W' Φ s) := by
  intro F _ _ _ _ _ _ ψ _ W₀ W' Φ s hW₀ hW' hP
  have hg : Continuous fun q : (Fˣ × Fˣ × GL (Fin 2) F) × GL (Fin 2) F => q.2 := continuous_snd
  have hh : Continuous fun q : (Fˣ × Fˣ × GL (Fin 2) F) × GL (Fin 2) F => hI q.1 * q.2⁻¹ :=
    (GlobalTheory.CompanionTheory.BochIw.cont_hI.comp continuous_fst).mul continuous_snd.inv
  have hhg : Continuous fun q : (Fˣ × Fˣ × GL (Fin 2) F) × GL (Fin 2) F =>
      hI q.1 * q.2⁻¹ * q.2 := hh.mul hg
  have hm1 : Continuous fun q : (Fˣ × Fˣ × GL (Fin 2) F) × GL (Fin 2) F =>
      mp (GeneralLinearGroup.det q.2) (s + 1 / 2) :=
    (GlobalTheory.CompanionTheory.DampedWhittakerLimit.continuous_mp (s + 1 / 2)).comp (cont_det.comp hg)
  have hm2 : Continuous fun q : (Fˣ × Fˣ × GL (Fin 2) F) × GL (Fin 2) F =>
      mp (GeneralLinearGroup.det (hI q.1 * q.2⁻¹)) s :=
    (GlobalTheory.CompanionTheory.DampedWhittakerLimit.continuous_mp s).comp (cont_det.comp hh)
  have hw : Continuous fun q : (Fˣ × Fˣ × GL (Fin 2) F) × GL (Fin 2) F =>
      ((GlobalTheory.CompanionTheory.DampedZetaMajorant.wR q.1 : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (cont_wR.comp continuous_fst)
  have hp : Continuous fun q : (Fˣ × Fˣ × GL (Fin 2) F) × GL (Fin 2) F =>
      pFT ψ Φ q.2.val (e2r (hI q.1 * q.2⁻¹)) :=
    hP.comp ((Units.continuous_val.comp hg).prodMk (continuous_second_vector_GL2.comp hh))
  unfold Aq Bq
  exact hm1.mul (hw.mul ((((hW₀.comp hh).mul (hW'.comp hhg)).mul hp).mul hm2))

end D

end GlobalTheory.CompanionTheory.GL2Unfolding.AqCont
