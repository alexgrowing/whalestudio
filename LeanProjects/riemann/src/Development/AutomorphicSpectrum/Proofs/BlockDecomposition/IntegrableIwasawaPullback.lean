import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocalWhittakerDuality.WhittakerFunctionalEquationAdditive
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Th
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData GlobalTheory.CompanionTheory.DampedZetaMajorant
open scoped ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.BochIw

section D

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

theorem continuous_diag_torus_pair : Continuous (fun q : Fˣ × Fˣ => (dg2 q.1 q.2 : GL (Fin 2) F)) := by
  have h1 : Continuous fun q : Fˣ × Fˣ => (q.1 : F) := Units.continuous_val.comp continuous_fst
  have h2 : Continuous fun q : Fˣ × Fˣ => (q.2 : F) := Units.continuous_val.comp continuous_snd
  have h3 : Continuous fun q : Fˣ × Fˣ => ((q.1⁻¹ : Fˣ) : F) :=
    Units.continuous_val.comp (continuous_inv.comp continuous_fst)
  have h4 : Continuous fun q : Fˣ × Fˣ => ((q.2⁻¹ : Fˣ) : F) :=
    Units.continuous_val.comp (continuous_inv.comp continuous_snd)
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · refine continuous_matrix fun i j => ?_
    show Continuous fun q : Fˣ × Fˣ => (!![(q.1 : F), 0; 0, (q.2 : F)] : Matrix (Fin 2) (Fin 2) F) i j
    fin_cases i <;> fin_cases j <;>
      first | (simpa using h1) | (simpa using h2) | (simpa using continuous_const)
  · refine continuous_matrix fun i j => ?_
    show Continuous fun q : Fˣ × Fˣ =>
      (!![((q.1⁻¹ : Fˣ) : F), 0; 0, ((q.2⁻¹ : Fˣ) : F)] : Matrix (Fin 2) (Fin 2) F) i j
    fin_cases i <;> fin_cases j <;>
      first | (simpa using h3) | (simpa using h4) | (simpa using continuous_const)

theorem cont_hI : Continuous (hI : Fˣ × Fˣ × GL (Fin 2) F → GL (Fin 2) F) := by
  have h1 : Continuous fun p : Fˣ × Fˣ × GL (Fin 2) F => (p.1 * p.2.1, p.2.1) := by fun_prop
  exact (continuous_diag_torus_pair.comp h1).mul (by fun_prop)

def Tm (q : (Fˣ × Fˣ × GL (Fin 2) F) × (Fˣ × F)) : Fˣ × GL (Fin 2) F :=
  (q.2.1, uni2 q.2.2 * hI q.1)

theorem measurable_wR' : Measurable (wR (F := F)) :=
  ((NNReal.continuous_coe.comp (continuous_modulus.comp Units.continuous_val)).measurable.comp
    measurable_fst).inv

theorem wR_pos' (p : Fˣ × Fˣ × GL (Fin 2) F) : 0 < wR p :=
  inv_pos.2 (by exact_mod_cast modulus_pos p.1.ne_zero)

end D

end GlobalTheory.CompanionTheory.BochIw
