import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffPolynomialEqZeroOfVanishingOnGLFamily
import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIsScalar
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField GlobalTheory.ExportSeries
open Formalism.IndefR.Links
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coeffPolynomial_eq_zero_of_vanishing_on_GLFamily : ∀ (D : D7) (n : ℕ) (lam : D.what₂.Tau → DomWeight n) (F : Formalism.L2.DIV.Pol ℂ D.what₂.Tau n), (∀ x : GLR D n, coefFn (RingHom.id ℂ) lam F x = 0) → F = 0 := by
  first | exact @GlobalTheory.ExportSeries.eq_zero_of_coefFn_id_eq_zero | exact GlobalTheory.ExportSeries.eq_zero_of_coefFn_id_eq_zero | (intros; apply GlobalTheory.ExportSeries.eq_zero_of_coefFn_id_eq_zero <;> assumption)
