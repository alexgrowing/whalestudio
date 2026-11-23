import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CstD
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open Ad3.R (G2 Jd md Dt KA Set0 Coord LInv pt dia2 pri)
open GlobalTheory.CompanionTheory.UnfoldingAlt
open scoped NumberField.AdeleRing ENNReal

namespace GlobalTheory.CompanionTheory.UnfoldingAlt.Ti

theorem ti_mul {R : Type} [CommRing R] {n : ℕ} (g h : GL (Fin n) R) : ti (g * h) = ti g * ti h := by
  apply Units.ext
  show ((g * h).inv).transpose = g.inv.transpose * h.inv.transpose
  show (h.inv * g.inv).transpose = _
  rw [Matrix.transpose_mul]

theorem ti_ti {R : Type} [CommRing R] {n : ℕ} (g : GL (Fin n) R) : ti (ti g) = g := by
  apply Units.ext
  exact Matrix.transpose_transpose _

theorem ti_diagonal {n : ℕ} (γ : GL (Fin n) ℚ) :
    ti (AdelicGLn.diagonal ℚ n γ) = AdelicGLn.diagonal ℚ n (ti γ) := by
  apply Units.ext
  ext a b
  rfl

theorem ti_cont {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] {n : ℕ} :
    Continuous (ti : GL (Fin n) R → GL (Fin n) R) := by
  rw [Units.continuous_iff]
  constructor
  · exact (Units.continuous_coe_inv).matrix_transpose
  · exact (Units.continuous_val).matrix_transpose

theorem ti_alg : (∀ (R : Type) [CommRing R] (n : ℕ) (g h : GL (Fin n) R), ti (g * h) = ti g * ti h ∧ ti (ti g) = g) ∧
  (∀ γ : GL (Fin 3) ℚ, ti (dia γ) = dia (ti γ)) ∧ (∀ γ : GL (Fin 2) ℚ, ti (dia2 γ) = dia2 (ti γ)) ∧
  Continuous (ti : G3 → G3) ∧ Continuous (ti : G2 → G2) :=
  ⟨fun _ _ _ g h => ⟨ti_mul g h, ti_ti g⟩, ti_diagonal, ti_diagonal, ti_cont, ti_cont⟩

end GlobalTheory.CompanionTheory.UnfoldingAlt.Ti
