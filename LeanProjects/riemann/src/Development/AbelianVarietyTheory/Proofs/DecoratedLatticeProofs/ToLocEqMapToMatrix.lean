import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PhiTopAgree
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FreeN
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SymBridge

namespace GlobalTheory.SymBridge

theorem toLoc_eq_map_toMatrix' {E k : Type} [Field E] [Field k] (ι : E →+* k) {A : Type} [Fintype A] [DecidableEq A]
    {N : ℕ} (e : A ≃ Fin N) (x : Sp E N →ₗ[E] Sp E N) :
    toLoc ι e e x = ((LinearMap.toMatrix' x).submatrix e e).map ι := by
  ext i j
  simp only [toLoc, Matrix.map_apply, Matrix.submatrix_apply, LinearMap.toMatrix'_apply]

theorem toLoc_comp_square {E k : Type} [Field E] [Field k] (ι : E →+* k) {A : Type} [Fintype A] [DecidableEq A]
    {N : ℕ} (e : A ≃ Fin N) (x y : Sp E N →ₗ[E] Sp E N) :
    toLoc ι e e (x ∘ₗ y) = toLoc ι e e x * toLoc ι e e y := by
  rw [toLoc_eq_map_toMatrix', toLoc_eq_map_toMatrix', toLoc_eq_map_toMatrix', LinearMap.toMatrix'_comp,
    ← Matrix.submatrix_mul_equiv _ _ _ e _, Matrix.map_mul]

theorem toLoc_id_square {E k : Type} [Field E] [Field k] (ι : E →+* k) {A : Type} [Fintype A] [DecidableEq A]
    {N : ℕ} (e : A ≃ Fin N) :
    toLoc ι e e (LinearMap.id : Sp E N →ₗ[E] Sp E N) = 1 := by
  rw [toLoc_eq_map_toMatrix', LinearMap.toMatrix'_id, Matrix.submatrix_one_equiv,
    Matrix.map_one _ ι.map_zero ι.map_one]

end GlobalTheory.SymBridge
