import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.ChartA

noncomputable section

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Ald

set_option linter.unusedSectionVars false

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem trace_mul_single' {m k : ℕ} (A : Matrix (Fin k) (Fin m) (AE F E)) (a : Fin m) (c : Fin k) (z : AE F E) :
    (A * Matrix.single a c z).trace = A c a * z := by
  simp [Matrix.trace, Matrix.mul_apply, Matrix.single_apply, ite_and]

theorem map_single' {m k : ℕ} (a : Fin m) (c : Fin k) (z : AE F E) :
    (Matrix.single a c z).map (cA σ) = Matrix.single a c (cA σ z) := by
  ext i j
  simp only [Matrix.map_apply, Matrix.single_apply]
  split_ifs <;> simp

theorem Bf_Ek {m k : ℕ} (bs : Module.Basis (Fin 2) F E) (J : Matrix (Fin m) (Fin m) E) (X : Mx F E m k)
    (q : Fin m × Fin k × Fin 2) : Bf σ J X (Ek bs q) =
      Algebra.trace (AF F) (AE F E) ((∑ p, X p q.2.1 * incM F J p q.1) * cA σ ((1 : AF F) ⊗ₜ[F] bs q.2.2)) := by
  unfold Bf Ek
  rw [map_single', trace_mul_single']
  simp [Matrix.mul_apply, Matrix.transpose_apply]

theorem Bf_col {m k k' : ℕ} (bs : Module.Basis (Fin 2) F E) (J : Matrix (Fin m) (Fin m) E) (X : Mx F E m k)
    (X' : Mx F E m k') (a : Fin m) (c : Fin k) (c' : Fin k') (t : Fin 2) (hX : ∀ p, X p c = X' p c') :
    Bf σ J X (Ek bs (a, c, t)) = Bf σ J X' (Ek bs (a, c', t)) := by
  simp only [Bf_Ek, hX]

theorem Bf_zero_col {m k : ℕ} (bs : Module.Basis (Fin 2) F E) (J : Matrix (Fin m) (Fin m) E) (X : Mx F E m k)
    (a : Fin m) (c : Fin k) (t : Fin 2) (hX : ∀ p, X p c = 0) : Bf σ J X (Ek bs (a, c, t)) = 0 := by
  rw [Bf_Ek]
  simp [hX]

theorem crdB_col {m k k' : ℕ} (bs : Module.Basis (Fin 2) F E) (X : Mx F E m k) (X' : Mx F E m k') (a : Fin m)
    (c : Fin k) (c' : Fin k') (t : Fin 2) (hX : X a c = X' a c') : crdB bs X (a, c, t) = crdB bs X' (a, c', t) := by
  simp only [crdB, hX]

theorem crdB_zero_col {m k : ℕ} (bs : Module.Basis (Fin 2) F E) (X : Mx F E m k) (a : Fin m) (c : Fin k) (t : Fin 2)
    (hX : X a c = 0) : crdB bs X (a, c, t) = 0 := by
  simp [crdB, hX]

theorem extend_zero_embedded_column {m n N : ℕ} (h : n + 1 = N) (X : Mx F E m n) (p : Fin m) (j : Fin n) : ext0 h X p (em0 h j) = X p j := by
  simp [ext0, em0]

theorem extend_zero_last_column {m n N : ℕ} (h : n + 1 = N) (X : Mx F E m n) (p : Fin m) : ext0 h X p (i0 h) = 0 := by
  simp [ext0, i0]

end PositivityTheory.SiegelWeilFormula.Ald

end
