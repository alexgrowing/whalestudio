import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SigmaFiniteParameterProductMeasure
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.ColumnSplitting
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.CompanionTheory.ColumnSplitting.JnM

variable {D : D7} {a b r t n : ℕ}

theorem fromCols_mul_shear {R : Type} [Ring R] (w : Matrix (Fin a) (Fin r) R) (v : Matrix (Fin a) (Fin t) R)
    (y : Matrix (Fin r) (Fin t) R) :
    (Matrix.fromCols w v : Matrix (Fin a) (Fin r ⊕ Fin t) R) *
        (Matrix.fromBlocks 1 y 0 1 : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) R) =
      Matrix.fromCols w (w * y + v) := by
  ext i (k | k) <;> simp [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]

theorem mm_jn (hn : r + t = n) (A : Mx D b a) (x : Mx D a r) (v : Mx D a t) :
    mm A (jn hn x v) = jn hn (mm A x) (mm A v) := by
  ext i j
  simp only [jn, mm, Matrix.submatrix_apply, id, Matrix.mul_apply]
  rcases h : (finSumFinEquiv.trans (finCongr hn)).symm j with k | k <;>
    simp [Matrix.mul_apply]

theorem jn_add (hn : r + t = n) (x x' : Mx D a r) (v v' : Mx D a t) :
    jn hn x v + jn hn x' v' = jn hn (x + x') (v + v') := by
  ext i j
  simp only [jn, Matrix.add_apply, Matrix.submatrix_apply, id]
  rcases h : (finSumFinEquiv.trans (finCongr hn)).symm j with k | k <;> simp

theorem jn_c {W : HSp D} (hn : W.rank + t = n) (U : Mx D a n) :
    jn hn (c1 hn U) (c2 hn U) = U := by
  ext i j
  obtain ⟨s, rfl⟩ := (finSumFinEquiv.trans (finCongr hn)).surjective j
  rcases s with k | k <;> simp [jn, c1, c2]

theorem shear_gen {R : Type} [Ring R] (hn : r + t = n) (w : Matrix (Fin a) (Fin r) R)
    (v : Matrix (Fin a) (Fin t) R) (y : Matrix (Fin r) (Fin t) R) :
    ((Matrix.fromCols w v).submatrix id (finSumFinEquiv.trans (finCongr hn)).symm : Matrix (Fin a) (Fin n) R) *
        ((Matrix.fromBlocks 1 y 0 1).submatrix (finSumFinEquiv.trans (finCongr hn)).symm
          (finSumFinEquiv.trans (finCongr hn)).symm : Matrix (Fin n) (Fin n) R) =
      (Matrix.fromCols w (w * y + v)).submatrix id (finSumFinEquiv.trans (finCongr hn)).symm := by
  rw [Matrix.submatrix_mul_equiv, fromCols_mul_shear]

theorem jn_bl (hn : r + t = n) (w : Mx D a r) (v : Mx D a t) (y : Mx D r t) :
    mm (jn hn w v) (bl hn 1 y 0 1) = jn hn w (mm w y + v) :=
  shear_gen hn w v y

end GlobalTheory.CompanionTheory.ColumnSplitting.JnM

namespace GlobalTheory.CompanionTheory.ColumnSplitting

theorem jnPi_holds : JnPi := by
  intro D n t B W d hn x₀ g p
  obtain ⟨h, U, y⟩ := p
  have hX : XU d hn x₀ h U =
      jn hn (mm d.jX (c1 hn U) + mm d.j0 (ww W x₀ h)) (mm d.jX (c2 hn U)) := by
    unfold XU
    conv_lhs => rw [← JnM.jn_c (W := W) hn U]
    have h0 : mm d.j0 (0 : Mx D W.rank t) = 0 := Matrix.mul_zero _
    rw [JnM.mm_jn, JnM.mm_jn, JnM.jn_add, h0, add_zero]
  simp only [hX, JnM.jn_bl, JnM.mm_jn]
  rfl

end GlobalTheory.CompanionTheory.ColumnSplitting

end
