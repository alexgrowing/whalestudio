import Formalism.LocalToGlobal.GlobalTheory.BlockActions.BlockActEqBlkRow

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Br

open MvPolynomial Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms Matrix Formalism.UG

variable {D : D7} {u : D.what₂.Word} {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i}

theorem embS_embLL : embS D D.what₂.embLL = embT D := by
  funext τ
  apply RingHom.ext
  intro x
  show D.what₂.embLL (D.embE (D.host.sigmaOf (D.eTau τ : D.R.GG) x)) =
    D.host.φ₀ (D.host.sigmaOf (D.eTau τ : D.R.GG) x)
  rw [← D.embE_φ₀]
  rfl

theorem brOne_gFull (Tf : FormsTiedSym D u Ch chOf) (τ : D.what₂.Tau) (g : GL (Fin (D.R.N D.R.m - 1)) ℂ)
    (f : MvPolynomial (Fin (D.R.N D.R.m) × Fin (D.R.N D.R.m)) ℂ) :
    Formalism.L2.Ker.brOne ℂ (Nm_succ D.R).symm (lamTr D u τ) (sgTr D u τ) (sqAct ℂ _ (lamTr D u τ) (gFull D u g) f) =
      (((sqrtT D u) ^ ((D.fm u).deg τ) : ℂˣ) : ℂ) •
        sqAct ℂ _ (sgTr D u τ) g (Formalism.L2.Ker.brOne ℂ (Nm_succ D.R).symm (lamTr D u τ) (sgTr D u τ) f) := by
  have hI0 := interlaceTr D u (sg_interlace Tf.valP) τ
  have hS := Formalism.L2.Ker.sameShiftTr D u τ hI0
  have hI := (Formalism.L2.Ker.interlace_iff _ _ (Nm_succ D.R)).1 hI0
  unfold gFull
  rw [(factSqActMul ℂ _ _ _ _ f).1, Formalism.L2.Ker.brOne_sqAct _ _ _ hS g _, Formalism.L2.Ker.brOne_last _ _ _ hI _ f, deg_eq_degZ]
  unfold sqAct
  rw [map_smul, smul_comm]

theorem transpose_gFull_eq_dOT_of_eq_transpose (o' : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) ℂ) (g : GL (Fin (D.R.N D.R.m - 1)) ℂ)
    (hg : (g : Matrix _ _ ℂ) = o'ᵀ) : ((gFull D u g : GL (Fin (D.R.N D.R.m)) ℂ) : Matrix _ _ ℂ)ᵀ = dOT u o' := by
  have hl : ((Formalism.MainNotions.PrimeDegreeVariant.lastGL ℂ (D.R.N D.R.m) (sqrtT D u) : GL _ ℂ) : Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m)) ℂ)ᵀ =
      Matrix.reindex (eN D) (eN D) (Matrix.fromBlocks 1 0 0 (Matrix.of fun _ _ => ((sqrtT D u : ℂˣ) : ℂ))) := by
    rw [← lastGL_eq]
    show (Matrix.diagonal _)ᵀ = Matrix.diagonal _
    exact Matrix.diagonal_transpose _
  have he : ((Formalism.MainNotions.PrimeDegreeVariant.embGL ℂ _ _ (Nm_succ D.R) g : GL (Fin (D.R.N D.R.m)) ℂ) : Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m)) ℂ)ᵀ =
      Matrix.reindex (eN D) (eN D) (Matrix.fromBlocks o' 0 0 1) := by
    rw [embGL_val, Matrix.transpose_reindex, Matrix.fromBlocks_transpose, hg, Matrix.transpose_transpose,
      Matrix.transpose_zero, Matrix.transpose_zero, Matrix.transpose_one]
  unfold gFull dOT
  rw [Units.val_mul, Matrix.transpose_mul, hl, he, reindex_mulB, Matrix.fromBlocks_multiply]
  congr 1
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one, Matrix.one_mul]

theorem det_dOT (o' : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) ℂ) :
    (dOT u o').det = o'.det * ((sqrtT D u : ℂˣ) : ℂ) := by
  unfold dOT
  rw [Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁]
  congr 1
  rw [Matrix.det_unique]
  rfl

end Formalism.L2.GlobalTheoryTheory.Br
