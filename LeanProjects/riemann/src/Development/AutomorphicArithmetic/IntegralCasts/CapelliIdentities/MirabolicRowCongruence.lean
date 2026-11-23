import Mathlib

theorem UpperTheory.mirabolic_row_congruence :
    ∀ {R : Type} [CommRing R] (I J : Ideal R) (g : GL (Fin 2) R), I ≤ J →
        Matrix.vecMul ![0, 1] ((Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk I) g : GL (Fin 2) (R ⧸ I)) : Matrix (Fin 2) (Fin 2) (R ⧸ I)) = ![0, 1] →
        Matrix.vecMul ![0, 1] ((Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk J) g : GL (Fin 2) (R ⧸ J)) : Matrix (Fin 2) (Fin 2) (R ⧸ J)) = ![0, 1] := by
  intro R _ I J g hIJ h
  have key : ∀ (K : Ideal R) (j : Fin 2),
      Matrix.vecMul ![0, 1] ((Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk K) g :
        GL (Fin 2) (R ⧸ K)) : Matrix (Fin 2) (Fin 2) (R ⧸ K)) j
        = Ideal.Quotient.mk K ((g : Matrix (Fin 2) (Fin 2) R) 1 j) := by
    intro K j
    simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two, Matrix.GeneralLinearGroup.map]
  funext j
  have hj := congrArg (Ideal.Quotient.factor hIJ) ((key I j).symm.trans (congrFun h j))
  rw [Ideal.Quotient.factor_mk] at hj
  rw [key J j, hj]
  fin_cases j <;> simp
