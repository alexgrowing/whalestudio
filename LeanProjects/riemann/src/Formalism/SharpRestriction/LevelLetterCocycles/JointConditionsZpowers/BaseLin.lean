import Mathlib

noncomputable section

namespace Formalism.MainNotions.N

open Matrix

def splitRT (Kf : Type) [Field Kf] (r t : ℕ) : (Fin (r + t) → Kf) ≃ₗ[Kf] ((Fin r → Kf) × (Fin t → Kf)) :=
  (LinearEquiv.funCongrLeft Kf Kf finSumFinEquiv).trans (LinearEquiv.sumArrowLequivProdArrow (Fin r) (Fin t) Kf Kf)

private theorem sumSplitEquiv_apply_lemma (Kf : Type) [Field Kf] (r t : ℕ) (z : Fin (r + t) → Kf) :
    splitRT Kf r t z = (fun i => z (Fin.castAdd t i), fun j => z (Fin.natAdd r j)) := by
  first
  | rfl
  | (refine Prod.ext (funext fun i => ?_) (funext fun j => ?_) <;> simp [splitRT])

theorem splitRT_diag (Kf : Type) [Field Kf] (r t : ℕ) (c : Kf) (z : Fin (r + t) → Kf) :
    splitRT Kf r t ((Matrix.diagonal (fun k : Fin (r + t) => if (k : ℕ) < r then 1 else c)).mulVec z) =
      ((splitRT Kf r t z).1, c • (splitRT Kf r t z).2) := by
  simp only [sumSplitEquiv_apply_lemma]
  refine Prod.ext (funext fun i => ?_) (funext fun j => ?_)
  · simp [Matrix.mulVec_diagonal]
  · simp [Matrix.mulVec_diagonal]

section Block

variable {Γ k : Type} [Group Γ] [Field k] {a b : ℕ}

def blockHom (k : Type) [Field k] (a b : ℕ) :
    Matrix (Fin a) (Fin a) k × Matrix (Fin b) (Fin b) k →* Matrix (Fin (a + b)) (Fin (a + b)) k :=
  ((LinearMap.toMatrixAlgEquiv' : Module.End k (Fin (a + b) → k) ≃ₐ[k] _).toAlgHom.toRingHom.toMonoidHom).comp
    (((splitRT k a b).symm.conjRingEquiv.toRingHom.toMonoidHom).comp
      (((LinearMap.prodMapAlgHom k (Fin a → k) (Fin b → k)).toRingHom.toMonoidHom).comp
        (MonoidHom.prodMap (Matrix.toLinAlgEquiv' : Matrix (Fin a) (Fin a) k ≃ₐ[k] _).toAlgHom.toRingHom.toMonoidHom
          (Matrix.toLinAlgEquiv' : Matrix (Fin b) (Fin b) k ≃ₐ[k] _).toAlgHom.toRingHom.toMonoidHom)))

theorem blockHom_mulVec (A : Matrix (Fin a) (Fin a) k) (B : Matrix (Fin b) (Fin b) k) (u : Fin (a + b) → k) :
    splitRT k a b ((blockHom k a b (A, B)).mulVec u) =
      (A.mulVec (splitRT k a b u).1, B.mulVec (splitRT k a b u).2) := by
  have h1 : blockHom k a b (A, B) = LinearMap.toMatrix'
      ((splitRT k a b).symm.conjRingEquiv ((Matrix.toLin' A).prodMap (Matrix.toLin' B))) := rfl
  rw [h1, LinearMap.toMatrix'_mulVec]
  first
  | (change splitRT k a b ((splitRT k a b).symm
        (((Matrix.toLin' A).prodMap (Matrix.toLin' B)) (splitRT k a b u))) = _
     rw [LinearEquiv.apply_symm_apply]
     simp [Matrix.toLin'_apply])
  | (simp [LinearEquiv.conjRingEquiv_apply, LinearEquiv.conj_apply, Matrix.toLin'_apply]; done)

private theorem blockHom_eq_reindex_lemma_2 (A : Matrix (Fin a) (Fin a) k) (B : Matrix (Fin b) (Fin b) k) :
    blockHom k a b (A, B) =
      Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks A 0 0 B) := by
  apply Matrix.toLin'.injective
  refine LinearMap.ext fun u => ?_
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply]
  apply (splitRT k a b).injective
  rw [blockHom_mulVec]
  simp only [sumSplitEquiv_apply_lemma]
  refine Prod.ext (funext fun i => ?_) (funext fun j => ?_)
  · first
    | (simp [Matrix.mulVec, dotProduct, Fin.sum_univ_add]; done)
    | (simp [Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_add]; done)
  · first
    | (simp [Matrix.mulVec, dotProduct, Fin.sum_univ_add]; done)
    | (simp [Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_add]; done)

theorem blockHom_charpoly (A : Matrix (Fin a) (Fin a) k) (B : Matrix (Fin b) (Fin b) k) :
    (blockHom k a b (A, B)).charpoly = A.charpoly * B.charpoly := by
  rw [blockHom_eq_reindex_lemma_2, Matrix.charpoly_reindex, Matrix.charpoly_fromBlocks_zero₁₂]

def blockRep (ρ : Γ →* GL (Fin a) k) (ρ' : Γ →* GL (Fin b) k) : Γ →* GL (Fin (a + b)) k :=
  (Units.map (blockHom k a b)).comp
    ((MulEquiv.prodUnits.symm : _ ≃* (Matrix (Fin a) (Fin a) k × Matrix (Fin b) (Fin b) k)ˣ).toMonoidHom.comp
      (ρ.prod ρ'))

theorem blockRep_coe (ρ : Γ →* GL (Fin a) k) (ρ' : Γ →* GL (Fin b) k) (g : Γ) :
    ((blockRep ρ ρ' g : GL _ _) : Matrix (Fin (a + b)) (Fin (a + b)) k) =
      blockHom k a b ((ρ g : Matrix (Fin a) (Fin a) k), (ρ' g : Matrix (Fin b) (Fin b) k)) := rfl

def diagGL (χ : Fin b → Γ →* kˣ) : Γ →* GL (Fin b) k where
  toFun g := ⟨Matrix.diagonal fun c => ((χ c g : kˣ) : k), Matrix.diagonal fun c => (((χ c g)⁻¹ : kˣ) : k),
    by rw [Matrix.diagonal_mul_diagonal]; simp, by rw [Matrix.diagonal_mul_diagonal]; simp⟩
  map_one' := by
    apply Units.ext
    simp
  map_mul' g h := by
    apply Units.ext
    simp [Matrix.diagonal_mul_diagonal]

end Block

end Formalism.MainNotions.N
