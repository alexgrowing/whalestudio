import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTransportF
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousUgReindex

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.WeilSchrodinger.DblTargetF

open GlobalTheory.WeilSchrodinger.DblTarget

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def dblG {n : ℕ} (J : Matrix (Fin n) (Fin n) E) : Matrix (Fin (n + n)) (Fin (n + n)) E :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv (dbl J)

theorem isHermND_dblG {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (h : IsHermND σ J) :
    IsHermND σ (dblG J) := by
  refine ⟨fun i j => ?_, ?_⟩
  · obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
    obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
    rcases i with i | i <;> rcases j with j | j <;>
      simp only [dblG, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply] <;>
      simp [dbl, h.1 i j]
  · rw [dblG, Matrix.det_reindex_self, dbl, Matrix.det_fromBlocks_zero₂₁, Matrix.det_neg]
    simp [h.2]

theorem reindex_dbl_incM {n : ℕ} {J JA : Matrix (Fin n) (Fin n) E} (hA : JA = Jᵀ) :
    Matrix.reindex finSumFinEquiv finSumFinEquiv (dbl (incM F JA)) = incM F (dblG J)ᵀ := by
  subst hA
  ext i j
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
  rcases i with i | i <;> rcases j with j | j <;>
    simp only [dblG, incM, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply,
      Matrix.transpose_apply, Matrix.map_apply] <;> simp [dbl]

abbrev coDbl {σ : E →ₐ[F] E} {nS nT : ℕ} {JT JA : Matrix (Fin nT) (Fin nT) E} {JB : Matrix (Fin nS) (Fin nS) E}
    {ξ : AF F ⊗[F] E} (hA : JA = JTᵀ) {κ : Type} [Fintype κ]
    (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ) :
    Darboux (symp (cA σ) ξ (incM F (dblG JT)ᵀ) (incM F JB)) (κ ⊕ κ) :=
  reindexRows finSumFinEquiv (dblRows co) _ (reindex_dbl_incM hA)

theorem coDbl_rat {σ : E →ₐ[F] E} {nS nT : ℕ} {JT JA : Matrix (Fin nT) (Fin nT) E} {JB : Matrix (Fin nS) (Fin nS) E}
    {ξ : AF F ⊗[F] E} (hA : JA = JTᵀ) {κ : Type} [Fintype κ]
    (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ)
    (hrat : ∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : κ → F,
      co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) :
    ∀ x : Matrix (Fin (nT + nT)) (Fin nS) E, ∃ y z : κ ⊕ κ → F,
      (coDbl hA co).e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i)) := by
  intro x
  obtain ⟨y₁, z₁, h₁⟩ := hrat (x.submatrix (finSumFinEquiv ∘ Sum.inl) id)
  obtain ⟨y₂, z₂, h₂⟩ := hrat (x.submatrix (finSumFinEquiv ∘ Sum.inr) id)
  refine ⟨Sum.elim y₁ y₂, Sum.elim z₁ (-z₂), ?_⟩
  have e₁ : ((incM F x).submatrix finSumFinEquiv id).submatrix Sum.inl id =
      incM F (x.submatrix (finSumFinEquiv ∘ Sum.inl) id) := rfl
  have e₂ : ((incM F x).submatrix finSumFinEquiv id).submatrix Sum.inr id =
      incM F (x.submatrix (finSumFinEquiv ∘ Sum.inr) id) := rfl
  rw [coDbl, reindexRows_e, dblRows_e, e₁, e₂, h₁, h₂]
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_) <;> rcases i with i | i <;> simp

theorem isHeckeCharF_one : Formalism.IndefR.DatumF.IsHeckeCharF (1 : (AF F ⊗[F] E)ˣ →* Circle) :=
  ⟨continuous_const, fun _ => rfl⟩

theorem resEtaF_one_dbl (h2 : Module.finrank F E = 2) {χ : (AF F ⊗[F] E)ˣ →* Circle} {n : ℕ}
    (hr : Formalism.IndefR.DatumF.ResEtaF χ n) : Formalism.IndefR.DatumF.ResEtaF (1 : (AF F ⊗[F] E)ˣ →* Circle) (n + n) :=
  ⟨hr.1, fun η hη a => by
    have h4 := hη.2.2.1 (Formalism.IndefR.DatumF.idFF F E a)
    have h5 : Units.map (Algebra.norm (AF F) : AF F ⊗[F] E →* AF F) (Formalism.IndefR.DatumF.idFF F E a) = a ^ 2 :=
      Units.ext (by
        change Algebra.norm (AF F) (algebraMap (AF F) (AF F ⊗[F] E) a.1) = _
        have : Nontrivial (AF F) :=
          (NumberField.AdeleRing.algebraMap_injective (NumberField.RingOfIntegers F) F).nontrivial
        rw [Algebra.norm_algebraMap, Module.finrank_baseChange, h2, Units.val_pow_eq_pow_val])
    rw [h5, map_pow] at h4
    change (1 : Circle) = η a ^ (n + n)
    rw [← two_mul, pow_mul, h4, one_pow]⟩

def ugDbl {σ : E →ₐ[F] E} {n : ℕ} {JT JA : Matrix (Fin n) (Fin n) E} (hA : JA = JTᵀ) :
    UG (cA σ) (dbl (incM F JA)) →* UG (cA σ) (incM F (dblG JT)ᵀ) :=
  ugReindex finSumFinEquiv (reindex_dbl_incM hA)

theorem ugDbl_coe {σ : E →ₐ[F] E} {n : ℕ} {JT JA : Matrix (Fin n) (Fin n) E} (hA : JA = JTᵀ)
    (g : UG (cA σ) (dbl (incM F JA))) :
    (ugDbl hA g).1.1 = Matrix.reindex finSumFinEquiv finSumFinEquiv g.1.1 := rfl

end GlobalTheory.WeilSchrodinger.DblTargetF

end
