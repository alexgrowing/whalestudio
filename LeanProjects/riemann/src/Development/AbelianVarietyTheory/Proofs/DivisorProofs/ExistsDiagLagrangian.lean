import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReindexDblIncM
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LagrInt
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

noncomputable section

namespace GlobalTheory.WeilSchrodinger.DiagLagr

def fold (n : ℕ) (i : Fin (n + n)) : Fin n := Sum.elim id id (finSumFinEquiv.symm i)

theorem diagCols_mul {A : Type} [CommRing A] {n m : ℕ} (u : Matrix (Fin n) (Fin m) A) :
    ((diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) A).submatrix finSumFinEquiv.symm id) * u =
      u.submatrix (fold n) id := by
  ext i j
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  rcases i with i | i <;>
    simp only [Matrix.mul_apply, Matrix.submatrix_apply, fold, Equiv.symm_apply_apply] <;>
    simp [diagCols, Matrix.one_apply]

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem hTens_fold (σ : E →ₐ[F] E) {n m : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (JB : Matrix (Fin m) (Fin m) (AF F ⊗[F] E)) (u v : Matrix (Fin n) (Fin m) (AF F ⊗[F] E)) :
    hTens (cA σ) (incM F (GlobalTheory.WeilSchrodinger.DblTargetF.dblG J)ᵀ) JB (u.submatrix (fold n) id)
      (v.submatrix (fold n) id) = 0 := by
  simp only [hTens, ← finSumFinEquiv.sum_comp, Fintype.sum_sum_type, Matrix.submatrix_apply, fold,
    GlobalTheory.WeilSchrodinger.DblTargetF.dblG, incM, Matrix.map_apply, Matrix.transpose_apply, Matrix.reindex_apply,
    Equiv.symm_apply_apply, id]
  simp [dbl]

def repL (F : Type) [Field F] [NumberField F] [Algebra F E] (n m : ℕ) :
    Matrix (Fin n) (Fin m) E →ₗ[F] Matrix (Fin (n + n)) (Fin m) (AF F ⊗[F] E) where
  toFun x := (incM F x).submatrix (fold n) id
  map_add' x y := by ext i j; simp [incM]
  map_smul' a x := by
    ext i j
    simp [incM, inclR, TensorProduct.tmul_smul]

theorem repL_injective (n m : ℕ) : Function.Injective (repL (E := E) F n m) := by
  intro x y h
  have : Nontrivial (AF F) :=
    (NumberField.AdeleRing.algebraMap_injective (NumberField.RingOfIntegers F) F).nontrivial
  have hi : Function.Injective (inclR (F := F) (E := E) (AF F)) := by
    have : Nontrivial (AF F ⊗[F] E) :=
      (Algebra.TensorProduct.includeLeft_injective (R := F) (S := F) (A := AF F) (B := E)
        (algebraMap F E).injective).nontrivial
    exact RingHom.injective _
  ext i j
  have := congrFun (congrFun h (finSumFinEquiv (Sum.inl i))) j
  simp only [repL, LinearMap.coe_mk, AddHom.coe_mk, Matrix.submatrix_apply, fold, Equiv.symm_apply_apply, incM,
    Matrix.map_apply, Sum.elim_inl, id] at this
  exact hi this

theorem exists_diag_lagrangian : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (nS nT : ℕ) (JT : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E)
    (κ : Type) [Fintype κ]
    (co : Darboux (symp (cA σ) ξ (incM F (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)ᵀ) (incM F JB)) κ),
    (∀ x : Matrix (Fin (nT + nT)) (Fin nS) E, ∃ y z : κ → F,
      co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
    ∃ L : Submodule F ((κ → F) × (κ → F)), (∀ a ∈ L, ∀ b ∈ L, a.1 ⬝ᵥ b.2 = b.1 ⬝ᵥ a.2) ∧
      Module.finrank F L = Fintype.card κ ∧
      ∀ (t : AF F), ∀ w ∈ L, ∃ u : Matrix (Fin nT) (Fin nS) (AF F ⊗[F] E),
        co.e (((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id) * u) = t • ((fun i => algebraMap F (AF F) (w.1 i)), (fun i => algebraMap F (AF F) (w.2 i))) := by
  intro F E _ _ _ _ _ σ nS nT JT JB ξ κ _ co hrat
  have hinj := NumberField.AdeleRing.algebraMap_injective (NumberField.RingOfIntegers F) F
  have : Nontrivial (AF F) := hinj.nontrivial
  let i1 : (κ → F) →ₗ[F] (κ → AF F) := (Algebra.linearMap F (AF F)).compLeft κ
  let ι : ((κ → F) × (κ → F)) →ₗ[F] ((κ → AF F) × (κ → AF F)) := i1.prodMap i1
  have hι : ∀ w, ι w = ((fun i => algebraMap F (AF F) (w.1 i)), (fun i => algebraMap F (AF F) (w.2 i))) :=
    fun _ => rfl
  have hιi : Function.Injective ι := by
    intro a b h
    rw [hι, hι, Prod.mk.injEq] at h
    exact Prod.ext (funext fun i => hinj (congrFun h.1 i)) (funext fun i => hinj (congrFun h.2 i))
  let g : Matrix (Fin nT) (Fin nS) E →ₗ[F] ((κ → AF F) × (κ → AF F)) :=
    (co.e.toLinearMap.restrictScalars F) ∘ₗ repL F nT nS
  have hg : ∀ x, g x = co.e ((incM F x).submatrix (fold nT) id) := fun _ => rfl
  have hgi : Function.Injective g := co.e.injective.comp (repL_injective nT nS)
  have hle : LinearMap.range g ≤ LinearMap.range ι := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨y, z, h⟩ := hrat (x.submatrix (fold nT) id)
    exact ⟨(y, z), h.symm⟩
  refine ⟨(LinearMap.range g).comap ι, ?_, ?_, ?_⟩
  · rintro a ⟨x, hx⟩ b ⟨x', hx'⟩
    have h := co.form ((incM F x).submatrix (fold nT) id) ((incM F x').submatrix (fold nT) id)
    rw [symp, hTens_fold, mul_zero, map_zero, ← hg, ← hg, hx, hx', hι, hι, eq_comm, sub_eq_zero] at h
    apply hinj
    simpa only [dotProduct, map_sum, map_mul] using h
  · have : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
    have h1 : Module.finrank F ((LinearMap.range g).comap ι) = nT * nS * Module.finrank F E := by
      rw [(Submodule.equivMapOfInjective ι hιi _).finrank_eq, Submodule.map_comap_eq_of_le hle,
        LinearMap.finrank_range_of_inj hgi, Module.finrank_matrix]
      simp
    have h2 := co.e.finrank_eq
    rw [Module.finrank_matrix, Module.finrank_baseChange, Module.finrank_prod, Module.finrank_fintype_fun_eq_card] at h2
    simp only [Fintype.card_fin] at h2
    rw [h1]
    nlinarith [h2]
  · rintro t w ⟨x, hx⟩
    refine ⟨t • incM F x, ?_⟩
    rw [← hι, ← hx, hg, diagCols_mul, ← map_smul]
    rfl

end GlobalTheory.WeilSchrodinger.DiagLagr

end
