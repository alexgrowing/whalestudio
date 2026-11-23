import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReindexDblIncM
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeltaTApply
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.DiagEmbU

section Gen

variable {A : Type} [CommRing A] {n : ℕ}

def dg (M : Matrix (Fin n) (Fin n) A) : Matrix (Fin (n + n)) (Fin (n + n)) A :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks M 0 0 1)

theorem dg_mul (M N : Matrix (Fin n) (Fin n) A) : dg (M * N) = dg M * dg N := by
  simp only [dg, Matrix.reindex_apply, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
  simp

theorem dg_one : dg (1 : Matrix (Fin n) (Fin n) A) = 1 := by
  simp [dg, Matrix.fromBlocks_one]

theorem dg_sub_one_apply (M : Matrix (Fin n) (Fin n) A) (i j : Fin (n + n)) :
    (dg M - 1) i j = Sum.elim (fun a => Sum.elim (fun b => (M - 1) a b) (fun _ => 0)) (fun _ _ => 0)
      (finSumFinEquiv.symm i) (finSumFinEquiv.symm j) := by
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
  rw [← dg_one]
  rcases i with a | a <;> rcases j with b | b <;> simp only [dg, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.map_apply, Matrix.transpose_apply, Matrix.sub_apply, Formalism.UG.cT] <;> simp

theorem det_dg (M : Matrix (Fin n) (Fin n) A) : (dg M).det = M.det := by
  rw [dg, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, mul_one]

theorem continuous_dg [TopologicalSpace A] : Continuous (dg (A := A) (n := n)) :=
  (Continuous.matrix_fromBlocks continuous_id continuous_const continuous_const continuous_const).matrix_reindex _ _

def dgHom : Matrix (Fin n) (Fin n) A →* Matrix (Fin (n + n)) (Fin (n + n)) A where
  toFun := dg
  map_one' := dg_one
  map_mul' := dg_mul

def diagGL : GL (Fin n) A →* GL (Fin (n + n)) A := Units.map (dgHom (A := A) (n := n))

theorem continuous_diagGL [TopologicalSpace A] : Continuous (diagGL (A := A) (n := n)) :=
  Continuous.units_map _ continuous_dg

theorem dg_map {B : Type} [CommRing B] (φ : A →+* B) (M : Matrix (Fin n) (Fin n) A) :
    (dg M).map φ = dg (M.map φ) := by
  ext i j
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
  rcases i with a | a <;> rcases j with b | b <;> simp only [dg, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.map_apply, Matrix.transpose_apply, Matrix.sub_apply, Formalism.UG.cT] <;> simp [Matrix.one_apply]

theorem bc_diagGL {B : Type} [CommRing B] (φ : A →+* B) (g : GL (Fin n) A) :
    Formalism.UG.bc φ (diagGL g) = diagGL (Formalism.UG.bc φ g) := by
  ext : 1
  exact dg_map φ _

theorem cT_dg (s : A →+* A) (M : Matrix (Fin n) (Fin n) A) :
    Formalism.UG.cT s (dg M) = Matrix.reindex finSumFinEquiv finSumFinEquiv
      (Matrix.fromBlocks (Formalism.UG.cT s M) 0 0 1) := by
  ext i j
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
  rcases i with a | a <;> rcases j with b | b <;> simp only [dg, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.map_apply, Matrix.transpose_apply, Matrix.sub_apply, Formalism.UG.cT] <;> simp [Matrix.one_apply, eq_comm]

theorem diagGL_mem (s : A →+* A) (J K : Matrix (Fin n) (Fin n) A) {g : GL (Fin n) A}
    (hg : g ∈ Formalism.UG.UJ s J) :
    diagGL g ∈ Formalism.UG.UJ s (Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks J 0 0 K)) := by
  have hg' : Formalism.UG.cT s (g : Matrix (Fin n) (Fin n) A) * J * (g : Matrix (Fin n) (Fin n) A) = J := hg
  show Formalism.UG.cT s (dg (g : Matrix (Fin n) (Fin n) A)) * _ * dg (g : Matrix (Fin n) (Fin n) A) = _
  rw [cT_dg, dg]
  simp only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
  simp [hg']

end Gen

end GlobalTheory.DiagEmbU

namespace GlobalTheory.DiagEmbU

open GlobalTheory.WeilSchrodinger.DblTarget

section Main

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem JR_dblG (R : Type) [CommRing R] [Algebra F R] {n : ℕ} (J : Matrix (Fin n) (Fin n) E) :
    JR (F := F) R (GlobalTheory.WeilSchrodinger.DblTargetF.dblG J) =
      Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks (JR (F := F) R J) 0 0 (-JR (F := F) R J)) := by
  ext i j
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
  rcases i with a | a <;> rcases j with b | b <;>
    simp only [JR, GlobalTheory.WeilSchrodinger.DblTargetF.dblG, Matrix.reindex_apply, Matrix.submatrix_apply,
      Equiv.symm_apply_apply, Matrix.map_apply] <;> simp [dbl]

theorem dblG_eq {n : ℕ} (J : Matrix (Fin n) (Fin n) E) :
    GlobalTheory.WeilSchrodinger.DblTargetF.dblG J =
      Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks J 0 0 (-J)) := rfl

def diagU (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) :
    Formalism.IndefR.DatumF.GAF σ J →* Formalism.IndefR.DatumF.GAF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG J) :=
  ((diagGL (A := AF F ⊗[F] E)).comp (Formalism.IndefR.DatumF.matHomF σ J)).codRestrict
    (HR (AF F) σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG J)) fun g => by
      have hg : (show HR (AF F) σ J from g).1 ∈ Formalism.UG.UJ (sigR (AF F) σ) (JR (F := F) (AF F) J) :=
        (show HR (AF F) σ J from g).2
      have := diagGL_mem (sigR (AF F) σ) (JR (F := F) (AF F) J) (-JR (F := F) (AF F) J) hg
      show _ ∈ Formalism.UG.UJ (sigR (AF F) σ) (JR (F := F) (AF F) (GlobalTheory.WeilSchrodinger.DblTargetF.dblG J))
      rw [JR_dblG]
      exact this

theorem mtF_diagU (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (h : Formalism.IndefR.DatumF.GAF σ J) :
    Formalism.IndefR.DatumF.mtF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG J) (diagU σ J h) =
      dg (Formalism.IndefR.DatumF.mtF σ J h) := rfl

end Main

end GlobalTheory.DiagEmbU

namespace GlobalTheory.DiagEmbU

open GlobalTheory.WeilSchrodinger.DblTarget

theorem exists_diagEmb : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (n : ℕ) (J : Matrix (Fin n) (Fin n) E),
      ∃ ι : Formalism.IndefR.DatumF.GAF σ J →* Formalism.IndefR.DatumF.GAF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG J),
        Continuous ι ∧
        (∀ h, Formalism.IndefR.DatumF.mtF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG J) (ι h) =
          Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks (Formalism.IndefR.DatumF.mtF σ J h) 0 0 1)) ∧
        (∀ γ ∈ Formalism.IndefR.DatumF.GQF σ J, ι γ ∈ Formalism.IndefR.DatumF.GQF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG J)) ∧
        (∀ e h, Formalism.IndefR.DatumF.SuppAtF σ e J h → Formalism.IndefR.DatumF.SuppAtF σ e (GlobalTheory.WeilSchrodinger.DblTargetF.dblG J) (ι h)) ∧
        (∀ e h y, Formalism.IndefR.DatumF.IsDetAtF σ e J h y →
          Formalism.IndefR.DatumF.IsDetAtF σ e (GlobalTheory.WeilSchrodinger.DblTargetF.dblG J) (ι h) y) := by
  intro F E _ _ _ _ _ σ n J
  refine ⟨diagU σ J, ?_, fun h => mtF_diagU σ J h, ?_, ?_, ?_⟩
  · exact Continuous.subtype_mk (continuous_diagGL.comp continuous_subtype_val) _
  · intro γ hγ
    have h1 : (show HR (AF F) σ J from γ).1 ∈ HFin (AF F) σ J := Subgroup.mem_subgroupOf.mp hγ
    obtain ⟨γ₀, hγ₀, he⟩ := Subgroup.mem_map.mp h1
    refine Subgroup.mem_subgroupOf.mpr (Subgroup.mem_map.mpr ⟨diagGL γ₀, ?_, ?_⟩)
    · rw [dblG_eq]
      exact diagGL_mem _ J (-J) hγ₀
    · rw [bc_diagGL, he]
      rfl
  · intro e h hs i j
    rw [mtF_diagU]
    obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
    obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
    rw [dg_sub_one_apply]
    rcases i with a | a <;> rcases j with b | b <;> simp only [Equiv.symm_apply_apply, Sum.elim_inl, Sum.elim_inr, mul_zero]
    exact hs a b
  · intro e h y hy
    show (y : Formalism.IndefR.DatumF.AEF F E) = e * (Formalism.IndefR.DatumF.mtF σ _ (diagU σ J h)).det + (1 - e)
    rw [mtF_diagU, det_dg]
    exact hy

end GlobalTheory.DiagEmbU
