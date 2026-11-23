import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DgMatOne
import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.CtLevel
open scoped Classical TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT.CtLevel

theorem blockDiagonalMatrixOfAddEq_entries_mem_subring {R : Type} [CommRing R] (O : Subring R) {a b n : ℕ} (h : a + b = n)
    (A : Matrix (Fin a) (Fin a) R) (D : Matrix (Fin b) (Fin b) R)
    (hA : ∀ i j, A i j ∈ O) (hD : ∀ i j, D i j ∈ O) (i j : Fin n) : dgMat h A D i j ∈ O := by
  simp only [dgMat, reindex_apply, submatrix_apply]
  rcases (blkEq h).symm i with i' | i' <;> rcases (blkEq h).symm j with j' | j' <;>
    simp [fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂, hA, hD, O.zero_mem]

theorem det_mem_subring_of_entries_mem_fin {R : Type} [CommRing R] (O : Subring R) {m : ℕ} (A : Matrix (Fin m) (Fin m) R)
    (hA : ∀ i j, A i j ∈ O) : A.det ∈ O := by
  rw [Matrix.det_apply']
  exact O.sum_mem fun σ _ => O.mul_mem (intCast_mem O _) (O.prod_mem fun i _ => hA _ _)

theorem one_matrix_apply_mem_subring {R : Type} [CommRing R] (O : Subring R) {m : ℕ} (i j : Fin m) :
    (1 : Matrix (Fin m) (Fin m) R) i j ∈ O := by
  rw [Matrix.one_apply]; split_ifs
  · exact O.one_mem
  · exact O.zero_mem

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem character_det_integralGL_eq_one_of_unramified (w : Pl E) (μ : (w.adicCompletion E)ˣ →* ℂˣ)
    (hμ : ∀ u ∈ GlobalTheory.LFun.KGL w 1, μ (GeneralLinearGroup.det u) = 1) {m : ℕ} (k : GLw m w)
    (hk : k ∈ GlobalTheory.LFun.KGL w m) : μ (GeneralLinearGroup.det k) = 1 := by
  set d := GeneralLinearGroup.det k
  let u : GL (Fin 1) (w.adicCompletion E) := Units.map (Matrix.scalar (Fin 1)).toMonoidHom d
  have hu : GeneralLinearGroup.det u = d := by
    ext; simp [u]
  rw [← hu]
  apply hμ
  obtain ⟨h1, h2⟩ := GlobalTheory.AdelicU.mem_GLint_iff.1 hk
  refine GlobalTheory.AdelicU.mem_GLint_iff.2 ⟨fun i j => ?_, fun i j => ?_⟩
  · have : (u : Matrix (Fin 1) (Fin 1) _) i j = (k.val).det := by
      simp [u, d, Subsingleton.elim i j]
    rw [this]; exact det_mem_subring_of_entries_mem_fin _ _ h1
  · have : (u⁻¹ : GL (Fin 1) _).val i j = (k⁻¹ : GLw m w).val.det := by
      simp [u, d, Subsingleton.elim i j, ← map_inv]
    rw [this]; exact det_mem_subring_of_entries_mem_fin _ _ h2

end GlobalTheory.BCT.CtLevel

namespace GlobalTheory.BCT.CtLevel

theorem lev_KGL_of_unram : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b n : ℕ) (h : a + b = n)
    (w : Pl E) (μ : (w.adicCompletion E)ˣ →* ℂˣ), (∀ u ∈ GlobalTheory.LFun.KGL w 1, μ (GeneralLinearGroup.det u) = 1) →
    lev₁ h w (GlobalTheory.LFun.KGL w n) μ = GlobalTheory.LFun.KGL w a ∧ lev₂ h w (GlobalTheory.LFun.KGL w n) μ = GlobalTheory.LFun.KGL w b := by
  intro E _ _ _ a b n h w μ hμ
  constructor
  · refine le_antisymm (fun x hx => hx.1.1) fun k hk => ⟨⟨hk, ?_⟩, character_det_integralGL_eq_one_of_unramified w μ hμ k hk⟩
    obtain ⟨h1, h2⟩ := GlobalTheory.AdelicU.mem_GLint_iff.1 hk
    show dgM h w (k, 1) ∈ GlobalTheory.LFun.KGL w n
    refine GlobalTheory.AdelicU.mem_GLint_iff.2 ⟨fun i j => ?_, fun i j => ?_⟩
    · rw [dgM_val]
      exact blockDiagonalMatrixOfAddEq_entries_mem_subring _ h _ _ h1 (one_matrix_apply_mem_subring _) i j
    · rw [← map_inv, dgM_val]
      exact blockDiagonalMatrixOfAddEq_entries_mem_subring _ h _ _ h2 (fun i j => by simpa using one_matrix_apply_mem_subring (Ov E w) i j) i j
  · refine le_antisymm (fun x hx => hx.1.1) fun k hk => ⟨⟨hk, ?_⟩, character_det_integralGL_eq_one_of_unramified w μ hμ k hk⟩
    obtain ⟨h1, h2⟩ := GlobalTheory.AdelicU.mem_GLint_iff.1 hk
    show dgM h w (1, k) ∈ GlobalTheory.LFun.KGL w n
    refine GlobalTheory.AdelicU.mem_GLint_iff.2 ⟨fun i j => ?_, fun i j => ?_⟩
    · rw [dgM_val]
      exact blockDiagonalMatrixOfAddEq_entries_mem_subring _ h _ _ (one_matrix_apply_mem_subring _) h1 i j
    · rw [← map_inv, dgM_val]
      exact blockDiagonalMatrixOfAddEq_entries_mem_subring _ h _ _ (fun i j => by simpa using one_matrix_apply_mem_subring (Ov E w) i j) h2 i j

end GlobalTheory.BCT.CtLevel
