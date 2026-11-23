import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsConstAlongSingleton
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CTSubmatrixMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoeffOfMemColSpan
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet
open scoped TensorProduct

namespace GlobalTheory.TieStd

theorem exists_coeff_of_mem_colSpan {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {n r s : ℕ} (hs : s ≤ r) (X : Matrix (Fin n) (Fin r) E) (I : Set (Fin r)) (P : Fin s → Prop)
    (hI : ∀ i ∈ I, ∃ j, Fin.castLE hs j = i ∧ P j) {y : Fin n → AF F ⊗[F] E}
    (hy : y ∈ GlobalTheory.StdPar.colSpan F X I) :
    ∃ a : Fin s → AF F ⊗[F] E, (∀ j, ¬ P j → a j = 0) ∧ adMat F (X.submatrix id (Fin.castLE hs)) *ᵥ a = y := by
  first
  | exact @_root_.GlobalTheory.ColumnSpanCoefficients.exists_coeff_of_mem_colSpan
  | exact _root_.GlobalTheory.ColumnSpanCoefficients.exists_coeff_of_mem_colSpan
  | (apply _root_.GlobalTheory.ColumnSpanCoefficients.exists_coeff_of_mem_colSpan <;> assumption)
  | (intros; apply _root_.GlobalTheory.ColumnSpanCoefficients.exists_coeff_of_mem_colSpan <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ColumnSpanCoefficients.exists_coeff_of_mem_colSpan <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ColumnSpanCoefficients.exists_coeff_of_mem_colSpan ..)

theorem unip_le_unipFlag : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y → ∀ (S : Finset (Fin r)) (s : ℕ) (hs : s ≤ r), (∀ i : Fin r, i.val < s ↔ ∃ k ∈ S, i ≤ k) → ∀ d : Fin s → ℕ, (∀ i, d i = (S.filter (· < Fin.castLE hs i)).card) → GlobalTheory.StdPar.unip σ J X S ≤ GlobalTheory.UAut.unipFlag σ J (X.submatrix id (Fin.castLE hs)) d := by
  intro F E _ _ _ _ _ σ _ n J _ r X Y _ S s hs hS d hd g hg
  refine Subgroup.subset_closure (?_ : g ∈ GlobalTheory.UAut.unipSet σ J (X.submatrix id (Fin.castLE hs)) d)
  have hlt : ∀ i : Fin r, (∃ k ∈ S, i ≤ k) → ∃ j : Fin s, Fin.castLE hs j = i :=
    fun i h => ⟨⟨i.val, (hS i).2 h⟩, rfl⟩
  refine ⟨fun i => ?_, fun x hx => ?_⟩
  · have h1 := (Subgroup.mem_iInf.1 hg.1 (Fin.castLE hs i)).2 _ (Submodule.subset_span ⟨Fin.castLE hs i, rfl, rfl⟩)
    obtain ⟨a, ha, e⟩ := exists_coeff_of_mem_colSpan hs X {i' | ∃ k ∈ S, i' ≤ k ∧ k < Fin.castLE hs i} (fun j => d j < d i) (fun i' ⟨k, hk, h1, h2⟩ => by
      obtain ⟨j, rfl⟩ := hlt i' ⟨k, hk, h1⟩
      exact ⟨j, rfl, (depth_lt_iff S s hs d hd i j).2 ⟨k, hk, h1, h2⟩⟩) h1
    refine ⟨a, fun j hj => ha j (not_lt.2 hj), ?_⟩
    rw [sub_mulVec, one_mulVec, e]
    rfl
  · have hp : (fun i => inclR (F := F) (AF F) (x i)) ∈ GlobalTheory.StdPar.colPerp σ J X {i | ∃ k ∈ S, i ≤ k} := by
      simp only [GlobalTheory.StdPar.colPerp, Submodule.mem_iInf, LinearMap.mem_ker]
      intro i hi
      obtain ⟨j, rfl⟩ := hlt i hi
      refine (RingHom.map_mulVec (inclR (F := F) (AF F)) _ x (Fin.castLE hs j)).symm.trans ?_
      rw [show ((Formalism.UG.cT (σ : E →+* E) X * J) *ᵥ x) (Fin.castLE hs j) =
        ((Formalism.UG.cT (σ : E →+* E) (X.submatrix id (Fin.castLE hs)) * J) *ᵥ x) j from rfl, hx]
      exact map_zero _
    obtain ⟨a, -, e⟩ := exists_coeff_of_mem_colSpan hs X _ (fun _ => True)
      (fun i' h => let ⟨j, hj⟩ := hlt i' h; ⟨j, hj, trivial⟩) (hg.2.2 _ hp)
    exact ⟨a, by rw [sub_mulVec, one_mulVec, e]⟩

end GlobalTheory.TieStd
