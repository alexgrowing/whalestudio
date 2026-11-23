import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.LtChar
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.PZ GlobalTheory.PMC

namespace GlobalTheory

theorem prod_mem_Fil_zero_of_factors {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K : FinExt l) {ι : Type}
    (s : Finset ι) (x : ι → P.R.BdR) (h : ∀ i ∈ s, x i ∈ (P.PD K).Fil 0) :
    (∏ i ∈ s, x i) ∈ (P.PD K).Fil 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (P.PD K).one_mem
  | insert a t ha ih =>
    rw [Finset.prod_insert ha]
    have h1 := (P.PD K).Fil_mul 0 0 _ _ (h a (Finset.mem_insert_self a t))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
    simpa using h1

theorem prod_degree_of_not_mem_Fil_two : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) {ι : Type} (s : Finset ι) (x : ι → P.R.BdR) (i₀ : ι), i₀ ∈ s →
    (∀ i ∈ s, x i ∈ (P.PD K).Fil 0) → x i₀ ∈ (P.PD K).Fil 1 → (∏ i ∈ s, x i) ∉ (P.PD K).Fil 2 →
    x i₀ ∉ (P.PD K).Fil 2 ∧ ∀ i ∈ s, i ≠ i₀ → x i ∉ (P.PD K).Fil 1 := by
  classical
  intro l _ P K ι s x i₀ hi₀ h0 h1 hprod
  have hrest : (∏ i ∈ s.erase i₀, x i) ∈ (P.PD K).Fil 0 :=
    prod_mem_Fil_zero_of_factors P K _ x fun i hi => h0 i (Finset.mem_of_mem_erase hi)
  refine ⟨fun h2 => hprod ?_, fun i hi hne h1i => hprod ?_⟩
  · rw [← Finset.mul_prod_erase s x hi₀]
    simpa using (P.PD K).Fil_mul 2 0 _ _ h2 hrest
  · have hi' : i ∈ s.erase i₀ := Finset.mem_erase.mpr ⟨hne, hi⟩
    have hrest2 : (∏ j ∈ (s.erase i₀).erase i, x j) ∈ (P.PD K).Fil 0 :=
      prod_mem_Fil_zero_of_factors P K _ x fun j hj =>
        h0 j (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hj))
    have hA : x i * (∏ j ∈ (s.erase i₀).erase i, x j) ∈ (P.PD K).Fil 1 := by
      simpa using (P.PD K).Fil_mul 1 0 _ _ h1i hrest2
    rw [← Finset.mul_prod_erase s x hi₀, ← Finset.mul_prod_erase (s.erase i₀) x hi']
    simpa [one_add_one_eq_two] using (P.PD K).Fil_mul 1 1 _ _ h1 hA

end GlobalTheory
