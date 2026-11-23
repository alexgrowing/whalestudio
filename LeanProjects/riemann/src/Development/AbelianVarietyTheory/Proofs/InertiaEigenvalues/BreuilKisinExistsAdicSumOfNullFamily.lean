import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

noncomputable section

namespace GlobalTheory.BSP

theorem TopBasis.exists_sum_of_null {S A : Type} [CommRing S] [CommRing A] {s : S →+* A} {I : Ideal S}
    {ι : Type} (TB : TopBasis s I ι) (σ : ι → S) (hσ : ∀ n : ℕ, {i | σ i ∉ I ^ n}.Finite) :
    ∃ L : A, ∀ n : ℕ, ∃ F : Finset ι, ∀ G : Finset ι, F ⊆ G →
      L - ∑ i ∈ G, s (σ i) * TB.b i ∈ (I ^ n).map s := by
  classical
  let F : ℕ → Finset ι := fun n => (hσ n).toFinset
  have memF : ∀ n i, i ∈ F n ↔ σ i ∉ I ^ n := fun n i => by simp [F]
  have tail : ∀ m (G : Finset ι), F m ⊆ G →
      ∑ i ∈ G, s (σ i) * TB.b i - ∑ i ∈ F m, s (σ i) * TB.b i ∈ (I ^ m).map s := by
    intro m G hG
    rw [← Finset.sum_sdiff_eq_sub hG]
    refine Ideal.sum_mem _ fun i hi => Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ?_)
    have h : i ∉ F m := (Finset.mem_sdiff.1 hi).2
    rw [memF] at h
    exact not_not.1 h
  have mono : ∀ {m n : ℕ}, m ≤ n → F m ⊆ F n := fun {m n} h i hi => by
    rw [memF] at hi ⊢
    exact fun h' => hi (Ideal.pow_le_pow_right h h')
  have key : ∀ (n : ℕ) (x : A), x ∈ ((I.map s) ^ n • ⊤ : Submodule A A) ↔ x ∈ (I ^ n).map s := by
    intro n x
    rw [smul_eq_mul, Ideal.mul_top, Ideal.map_pow]
  obtain ⟨L, hL⟩ := TB.complete.toIsPrecomplete.prec (f := fun n => ∑ i ∈ F n, s (σ i) * TB.b i)
    (fun {m n} hmn => by
      rw [SModEq.sub_mem, key, ← neg_sub]
      exact neg_mem (tail m (F n) (mono hmn)))
  refine ⟨L, fun n => ⟨F n, fun G hG => ?_⟩⟩
  have h1 := hL n
  rw [SModEq.sub_mem, key] at h1
  have h2 := tail n G hG
  have e : L - ∑ i ∈ G, s (σ i) * TB.b i =
      -((∑ i ∈ F n, s (σ i) * TB.b i - L) + (∑ i ∈ G, s (σ i) * TB.b i - ∑ i ∈ F n, s (σ i) * TB.b i)) := by
    ring
  rw [e]
  exact neg_mem (add_mem h1 h2)

theorem exists_sum_null_ev : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (ι : Type)
    (TB : TopBasis bk.ev bk.J ι) (σ : ι → bk.S), (∀ n : ℕ, {i | σ i ∉ bk.J ^ n}.Finite) →
    ∃ L : Ainf l, ∀ n : ℕ, ∃ F : Finset ι, ∀ G : Finset ι, F ⊆ G →
      L - ∑ i ∈ G, bk.ev (σ i) * TB.b i ∈ (bk.J ^ n).map bk.ev :=
  fun _ _ _ _ _ TB σ hσ => TB.exists_sum_of_null σ hσ

end GlobalTheory.BSP
