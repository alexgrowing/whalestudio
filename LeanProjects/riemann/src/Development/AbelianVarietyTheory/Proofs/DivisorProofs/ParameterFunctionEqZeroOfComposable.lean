import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EllFamNontrivial
import Development.AbelianVarietyTheory.Definitions.Divisors.FstTszeSec

set_option autoImplicit false

open CategoryTheory GlobalTheory.CatCoh GlobalTheory.AnPer GlobalTheory.AnPer.Charts TopologicalSpace

namespace GlobalTheory.AnPer.Charts

theorem exists_composable {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ}
    (K : Charts F) (hK : K.Rich) (l m : Λ) (q : Tot I g) (hq : q.1 ∈ F.V) :
    ∃ k k' k'' : K.K, K.le l k' k ∧ K.le m k'' k' ∧ q ∈ K.W k'' := by
  obtain ⟨hcov, hjoin⟩ := hK
  obtain ⟨k, hk⟩ := hcov (F.shift l (F.shift m q)) hq
  obtain ⟨k₁, hk₁⟩ := hcov (F.shift m q) hq
  obtain ⟨k', hk', -, hlk⟩ := hjoin l k₁ k (F.shift m q) hk₁ hk
  obtain ⟨k₂, hk₂⟩ := hcov q hq
  obtain ⟨k'', hk'', -, hmk⟩ := hjoin m k₂ k' q hk₂ hk'
  exact ⟨k, k', k'', hlk, hmk, hk''⟩

theorem eq_zero_of_cst_composable : ∀ {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ}
    (K : Charts F), K.Rich → ∀ (l m : Λ) (p : Hol F.V),
    (∀ (k k' k'' : K.K), K.le l k' k → K.le m k'' k' → K.cst k'' p = 0) → p = 0 := by
  intro I _ g Λ _ F K hK l m p hp
  apply Hol.ext_fn
  intro z hz
  obtain ⟨k, k', k'', h1, h2, hq⟩ := exists_composable K hK l m ((z, 0) : Tot I g) hz
  have h : (K.cst k'' p).fn ((z, 0) : Tot I g) = (0 : Hol (K.W k'')).fn ((z, 0) : Tot I g) := by
    rw [hp k k' k'' h1 h2]
  rw [fn_cst K k'' p hq, show (0 : Hol (K.W k'')) = algebraMap ℂ _ 0 from (map_zero _).symm,
    Hol.fn_algebraMap _ hq] at h
  rw [show (0 : Hol F.V) = algebraMap ℂ _ 0 from (map_zero _).symm, Hol.fn_algebraMap _ hz]
  exact h

end GlobalTheory.AnPer.Charts
