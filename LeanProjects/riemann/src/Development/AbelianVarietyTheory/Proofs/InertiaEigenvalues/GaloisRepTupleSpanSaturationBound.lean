import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TupMemLatT
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.CovSat

theorem satA : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] (a m : ℕ) (ρs : Fin m → (Γ →* GL (Fin a) (Om l))) (t : Fin m → Finset (Matrix (Fin a) (Fin a) (Om l))), (∀ k, ∃ c' : Matrix (Fin a) (Fin a) (Om l) → ℤ_[l], ∑ y ∈ t k, zOm l (c' y) • y = 1) → (∀ k g, ∀ x ∈ t k, ∃ c' : Matrix (Fin a) (Fin a) (Om l) → ℤ_[l], ((ρs k g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) * x = ∑ y ∈ t k, zOm l (c' y) • y) → ∃ u : ℕ, ∀ N M : ℕ, N + u ≤ M → ∀ H : Γ →₀ ℤ_[l], (H.sum fun g c => zOm l c • GlobalTheory.TraceConjugationCover.tup ρs g) ∈ GlobalTheory.TraceConjugationCover.latL t M → ∃ H' : Γ →₀ ℤ_[l], (H.sum fun g c => zOm l c • GlobalTheory.TraceConjugationCover.tup ρs g) = (l : Om l) ^ N • (H'.sum fun g c => zOm l c • GlobalTheory.TraceConjugationCover.tup ρs g) := by
  intro l _ Γ _ a m ρs t h1 hst
  classical
  let E : Submodule ℤ_[l] (Fin m → Matrix (Fin a) (Fin a) (Om l)) :=
    Submodule.span ℤ_[l] (Set.range (GlobalTheory.TraceConjugationCover.tup ρs))
  let Λ := GlobalTheory.TraceConjugationCover.latL t 0
  have hsumE : ∀ H : Γ →₀ ℤ_[l], (H.sum fun g c => zOm l c • GlobalTheory.TraceConjugationCover.tup ρs g) ∈ E := by
    intro H
    rw [Finsupp.mem_span_range_iff_exists_finsupp]
    exact ⟨H, by simp only [GlobalTheory.TraceConjugationCover.zOm_smul]⟩
  have hEsum : ∀ x ∈ E, ∃ H' : Γ →₀ ℤ_[l], x = H'.sum fun g c => zOm l c • GlobalTheory.TraceConjugationCover.tup ρs g := by
    intro x hx
    obtain ⟨H', hH'⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hx
    exact ⟨H', by rw [← hH']; simp only [GlobalTheory.TraceConjugationCover.zOm_smul]⟩
  have hc : ∀ (n : ℕ) (w : Fin m → Matrix (Fin a) (Fin a) (Om l)), (l : Om l) ^ n • w = (l : ℤ_[l]) ^ n • w := by
    intro n w
    rw [← GlobalTheory.TraceConjugationCover.zOm_smul, map_pow, map_natCast]
  have hsingle : ∀ k, ∀ z ∈ t k, Pi.single k z ∈ Λ := by
    intro k z hz
    exact Submodule.subset_span (Set.mem_iUnion.2 ⟨k, z, hz, by simp⟩)
  have hlat : ∀ M, ∀ x ∈ GlobalTheory.TraceConjugationCover.latL t M, ∃ y ∈ Λ, x = ((l : ℤ_[l]) ^ M) • y := by
    intro M x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, hk⟩ := Set.mem_iUnion.1 hx
      obtain ⟨z, hz, rfl⟩ := hk
      refine ⟨Pi.single k z, hsingle k z hz, ?_⟩
      rw [← hc]
      ext i : 1
      by_cases hi : i = k
      · subst hi; simp
      · simp [Pi.single_apply, hi]
    | zero => exact ⟨0, Λ.zero_mem, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨x', hx', rfl⟩ := hx
      obtain ⟨y', hy', rfl⟩ := hy
      exact ⟨x' + y', Λ.add_mem hx' hy', by rw [smul_add]⟩
    | smul c x _ hx =>
      obtain ⟨x', hx', rfl⟩ := hx
      exact ⟨c • x', Λ.smul_mem c hx', by rw [smul_comm]⟩
  have hspan : ∀ k (c : Matrix (Fin a) (Fin a) (Om l) → ℤ_[l]),
      (∑ y ∈ t k, zOm l (c y) • y) ∈ Submodule.span ℤ_[l] (t k : Set (Matrix (Fin a) (Fin a) (Om l))) := by
    intro k c
    refine Submodule.sum_mem _ fun y hy => ?_
    rw [GlobalTheory.TraceConjugationCover.zOm_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hy)
  have hρ : ∀ k g, ((ρs k g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) ∈
      Submodule.span ℤ_[l] (t k : Set (Matrix (Fin a) (Fin a) (Om l))) := by
    intro k g
    obtain ⟨c', hc'⟩ := h1 k
    rw [← mul_one ((ρs k g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)), ← hc', Finset.mul_sum]
    refine Submodule.sum_mem _ fun y hy => ?_
    rw [Matrix.mul_smul]
    obtain ⟨c'', hc''⟩ := hst k g y hy
    rw [hc'', GlobalTheory.TraceConjugationCover.zOm_smul]
    exact Submodule.smul_mem _ _ (hspan k c'')
  have hspanΛ : ∀ k, Submodule.span ℤ_[l] (t k : Set (Matrix (Fin a) (Fin a) (Om l))) ≤
      Λ.comap (LinearMap.single ℤ_[l] (fun _ : Fin m => Matrix (Fin a) (Fin a) (Om l)) k) := by
    intro k
    rw [Submodule.span_le]
    intro z hz
    exact hsingle k z hz
  have hEΛ : E ≤ Λ := by
    rw [Submodule.span_le]
    rintro _ ⟨g, rfl⟩
    rw [← Finset.univ_sum_single (GlobalTheory.TraceConjugationCover.tup ρs g)]
    exact Submodule.sum_mem _ fun k _ => hspanΛ k (hρ k g)
  have hfg : Λ.FG := Submodule.fg_span (Set.finite_iUnion fun k => (t k).finite_toSet.image _)
  haveI : IsNoetherian ℤ_[l] Λ := isNoetherian_of_fg_of_noetherian Λ hfg
  let f : ℕ →o Submodule ℤ_[l] Λ :=
    ⟨fun v => (E.comap Λ.subtype).comap (((l : ℤ_[l]) ^ v) • LinearMap.id), by
      intro v w hvw y hy
      simp only [Submodule.mem_comap, LinearMap.smul_apply, LinearMap.id_apply, map_smul,
        Submodule.subtype_apply] at hy ⊢
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hvw
      rw [pow_add, mul_comm, mul_smul]
      exact E.smul_mem _ hy⟩
  have hf : ∀ v (y : Λ), y ∈ f v ↔ ((l : ℤ_[l]) ^ v) • (y : Fin m → Matrix (Fin a) (Fin a) (Om l)) ∈ E := by
    intro v y
    show y ∈ (E.comap Λ.subtype).comap (((l : ℤ_[l]) ^ v) • LinearMap.id) ↔ _
    simp only [Submodule.mem_comap, LinearMap.smul_apply, LinearMap.id_apply, map_smul,
      Submodule.subtype_apply]
  obtain ⟨u, hu⟩ := monotone_stabilizes_iff_noetherian.2 inferInstance f
  refine ⟨u, fun N M hNM H hx => ?_⟩
  obtain ⟨y, hyΛ, hxy⟩ := hlat M _ hx
  have hyM : (⟨y, hyΛ⟩ : Λ) ∈ f M := by
    rw [hf]
    show ((l : ℤ_[l]) ^ M) • y ∈ E
    rw [← hxy]
    exact hsumE H
  rw [← hu M (by omega), hf] at hyM
  have hz : ((l : ℤ_[l]) ^ (M - N - u)) • (((l : ℤ_[l]) ^ u) • y) ∈ E := E.smul_mem _ hyM
  obtain ⟨H', hH'⟩ := hEsum _ hz
  refine ⟨H', ?_⟩
  rw [hxy, ← hH', hc, smul_smul, smul_smul, ← pow_add, ← pow_add]
  congr 2
  omega

end GlobalTheory.CovSat
