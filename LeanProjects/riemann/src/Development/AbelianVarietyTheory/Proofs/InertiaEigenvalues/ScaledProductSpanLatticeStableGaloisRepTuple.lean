import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TupMemLatT
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section
namespace GlobalTheory.TraceConjugationCover

theorem tup_mul_tup {l : ℕ} [Fact l.Prime] {Γ : Type} [Group Γ] {a m : ℕ}
    (ρs : Fin m → (Γ →* GL (Fin a) (Om l))) (g h : Γ) : tup ρs g * tup ρs h = tup ρs (g * h) := by
  funext k
  simp [tup, map_mul, Units.val_mul]

theorem tup_mul_smul {l : ℕ} [Fact l.Prime] {Γ : Type} [Group Γ] {a m : ℕ}
    (ρs : Fin m → (Γ →* GL (Fin a) (Om l))) (g : Γ) (c : ℤ_[l]) (x : Fin m → Matrix (Fin a) (Fin a) (Om l)) :
    tup ρs g * (c • x) = c • (tup ρs g * x) := by
  rw [← zOm_smul, ← zOm_smul]
  funext k
  simp [Pi.mul_apply, Pi.smul_apply, Matrix.mul_smul]

theorem stabE : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] (a m : ℕ) (ρs : Fin m → (Γ →* GL (Fin a) (Om l))) (t : Fin m → Finset (Matrix (Fin a) (Fin a) (Om l))) (M : ℕ), (∀ k g, ∀ x ∈ t k, ∃ c' : Matrix (Fin a) (Fin a) (Om l) → ℤ_[l], ((ρs k g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) * x = ∑ y ∈ t k, zOm l (c' y) • y) → (∀ g, ∀ x ∈ GlobalTheory.TraceConjugationCover.latL t M, GlobalTheory.TraceConjugationCover.tup ρs g * x ∈ GlobalTheory.TraceConjugationCover.latL t M) ∧ ∀ g, ∀ x ∈ GlobalTheory.TraceConjugationCover.latT ρs t M, GlobalTheory.TraceConjugationCover.tup ρs g * x ∈ GlobalTheory.TraceConjugationCover.latT ρs t M := by
  intro l _ Γ _ a m ρs t M hc
  have hL : ∀ g, ∀ x ∈ latL t M, tup ρs g * x ∈ latL t M := by
    intro g x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hx
      obtain ⟨y, hy, rfl⟩ := hk
      obtain ⟨c', hc'⟩ := hc k g y hy
      have e : tup ρs g * Pi.single k ((l : Om l) ^ M • y)
          = ∑ z ∈ t k, c' z • (Pi.single k ((l : Om l) ^ M • z) : Fin m → Matrix (Fin a) (Fin a) (Om l)) := by
        have e1 : tup ρs g * Pi.single k ((l : Om l) ^ M • y)
            = Pi.single k ((l : Om l) ^ M • (((ρs k g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) * y)) := by
          funext j
          by_cases hj : j = k
          · subst hj; simp [tup, Matrix.mul_smul]
          · simp [Pi.single_apply, hj]
        rw [e1, hc', Finset.smul_sum]
        funext j
        rw [Finset.sum_apply]
        by_cases hj : j = k
        · subst hj
          simp only [Pi.single_eq_same, Pi.smul_apply]
          refine Finset.sum_congr rfl fun z _ => ?_
          rw [smul_comm ((l : Om l) ^ M) (zOm l (c' z)) z, zOm_smul]
        · simp [Pi.single_apply, hj]
      rw [e]
      refine Submodule.sum_mem _ fun z hz => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
      exact Set.mem_iUnion.mpr ⟨k, z, hz, rfl⟩
    | zero => simp
    | add x y _ _ hx hy => rw [mul_add]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx => rw [tup_mul_smul]; exact Submodule.smul_mem _ _ hx
  refine ⟨hL, fun g x hx => ?_⟩
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
  clear hx
  rw [mul_add]
  refine Submodule.add_mem _ ?_ (Submodule.mem_sup_right (hL g z hz))
  refine Submodule.mem_sup_left ?_
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨h, rfl⟩ := hx
    rw [tup_mul_tup]; exact Submodule.subset_span ⟨_, rfl⟩
  | zero => simp
  | add x y _ _ hx hy => rw [mul_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [tup_mul_smul]; exact Submodule.smul_mem _ _ hx

end GlobalTheory.TraceConjugationCover
end
