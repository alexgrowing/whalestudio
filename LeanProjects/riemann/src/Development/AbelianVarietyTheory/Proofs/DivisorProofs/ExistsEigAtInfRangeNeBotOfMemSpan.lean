import Mathlib
import Formalism.LocalToGlobal.Columns.HeckeSp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ISupIndepEigAtOfAnyFamily

open Formalism.L2.Col

namespace GlobalTheory

theorem map_mem_eigAt_of_semilinear {K V W I : Type} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module ℂ W] (σ : K →+* ℂ) (j : V →ₛₗ[σ] W) (op : I → Module.End K V)
    (T : I → Module.End ℂ W) (hT : ∀ i v, T i (j v) = j (op i v)) (y : I → K) (v : V)
    (hv : v ∈ eigAt op y) : j v ∈ eigAt T (fun i => σ (y i)) := by
  have key : ∀ (i : I) (k : ℕ) (v : V),
      ((T i - σ (y i) • (1 : Module.End ℂ W)) ^ k) (j v)
        = j (((op i - y i • (1 : Module.End K V)) ^ k) v) := by
    intro i k
    induction k with
    | zero => intro v; simp
    | succ k ih =>
      intro v
      rw [pow_succ, Module.End.mul_apply, pow_succ, Module.End.mul_apply, ← ih]
      congr 1
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, map_sub,
        map_smulₛₗ, hT]
  rw [eigAt, Submodule.mem_iInf]
  intro i
  obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace _ _ _).1 (eigAt_le op y i hv)
  rw [Module.End.mem_maxGenEigenspace]
  exact ⟨k, by rw [key, hk, map_zero]⟩

theorem exists_eigAt_inf_range_ne_bot_of_mem_span :
    ∀ {K V W I : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [AddCommGroup W] [Module ℂ W] (σ : K →+* ℂ) (j : V →ₛₗ[σ] W) (op : I → Module.End K V) (T : I → Module.End ℂ W) (e : Module.End K V) (x : I → ℂ) (w : W), (∀ i v, T i (j v) = j (op i v)) → PairComm op → SplitOver op → (∀ i, Commute (op i) e) → w ∈ Submodule.span ℂ (j '' (LinearMap.range e : Set V)) → w ≠ 0 → (∀ i, T i w = x i • w) → ∃ y : I → K, (∀ i, σ (y i) = x i) ∧ eigAt op y ⊓ LinearMap.range e ≠ ⊥ := by
  intro K V W I _ _ _ _ _ _ σ j op T e x w hT hc hs he hw hw0 hx
  by_contra hno
  push Not at hno
  have hall : ∀ v : V, j (e v) ∈ ⨆ (z : I → ℂ) (_ : z ≠ x), eigAt T z := by
    intro v
    have hv : v ∈ ⨆ y, eigAt op y := by
      rw [iSup_eigAt_eq_top hc hs]; exact Submodule.mem_top
    induction hv using Submodule.iSup_induction' with
    | mem y v hv =>
      have hev : e v ∈ eigAt op y := eigAt_le_comap he y hv
      by_cases hy : ∀ i, σ (y i) = x i
      · have h0 : e v ∈ eigAt op y ⊓ LinearMap.range e := ⟨hev, ⟨v, rfl⟩⟩
        rw [hno y hy, Submodule.mem_bot] at h0
        rw [h0, map_zero]
        exact Submodule.zero_mem _
      · have hne : (fun i => σ (y i)) ≠ x := fun h => hy fun i => congrFun h i
        exact le_iSup₂_of_le (f := fun (z : I → ℂ) (_ : z ≠ x) => eigAt T z) _ hne le_rfl
          (map_mem_eigAt_of_semilinear σ j op T hT y _ hev)
    | zero => rw [map_zero, map_zero]; exact Submodule.zero_mem _
    | add a b _ _ ha hb => rw [map_add, map_add]; exact Submodule.add_mem _ ha hb
  have hw' : w ∈ ⨆ (z : I → ℂ) (_ : z ≠ x), eigAt T z := by
    refine Submodule.span_le.2 ?_ hw
    rintro _ ⟨_, ⟨v, rfl⟩, rfl⟩
    exact hall v
  have hd := iSupIndep_eigAt_of_any_family ℂ W I T x
  exact hw0 ((Submodule.mem_bot ℂ).1 (hd.le_bot ⟨mem_eigAt_of_forall_apply hx, hw'⟩))

end GlobalTheory
