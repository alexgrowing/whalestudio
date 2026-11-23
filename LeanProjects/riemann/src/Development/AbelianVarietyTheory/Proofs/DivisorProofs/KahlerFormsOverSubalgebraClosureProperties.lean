import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DlogRatioVolumeFormNeZero
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PD

variable (k K : Type) [Field k] [Field K] [Algebra k K]

theorem dDR_ιMulti_D (q : ℕ) (v : Fin q → K) :
    dDR k K (ExteriorAlgebra.ιMulti K q fun j => D k K (v j)) = 0 := by
  induction q with
  | zero =>
    rw [ExteriorAlgebra.ιMulti_zero_apply, ← map_one (algebraMap K (DR k K)), dDR_algebraMap,
      Derivation.map_one_eq_zero, map_zero]
  | succ q ih =>
    rw [ExteriorAlgebra.ιMulti_succ_apply, dDR_mul]
    have ht : Matrix.vecTail (fun j => D k K (v j)) = fun j => D k K (v j.succ) := rfl
    rw [ht, ih (fun j => v j.succ), mul_zero, zero_add,
      show dDR k K (ExteriorAlgebra.ι K (D k K (v 0))) = 0 from dDR_D (v 0), zero_mul]

variable {k K}

theorem mem_deg_of_mem_omB (B : Subalgebra k K) (q : ℕ) (a : DR k K) (ha : a ∈ omB k K B q) :
    a ∈ ⋀[K]^q Ω[K⁄k] := by
  induction ha using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨c, -, v, -, rfl⟩ := hx
    exact Submodule.smul_mem _ c (ExteriorAlgebra.ιMulti_range K q ⟨_, rfl⟩)
  | zero => exact zero_mem _
  | add x y _ _ hx hy => exact add_mem hx hy
  | smul r x _ hx => exact Submodule.smul_of_tower_mem _ r hx

theorem mul_mem_omB (B : Subalgebra k K) (p q : ℕ) (a : DR k K) (ha : a ∈ omB k K B p)
    (b : DR k K) (hb : b ∈ omB k K B q) : a * b ∈ omB k K B (p + q) := by
  induction ha using Submodule.span_induction with
  | mem x hx =>
    induction hb using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨c, hc, v, hv, rfl⟩ := hx
      obtain ⟨c', hc', w, hw, rfl⟩ := hy
      have happ : Fin.append (fun j => D k K (v j)) (fun j => D k K (w j)) =
          fun j => D k K (Fin.append v w j) := by
        funext j
        refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;> simp
      refine Submodule.subset_span ⟨c * c', B.mul_mem hc hc', Fin.append v w, fun j => ?_, ?_⟩
      · refine Fin.addCases (fun i => ?_) (fun i => ?_) j
        · rw [Fin.append_left]; exact hv i
        · rw [Fin.append_right]; exact hw i
      · rw [smul_mul_smul_comm, ExteriorAlgebra.ιMulti_mul_ιMulti, happ]
    | zero => rw [mul_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [mul_add]; exact add_mem hy hz
    | smul r y _ hy => rw [mul_smul_comm]; exact Submodule.smul_mem _ r hy
  | zero => rw [zero_mul]; exact zero_mem _
  | add x y _ _ hx hy => rw [add_mul]; exact add_mem hx hy
  | smul r x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ r hx

theorem dDR_mem_omB (B : Subalgebra k K) (p : ℕ) (a : DR k K) (ha : a ∈ omB k K B p) :
    dDR k K a ∈ omB k K B (p + 1) := by
  induction ha using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨c, hc, v, hv, rfl⟩ := hx
    rw [dDR_smul, dDR_ιMulti_D, smul_zero, add_zero]
    refine Submodule.subset_span ⟨1, B.one_mem, Fin.cons c v, fun j => ?_, ?_⟩
    · refine Fin.cases ?_ (fun i => ?_) j
      · rw [Fin.cons_zero]; exact hc
      · rw [Fin.cons_succ]; exact hv i
    · rw [one_smul, ExteriorAlgebra.ιMulti_succ_apply]
      simp only [Matrix.vecTail, Function.comp_def, Fin.cons_succ, Fin.cons_zero]
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul r x _ hx => rw [map_smul]; exact Submodule.smul_mem _ r hx

theorem smul_mem_omB (B : Subalgebra k K) (p : ℕ) (c : K) (hc : c ∈ B) (a : DR k K)
    (ha : a ∈ omB k K B p) : c • a ∈ omB k K B p := by
  induction ha using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, hb, v, hv, rfl⟩ := hx
    exact Submodule.subset_span ⟨c * b, B.mul_mem hc hb, v, hv, by rw [smul_smul]⟩
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | smul r x _ hx => rw [smul_comm c r x]; exact Submodule.smul_mem _ r hx

theorem omB_mono (B B' : Subalgebra k K) (h : B ≤ B') (p : ℕ) : omB k K B p ≤ omB k K B' p := by
  refine Submodule.span_mono ?_
  rintro y ⟨b, hb, v, hv, rfl⟩
  exact ⟨b, h hb, v, fun j => h (hv j), rfl⟩

theorem mem_omB_zero (B : Subalgebra k K) (y : DR k K) :
    y ∈ omB k K B 0 ↔ ∃ c ∈ B, y = algebraMap K (DR k K) c := by
  constructor
  · intro hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨b, hb, v, -, rfl⟩ := hx
      exact ⟨b, hb, by rw [ExteriorAlgebra.ιMulti_zero_apply, Algebra.smul_def, mul_one]⟩
    | zero => exact ⟨0, B.zero_mem, (map_zero _).symm⟩
    | add x z _ _ hx hz =>
      obtain ⟨c, hc, rfl⟩ := hx
      obtain ⟨c', hc', rfl⟩ := hz
      exact ⟨c + c', B.add_mem hc hc', (map_add _ _ _).symm⟩
    | smul r x _ hx =>
      obtain ⟨c, hc, rfl⟩ := hx
      exact ⟨r • c, B.smul_mem hc r, by simp only [Algebra.algebraMap_eq_smul_one, smul_assoc]⟩
  · rintro ⟨c, hc, rfl⟩
    exact Submodule.subset_span ⟨c, hc, Fin.elim0, fun j => j.elim0, by
      rw [ExteriorAlgebra.ιMulti_zero_apply, Algebra.smul_def, mul_one]⟩

theorem omB_alg : ∀ (k K : Type) [Field k] [Field K] [Algebra k K], ∀ (B : Subalgebra k K) (p q : ℕ),
    (∀ a ∈ omB k K B p, ∀ b ∈ omB k K B q, a * b ∈ omB k K B (p + q)) ∧
    (∀ a ∈ omB k K B p, dDR k K a ∈ omB k K B (p + 1) ∧ sg k K a = (-1 : k) ^ p • a ∧
      a ∈ ⋀[K]^p Ω[K⁄k] ∧ ∀ c ∈ B, c • a ∈ omB k K B p) ∧
    (∀ B' : Subalgebra k K, B ≤ B' → omB k K B p ≤ omB k K B' p) ∧
    ∀ y : DR k K, y ∈ omB k K B 0 ↔ ∃ c ∈ B, y = algebraMap K (DR k K) c := by
  intro k K _ _ _ B p q
  refine ⟨fun a ha b hb => mul_mem_omB B p q a ha b hb, fun a ha => ?_,
    fun B' h => omB_mono B B' h p, mem_omB_zero B⟩
  have hdeg := mem_deg_of_mem_omB B p a ha
  refine ⟨dDR_mem_omB B p a ha, ?_, hdeg, fun c hc => smul_mem_omB B p c hc a ha⟩
  change sgn a = _
  rw [sgn_of_mem hdeg, Algebra.smul_def, map_pow, map_neg, map_one]

end GlobalTheory.PD
