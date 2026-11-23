import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DlogRatioVolumeFormNeZero

set_option autoImplicit false

noncomputable section

open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

namespace GlobalTheory.PD.KSpan

theorem alt_mem_of_span {K M N : Type} [Field K] [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
    {n : ℕ} (f : M [⋀^Fin n]→ₗ[K] N) (s : Set M) (hs : Submodule.span K s = ⊤) (T : Submodule K N)
    (hT : ∀ v : Fin n → M, (∀ i, v i ∈ s) → f v ∈ T) (v : Fin n → M) : f v ∈ T := by
  have key : ∀ j : ℕ, ∀ v : Fin n → M, (∀ i : Fin n, j ≤ i.val → v i ∈ s) → f v ∈ T := by
    intro j
    induction j with
    | zero => intro v hv; exact hT v fun i => hv i (Nat.zero_le _)
    | succ j ih =>
      intro v hv
      by_cases hj : j < n
      · have hmem : v ⟨j, hj⟩ ∈ Submodule.span K s := hs ▸ Submodule.mem_top
        have hall : ∀ x ∈ Submodule.span K s, f (Function.update v ⟨j, hj⟩ x) ∈ T := by
          intro x hx
          induction hx using Submodule.span_induction with
          | mem x hx =>
            apply ih
            intro i hi
            by_cases h : i = ⟨j, hj⟩
            · rw [h, Function.update_self]; exact hx
            · rw [Function.update_of_ne h]
              apply hv
              have : i.val ≠ j := fun h' => h (Fin.ext h')
              omega
          | zero => rw [AlternatingMap.map_update_zero]; exact T.zero_mem
          | add a b _ _ ha hb => rw [AlternatingMap.map_update_add]; exact T.add_mem ha hb
          | smul r a _ ha => rw [AlternatingMap.map_update_smul]; exact T.smul_mem r ha
        simpa using hall _ hmem
      · exact ih v fun i hi => hv i (by have := i.isLt; omega)
  exact key n v fun i hi => absurd i.isLt (by omega)

end GlobalTheory.PD.KSpan

namespace GlobalTheory.PD

open KSpan in

theorem omB_comap_span_eq_top : ∀ (k K : Type) [Field k] [Field K] [Algebra k K] (B : Subalgebra k K) [IsFractionRing B K] (p : ℕ) (W : Type) [AddCommGroup W] [Module K W] [Module k W] [IsScalarTower k K W] (e : W →ₗ[K] DR k K), Function.Injective e → LinearMap.range e = ⋀[K]^p Ω[K⁄k] → Submodule.span K ((omB k K B p).comap (e.restrictScalars k) : Set W) = ⊤ := by
  intro k K _ _ _ B _ p W _ _ _ _ e he hr
  have hD : Submodule.span K (D k K '' (B : Set K)) = ⊤ := by
    rw [eq_top_iff, ← span_range_derivation k K, Submodule.span_le]
    rintro _ ⟨y, rfl⟩
    obtain ⟨b1, b2, hb2, rfl⟩ := IsFractionRing.div_surjective (A := B) y
    have h2 : algebraMap B K b2 ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb2
    set q := algebraMap B K b1 / algebraMap B K b2 with hqdef
    have e1 : algebraMap B K b1 = q * algebraMap B K b2 := by rw [hqdef, div_mul_cancel₀ _ h2]
    have hq : D k K q = (algebraMap B K b2)⁻¹ • (D k K (algebraMap B K b1) - q • D k K (algebraMap B K b2)) := by
      rw [e1, Derivation.leibniz, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ h2, one_smul]
    have m1 : D k K (algebraMap B K b1) ∈ Submodule.span K (D k K '' (B : Set K)) :=
      Submodule.subset_span ⟨(b1 : K), b1.2, rfl⟩
    have m2 : D k K (algebraMap B K b2) ∈ Submodule.span K (D k K '' (B : Set K)) :=
      Submodule.subset_span ⟨(b2 : K), b2.2, rfl⟩
    rw [SetLike.mem_coe, hq]
    exact Submodule.smul_mem _ _ (Submodule.sub_mem _ m1 (Submodule.smul_mem _ _ m2))
  have hS : (omB k K B p : Set (DR k K)) ⊆ ⋀[K]^p Ω[K⁄k] := by
    intro y hy
    change y ∈ Submodule.span k _ at hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨b, -, v, -, rfl⟩ := hy
      exact Submodule.smul_mem _ b (ExteriorAlgebra.ιMulti_range K p ⟨_, rfl⟩)
    | zero => exact Submodule.zero_mem _
    | add a c _ _ ha hc => exact Submodule.add_mem _ ha hc
    | smul r a _ ha => rw [← algebraMap_smul K r a]; exact Submodule.smul_mem _ _ ha
  have hP : ⋀[K]^p Ω[K⁄k] ≤ Submodule.span K (omB k K B p : Set (DR k K)) := by
    rw [← ExteriorAlgebra.ιMulti_span_fixedDegree, Submodule.span_le]
    rintro _ ⟨v, rfl⟩
    refine alt_mem_of_span (ExteriorAlgebra.ιMulti K p) _ hD _ ?_ v
    intro v hv
    choose b hb hbv using hv
    apply Submodule.subset_span
    apply Submodule.subset_span
    refine ⟨1, B.one_mem, b, hb, ?_⟩
    rw [one_smul]
    simp only [hbv]
  have hSC : (omB k K B p : Set (DR k K)) ⊆ e '' ((omB k K B p).comap (e.restrictScalars k) : Set W) := by
    intro y hy
    obtain ⟨w, rfl⟩ : y ∈ LinearMap.range e := hr ▸ hS hy
    exact ⟨w, hy, rfl⟩
  rw [eq_top_iff, ← Submodule.map_le_map_iff_of_injective he, ← LinearMap.range_eq_map, hr, Submodule.map_span]
  exact hP.trans (Submodule.span_mono hSC)

end GlobalTheory.PD
