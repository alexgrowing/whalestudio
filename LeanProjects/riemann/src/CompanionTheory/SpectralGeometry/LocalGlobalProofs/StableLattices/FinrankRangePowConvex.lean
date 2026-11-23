import Mathlib

namespace GlobalTheory.CompanionTheory.CommNil

open Module

variable {V : Type} [AddCommGroup V] [Module ℂ V]

private theorem finrank_map_add_finrank_inf_ker' {E F : Type} [AddCommGroup E] [Module ℂ E]
    [FiniteDimensional ℂ E] [AddCommGroup F] [Module ℂ F] (f : E →ₗ[ℂ] F) (A : Submodule ℂ E) :
    finrank ℂ (A.map f) + finrank ℂ (A ⊓ LinearMap.ker f : Submodule ℂ E) = finrank ℂ A := by
  have h := LinearMap.finrank_range_add_finrank_ker (f.domRestrict A)
  rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict] at h
  rw [← Submodule.map_comap_subtype, Submodule.finrank_map_subtype_eq]
  exact h

theorem exists_rel_compl [FiniteDimensional ℂ V] (W' W : Submodule ℂ V) (h : W' ≤ W) :
    ∃ Y : Submodule ℂ V, Y ⊔ W' = W ∧ finrank ℂ Y + finrank ℂ W' = finrank ℂ W := by
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl W'
  have hsup : C ⊓ W ⊔ W' = W := by
    rw [sup_comm, ← sup_inf_assoc_of_le C h, hC.sup_eq_top, top_inf_eq]
  have hinf : C ⊓ W ⊓ W' = ⊥ := by
    have hle : C ⊓ W ⊓ W' ≤ C ⊓ W' := inf_le_inf_right W' inf_le_left
    rw [inf_comm C W', hC.inf_eq_bot] at hle
    exact le_bot_iff.1 hle
  refine ⟨C ⊓ W, hsup, ?_⟩
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq (C ⊓ W) W'
  rw [hsup, hinf, finrank_bot, add_zero] at hdim
  exact hdim.symm

theorem range_pow_succ (a : Module.End ℂ V) (i : ℕ) :
    LinearMap.range (a ^ (i + 1)) = (LinearMap.range (a ^ i)).map a := by
  rw [pow_succ', Module.End.mul_eq_comp, LinearMap.range_comp]

theorem range_pow_succ_le (a : Module.End ℂ V) (i : ℕ) :
    LinearMap.range (a ^ (i + 1)) ≤ LinearMap.range (a ^ i) := by
  rw [pow_succ, Module.End.mul_eq_comp]
  exact LinearMap.range_comp_le_range _ _

theorem finrank_range_pow_convex [FiniteDimensional ℂ V] (a : Module.End ℂ V) (i : ℕ) :
    2 * finrank ℂ (LinearMap.range (a ^ (i + 1))) ≤
      finrank ℂ (LinearMap.range (a ^ i)) + finrank ℂ (LinearMap.range (a ^ (i + 2))) := by
  have h0 : finrank ℂ (LinearMap.range (a ^ (i + 1))) +
      finrank ℂ (LinearMap.range (a ^ i) ⊓ LinearMap.ker a : Submodule ℂ V) = finrank ℂ (LinearMap.range (a ^ i)) := by
    have h := finrank_map_add_finrank_inf_ker' a (LinearMap.range (a ^ i))
    rw [← range_pow_succ] at h
    exact h
  have h1 : finrank ℂ (LinearMap.range (a ^ (i + 2))) +
      finrank ℂ (LinearMap.range (a ^ (i + 1)) ⊓ LinearMap.ker a : Submodule ℂ V) =
        finrank ℂ (LinearMap.range (a ^ (i + 1))) := by
    have h := finrank_map_add_finrank_inf_ker' a (LinearMap.range (a ^ (i + 1)))
    rw [← range_pow_succ] at h
    exact h
  have hmono : finrank ℂ (LinearMap.range (a ^ (i + 1)) ⊓ LinearMap.ker a : Submodule ℂ V) ≤
      finrank ℂ (LinearMap.range (a ^ i) ⊓ LinearMap.ker a : Submodule ℂ V) :=
    Submodule.finrank_mono (inf_le_inf_right _ (range_pow_succ_le a i))
  omega

theorem succ_mul_drop_le [FiniteDimensional ℂ V] (a : Module.End ℂ V) (x : ℕ) :
    (x + 1) * finrank ℂ (LinearMap.range (a ^ x)) + finrank ℂ (LinearMap.range (a ^ (x + 1))) ≤
      (x + 1) * finrank ℂ (LinearMap.range (a ^ (x + 1))) +
        finrank ℂ (LinearMap.range (a ^ 0)) := by
  induction x with
  | zero => omega
  | succ x ih =>
    have conv : 2 * finrank ℂ (LinearMap.range (a ^ (x + 1))) ≤
        finrank ℂ (LinearMap.range (a ^ x)) + finrank ℂ (LinearMap.range (a ^ (x + 1 + 1))) :=
      finrank_range_pow_convex a x
    have hm := Nat.mul_le_mul_left (x + 1) conv
    nlinarith [ih, hm]

theorem range_le_ker_of_commute (a b : Module.End ℂ V) (hab : Commute b a) (ha : IsNilpotent a)
    (x : ℕ) (Y : Submodule ℂ V) (hY : Y ⊔ LinearMap.range (a ^ (x + 1)) = LinearMap.range (a ^ x))
    (hb : Y ≤ LinearMap.ker b) : LinearMap.range (a ^ x) ≤ LinearMap.ker b := by
  have step : ∀ v ∈ LinearMap.range (a ^ x), ∃ u ∈ LinearMap.range (a ^ x), b v = a (b u) := by
    intro v hv
    rw [← hY] at hv
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hv
    rw [range_pow_succ] at hz
    obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.1 hz
    refine ⟨u, hu, ?_⟩
    have hba := LinearMap.congr_fun hab.eq u
    rw [Module.End.mul_apply, Module.End.mul_apply] at hba
    rw [map_add, LinearMap.mem_ker.1 (hb hy), zero_add, hba]
  have key : ∀ k : ℕ, ∀ v ∈ LinearMap.range (a ^ x), ∃ u ∈ LinearMap.range (a ^ x),
      b v = (a ^ k) (b u) := by
    intro k
    induction k with
    | zero => exact fun v hv => ⟨v, hv, by simp⟩
    | succ k ih =>
      intro v hv
      obtain ⟨u, hu, h1⟩ := ih v hv
      obtain ⟨u', hu', h2⟩ := step u hu
      exact ⟨u', hu', by rw [h1, h2, pow_succ, Module.End.mul_apply]⟩
  obtain ⟨N, hN⟩ := ha
  intro v hv
  obtain ⟨u, _, hu⟩ := key N v hv
  rw [LinearMap.mem_ker, hu, hN, LinearMap.zero_apply]

theorem finrank_map_le_of_ker {E F G : Type} [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E]
    [AddCommGroup F] [Module ℂ F] [AddCommGroup G] [Module ℂ G]
    (f : E →ₗ[ℂ] F) (T : E →ₗ[ℂ] G) (A : Submodule ℂ E)
    (h : ∀ b ∈ A, T b = 0 → f b = 0) : finrank ℂ (A.map f) ≤ finrank ℂ (A.map T) := by
  have hf := finrank_map_add_finrank_inf_ker' f A
  have hT := finrank_map_add_finrank_inf_ker' T A
  have hle : finrank ℂ (A ⊓ LinearMap.ker T : Submodule ℂ E) ≤ finrank ℂ (A ⊓ LinearMap.ker f : Submodule ℂ E) :=
    Submodule.finrank_mono fun b hb => Submodule.mem_inf.2 ⟨(Submodule.mem_inf.1 hb).1,
      LinearMap.mem_ker.2 (h b (Submodule.mem_inf.1 hb).1 (LinearMap.mem_ker.1 (Submodule.mem_inf.1 hb).2))⟩
  omega

theorem succ_mul_finrank_map_le :
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (a : Module.End ℂ V),
      IsNilpotent a → ∀ (x : ℕ) (A : Submodule ℂ (Module.End ℂ V)), (∀ b ∈ A, Commute b a) →
        (x + 1) * Module.finrank ℂ (A.map (LinearMap.mulRight ℂ (a ^ x))) ≤
          Module.finrank ℂ V ^ 2 := by
  intro V _ _ _ a ha x A hA
  obtain ⟨Y, hY, hdim⟩ := exists_rel_compl (LinearMap.range (a ^ (x + 1))) (LinearMap.range (a ^ x))
    (range_pow_succ_le a x)
  let T : Module.End ℂ V →ₗ[ℂ] (Y →ₗ[ℂ] V) := LinearMap.lcomp ℂ V Y.subtype
  have hker : ∀ b ∈ A, T b = 0 → LinearMap.mulRight ℂ (a ^ x) b = 0 := by
    intro b hbA hTb
    have hYk : Y ≤ LinearMap.ker b := by
      intro y hy
      have hy0 := LinearMap.congr_fun hTb ⟨y, hy⟩
      rw [LinearMap.lcomp_apply, LinearMap.zero_apply] at hy0
      exact LinearMap.mem_ker.2 hy0
    have hR := range_le_ker_of_commute a b (hA b hbA) ha x Y hY hYk
    rw [LinearMap.mulRight_apply]
    ext v
    rw [Module.End.mul_apply, LinearMap.zero_apply]
    exact LinearMap.mem_ker.1 (hR (LinearMap.mem_range_self _ v))
  have h7 := finrank_map_le_of_ker (LinearMap.mulRight ℂ (a ^ x)) T A hker
  have h8 : Module.finrank ℂ (A.map T) ≤ Module.finrank ℂ Y * Module.finrank ℂ V :=
    (Submodule.finrank_le _).trans (le_of_eq (Module.finrank_linearMap ℂ ℂ Y V))
  have h5 := succ_mul_drop_le a x
  have hr0 : Module.finrank ℂ (LinearMap.range (a ^ 0)) ≤ Module.finrank ℂ V := Submodule.finrank_le _
  rw [← hdim] at h5
  have hY1 : (x + 1) * Module.finrank ℂ Y ≤ Module.finrank ℂ V := by nlinarith [h5, hr0]
  calc (x + 1) * Module.finrank ℂ (A.map (LinearMap.mulRight ℂ (a ^ x)))
      ≤ (x + 1) * (Module.finrank ℂ Y * Module.finrank ℂ V) := Nat.mul_le_mul_left _ (h7.trans h8)
    _ = ((x + 1) * Module.finrank ℂ Y) * Module.finrank ℂ V := by ring
    _ ≤ Module.finrank ℂ V * Module.finrank ℂ V := Nat.mul_le_mul_right _ hY1
    _ = Module.finrank ℂ V ^ 2 := by ring

end GlobalTheory.CompanionTheory.CommNil
