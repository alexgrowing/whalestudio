import Mathlib
open NumberField

namespace GlobalTheory.GensModNsmul

theorem exists_gen_mod_nsmul_of_linearMap (E : Type) [Field E] [NumberField E] (M : ℕ) (hM : 1 ≤ M)
    (N : Type) [AddCommGroup N] [Module (𝓞 E) N] [Module.Finite (𝓞 E) N] (π : N →ₗ[𝓞 E] E) :
    ∃ l : N, ∀ x : N, ∃ o : 𝓞 E, ∃ y : N, π x = o • π l + M • π y := by
  have hfg : (LinearMap.range π).FG := by
    rw [LinearMap.range_eq_map]; exact Module.Finite.fg_top.map _
  obtain ⟨d, hd, hint⟩ := FractionalIdeal.isFractional_of_fg (S := nonZeroDivisors (𝓞 E)) hfg
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
  have hd0' : (algebraMap (𝓞 E) E d) ≠ 0 := by simpa using hd0
  set I : Ideal (𝓞 E) := Submodule.comap (Algebra.linearMap (𝓞 E) E) (LinearMap.range (d • π)) with hI
  have hmem : ∀ a : 𝓞 E, a ∈ I ↔ ∃ x : N, d • π x = algebraMap (𝓞 E) E a := by
    intro a; simp [hI]
  have hM0 : (M : 𝓞 E) ≠ 0 := by exact_mod_cast (by omega : M ≠ 0)
  have key : ∃ a ∈ I, Ideal.span {(M : 𝓞 E)} * I ⊔ Ideal.span {a} = I := by
    by_cases h : I = ⊥
    · exact ⟨0, I.zero_mem, by simp [h]⟩
    · obtain ⟨a, ha⟩ := IsDedekindDomain.exists_sup_span_eq
        (I := Ideal.span {(M : 𝓞 E)} * I) (J := I) Ideal.mul_le_right
        (mul_ne_zero (by simpa using hM0) h)
      refine ⟨a, ?_, ha⟩
      rw [← ha]
      exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self a)
  obtain ⟨a, haI, ha⟩ := key
  obtain ⟨l, hl⟩ := (hmem a).1 haI
  refine ⟨l, fun x => ?_⟩
  obtain ⟨b, hb⟩ := hint (π x) ⟨x, rfl⟩
  have hbI : b ∈ I := (hmem b).2 ⟨x, hb.symm⟩
  rw [← ha, Submodule.mem_sup] at hbI
  obtain ⟨u, hu, v, hv, huv⟩ := hbI
  obtain ⟨c, hc, rfl⟩ := Ideal.mem_span_singleton_mul.1 hu
  obtain ⟨o, rfl⟩ := Ideal.mem_span_singleton'.1 hv
  obtain ⟨y, hy⟩ := (hmem c).1 hc
  refine ⟨o, y, ?_⟩
  apply mul_left_cancel₀ hd0'
  rw [Algebra.smul_def] at hb hl hy
  rw [← hb, ← huv, Algebra.smul_def, nsmul_eq_mul, map_add, map_mul, map_mul, map_natCast, ← hl, ← hy]
  ring

theorem exists_gens_mod_nsmul_of_injective (E : Type) [Field E] [NumberField E] (M : ℕ) (hM : 1 ≤ M)
    (r : ℕ) : ∀ (N : Type) [AddCommGroup N] [Module (𝓞 E) N] [Module.Finite (𝓞 E) N]
    (f : N →ₗ[𝓞 E] (Fin r → E)), Function.Injective f →
    ∃ e : Fin r → N, ∀ x : N, ∃ o : Fin r → 𝓞 E, ∃ y : N, x = ∑ i, o i • e i + M • y := by
  induction r with
  | zero =>
    intro N _ _ _ f hf
    refine ⟨Fin.elim0, fun x => ⟨Fin.elim0, 0, ?_⟩⟩
    simpa using hf (Subsingleton.elim (f x) (f 0))
  | succ r ih =>
    intro N _ _ _ f hf
    let π : N →ₗ[𝓞 E] E := (LinearMap.proj 0) ∘ₗ f
    obtain ⟨l, hl⟩ := exists_gen_mod_nsmul_of_linearMap E M hM N π
    let f' : LinearMap.ker π →ₗ[𝓞 E] (Fin r → E) :=
      LinearMap.pi fun i => (LinearMap.proj i.succ) ∘ₗ f ∘ₗ (LinearMap.ker π).subtype
    have hf' : Function.Injective f' := by
      rw [injective_iff_map_eq_zero]
      intro x hx
      apply Subtype.ext
      apply hf
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · rw [Submodule.coe_zero, map_zero]; exact x.2
      · simpa [f'] using congrFun hx j
    obtain ⟨e, he⟩ := ih (LinearMap.ker π) f' hf'
    refine ⟨Fin.cons l (fun i => (e i : N)), fun x => ?_⟩
    obtain ⟨o, y, hoy⟩ := hl x
    have hk : x - o • l - M • y ∈ LinearMap.ker π := by
      rw [LinearMap.mem_ker, map_sub, map_sub, map_smul, map_nsmul, hoy]; abel
    obtain ⟨o', y', h'⟩ := he ⟨_, hk⟩
    refine ⟨Fin.cons o o', y + y', ?_⟩
    have h2 := congrArg Subtype.val h'
    simp only [Submodule.coe_add, Submodule.coe_sum, Submodule.coe_smul,
      Submodule.coe_smul_of_tower] at h2
    simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, smul_add]
    have : x = o • l + M • y + (x - o • l - M • y) := by abel
    rw [this, h2]; abel

theorem exists_gens_mod_nsmul (E : Type) [Field E] [NumberField E] (r M : ℕ)
    (Λ : Submodule (𝓞 E) (Fin r → E)) (hM : 1 ≤ M) (hΛ : Λ.FG) :
    ∃ e : Fin r → Fin r → E, (∀ i, e i ∈ Λ) ∧
      ∀ x ∈ Λ, ∃ o : Fin r → 𝓞 E, ∃ y ∈ Λ, x = ∑ i, o i • e i + M • y := by
  haveI : Module.Finite (𝓞 E) Λ := Module.Finite.iff_fg.2 hΛ
  obtain ⟨e, he⟩ := exists_gens_mod_nsmul_of_injective E M hM r Λ Λ.subtype Subtype.val_injective
  refine ⟨fun i => e i, fun i => (e i).2, fun x hx => ?_⟩
  obtain ⟨o, y, h⟩ := he ⟨x, hx⟩
  refine ⟨o, y, y.2, ?_⟩
  have h2 := congrArg Subtype.val h
  simpa only [Submodule.coe_add, Submodule.coe_sum, Submodule.coe_smul,
      Submodule.coe_smul_of_tower] using h2

end GlobalTheory.GensModNsmul
