import Mathlib

open IsLocalRing

private theorem mem_smul_top_pi {R : Type} [CommRing R] (J : Ideal R) {r : ℕ} (x : Fin r → R) :
    x ∈ J • (⊤ : Submodule R (Fin r → R)) ↔ ∀ i, x i ∈ J := by
  constructor
  · intro hx
    refine Submodule.smul_induction_on hx (fun a ha y _ i => ?_) (fun a b ha hb i => ?_)
    · exact J.mul_mem_right _ ha
    · exact J.add_mem (ha i) (hb i)
  · intro hx
    rw [pi_eq_sum_univ x]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (hx i) Submodule.mem_top

private theorem isPrecomplete_pi {R : Type} [CommRing R] (I : Ideal R) [IsPrecomplete I R] (r : ℕ) :
    IsPrecomplete I (Fin r → R) := by
  refine ⟨fun f hf => ?_⟩
  have hc : ∀ i, ∃ L : R, ∀ n, f n i ≡ L [SMOD (I ^ n • ⊤ : Submodule R R)] := by
    intro i
    refine IsPrecomplete.prec (I := I) inferInstance (f := fun n => f n i) (fun {m n} hmn => ?_)
    have := (mem_smul_top_pi (I ^ m) _).1 (SModEq.sub_mem.1 (hf hmn)) i
    rw [SModEq.sub_mem, Ideal.smul_eq_mul, Ideal.mul_top]
    simpa using this
  choose L hL using hc
  refine ⟨L, fun n => ?_⟩
  rw [SModEq.sub_mem, mem_smul_top_pi]
  intro i
  have := SModEq.sub_mem.1 (hL i n)
  rw [Ideal.smul_eq_mul, Ideal.mul_top] at this
  simpa using this

private theorem isPrecomplete_finite {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] (I : Ideal R) [IsPrecomplete I R] : IsPrecomplete I M := by
  obtain ⟨r, π, hπ⟩ := Module.Finite.exists_fin' R M
  haveI := isPrecomplete_pi I r
  have hmap : ∀ n, Submodule.map π (I ^ n • ⊤) = I ^ n • (⊤ : Submodule R M) := by
    intro n
    rw [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.2 hπ]
  refine ⟨fun f hf => ?_⟩
  have hd : ∀ n, ∃ y ∈ (I ^ n • ⊤ : Submodule R (Fin r → R)), π y = f (n + 1) - f n := by
    intro n
    have : f (n + 1) - f n ∈ Submodule.map π (I ^ n • ⊤) := by
      rw [hmap]
      exact SModEq.sub_mem.1 (hf (Nat.le_succ n)).symm
    exact Submodule.mem_map.1 this
  choose d hdI hdπ using hd
  obtain ⟨g0, hg0⟩ := hπ (f 0)
  have hgπ : ∀ n, π (g0 + ∑ k ∈ Finset.range n, d k) = f n := by
    intro n
    induction n with
    | zero => simp [hg0]
    | succ n ih =>
      rw [Finset.sum_range_succ, ← add_assoc, map_add, ih, hdπ]
      abel
  have hcau : ∀ {m n : ℕ}, m ≤ n → (g0 + ∑ k ∈ Finset.range m, d k) ≡
      (g0 + ∑ k ∈ Finset.range n, d k) [SMOD (I ^ m • ⊤ : Submodule R (Fin r → R))] := by
    intro m n hmn
    rw [SModEq.sub_mem, ← Finset.sum_range_add_sum_Ico _ hmn]
    have e : g0 + ∑ k ∈ Finset.range m, d k
        - (g0 + (∑ k ∈ Finset.range m, d k + ∑ k ∈ Finset.Ico m n, d k))
        = -∑ k ∈ Finset.Ico m n, d k := by abel
    rw [e]
    refine Submodule.neg_mem _ (Submodule.sum_mem _ fun k hk => ?_)
    exact Submodule.smul_mono_left (Ideal.pow_le_pow_right (Finset.mem_Ico.1 hk).1) (hdI k)
  obtain ⟨L, hL⟩ := IsPrecomplete.prec (I := I) inferInstance
    (f := fun n => g0 + ∑ k ∈ Finset.range n, d k) hcau
  refine ⟨π L, fun n => ?_⟩
  rw [← hgπ n, SModEq.sub_mem, ← map_sub, ← hmap n]
  exact Submodule.mem_map_of_mem (SModEq.sub_mem.1 (hL n))

theorem UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.finCompl :
    ∀ (Λ M : Type) [CommRing Λ] [IsNoetherianRing Λ] (I : Ideal Λ) [IsAdicComplete I Λ] [AddCommGroup M] [Module Λ M] [Module.Finite Λ M], IsAdicComplete I M := by
  intro Λ M _ _ I _ _ _ _
  exact
    { toIsHausdorff := IsHausdorff.of_le_jacobson I M (IsAdicComplete.le_jacobson_bot I)
      toIsPrecomplete := isPrecomplete_finite I }
