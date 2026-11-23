import Mathlib
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsSideBis

noncomputable section

namespace PositivityTheory.ThKH.Locrep

open Filter Topology

theorem eq_one_of_pow_near {R : Type} [NormedRing R] [NormedAlgebra ℂ R] {a : R} (h : ∀ p : ℕ, ‖a ^ p - 1‖ < 1 / 2) :
    a = 1 :=
  _root_.UpperTheory.Reformulated.B.Yhd7.main h

theorem linearIndependent_of_notMem {V : Type} [AddCommGroup V] [Module ℂ V] (u : ℕ → V) (T : ℕ → Set V)
    (h1 : ∀ m n, m < n → u m ∈ T n) (h2 : ∀ n, u n ∉ Submodule.span ℂ (T n)) : LinearIndependent ℂ u := by
  classical
  rw [linearIndependent_iff']
  intro s g
  induction s using Finset.induction_on_max with
  | empty => simp
  | insert a s hs ih =>
    intro hsum
    have ha : a ∉ s := fun h => lt_irrefl _ (hs a h)
    rw [Finset.sum_insert ha] at hsum
    have h0 : g a = 0 := by
      by_contra hne
      refine h2 a ((Submodule.smul_mem_iff _ hne).1 ?_)
      rw [eq_neg_of_add_eq_zero_left hsum]
      exact neg_mem (Submodule.sum_mem _ fun i hi =>
        Submodule.smul_mem _ _ (Submodule.subset_span (h1 i a (hs i hi))))
    rw [h0, zero_smul, zero_add] at hsum
    intro i hi
    rcases Finset.mem_insert.1 hi with rfl | hi
    · exact h0
    · exact ih hsum i hi

theorem exists_finite_orbit {G V : Type} [Group G] [TopologicalSpace G] [AddCommGroup V] [Module ℂ V]
    (K : ℕ → Subgroup G) (hanti : Antitone K) (hbasis : ∀ U ∈ 𝓝 (1 : G), ∃ n, (K n : Set G) ⊆ U)
    (f : G → V) (h1 : f 1 = 0) (hcont : ∀ l : V →ₗ[ℂ] ℂ, Continuous fun g => l (f g)) :
    ∃ n, ∃ s : Finset V, ∀ k ∈ K n, f k ∈ Submodule.span ℂ (s : Set V) := by
  classical
  by_contra hne
  push Not at hne
  choose c hc hc' using hne
  obtain ⟨T, hT⟩ : ∃ T : ℕ → Finset V, ∀ n, T (n + 1) = insert (f (c n (T n))) (T n) :=
    ⟨fun n => Nat.rec ∅ (fun n t => insert (f (c n t)) t) n, fun _ => rfl⟩
  have hli : LinearIndependent ℂ fun n => f (c n (T n)) := by
    refine linearIndependent_of_notMem (fun n => f (c n (T n))) (fun n => (T n : Set V)) (fun m n hmn => ?_)
      fun n => hc' n (T n)
    beta_reduce
    induction n, hmn using Nat.le_induction with
    | base => rw [Nat.succ_eq_add_one, hT]; exact Finset.mem_coe.2 (Finset.mem_insert_self _ _)
    | succ n _ ih => rw [hT]; exact Finset.mem_coe.2 (Finset.mem_insert_of_mem ih)
  obtain ⟨l, hl⟩ := LinearMap.exists_extend ((Module.Basis.span hli).constr ℂ fun _ => (1 : ℂ))
  have hl1 : ∀ n, l (f (c n (T n))) = 1 := fun n => by
    have := congrArg (fun L => L (Module.Basis.span hli n)) hl
    simp only [Module.Basis.constr_basis] at this
    simpa [Module.Basis.span_apply] using this
  have hU : {g | l (f g) ≠ 1} ∈ 𝓝 (1 : G) :=
    (isOpen_ne_fun (hcont l) continuous_const).mem_nhds (by simp [h1])
  obtain ⟨n, hn⟩ := hbasis _ hU
  exact hn (hc n (T n)) (hl1 n)

theorem smooth_of_weak {G V : Type} [Group G] [TopologicalSpace G] [AddCommGroup V] [Module ℂ V] (W : Submodule ℂ V)
    (K : ℕ → Subgroup G) (hanti : Antitone K) (hbasis : ∀ U ∈ 𝓝 (1 : G), ∃ n, (K n : Set G) ⊆ U)
    (ω : G → Module.End ℂ V) (hpres : ∀ g ∈ K 0, ∀ φ ∈ W, ω g φ ∈ W) (hone : ∀ φ ∈ W, ω 1 φ = φ)
    (hmul : ∀ g ∈ K 0, ∀ g' ∈ K 0, ∀ φ ∈ W, ω (g * g') φ = ω g (ω g' φ))
    (hcont : ∀ l : V →ₗ[ℂ] ℂ, ∀ φ ∈ W, Continuous fun g => l (ω g φ)) :
    ∀ φ ∈ W, ∃ n, ∀ k ∈ K n, ω k φ = φ := by
  classical
  intro φ hφ
  obtain ⟨n, s, hs⟩ := exists_finite_orbit K hanti hbasis (fun g => ω g φ - φ) (by simp [hone φ hφ]) fun l => by
    simp only [map_sub]
    exact (hcont l φ hφ).sub continuous_const
  have h0 : ∀ k ∈ K n, k ∈ K 0 := fun k hk => hanti (Nat.zero_le n) hk
  let V₀ : Submodule ℂ V := Submodule.span ℂ ((fun k => ω k φ) '' (K n : Set G))
  have hW : V₀ ≤ W := Submodule.span_le.2 (by rintro _ ⟨k, hk, rfl⟩; exact hpres k (h0 k hk) φ hφ)
  have hφ₀ : φ ∈ V₀ := Submodule.subset_span ⟨1, (K n).one_mem, hone φ hφ⟩
  have hinv : ∀ k ∈ K n, ∀ x ∈ V₀, ω k x ∈ V₀ := fun k hk x hx => by
    have : V₀ ≤ V₀.comap (ω k) := Submodule.span_le.2 (by
      rintro _ ⟨k', hk', rfl⟩
      exact Submodule.subset_span ⟨k * k', (K n).mul_mem hk hk', hmul k (h0 k hk) k' (h0 k' hk') φ hφ⟩)
    exact this hx
  have : FiniteDimensional ℂ V₀ := by
    have hle : V₀ ≤ Submodule.span ℂ ((insert φ s : Finset V) : Set V) := Submodule.span_le.2 (by
      rintro _ ⟨k, hk, rfl⟩
      have e : ω k φ = (ω k φ - φ) + φ := by abel
      change ω k φ ∈ Submodule.span ℂ _
      rw [e]
      exact add_mem (Submodule.span_mono (by simp) (hs k hk)) (Submodule.subset_span (by simp)))
    exact Submodule.finiteDimensional_of_le hle
  let b := (Module.finBasis ℂ V₀).equivFun
  obtain ⟨π, hπ⟩ := LinearMap.exists_extend (b : V₀ →ₗ[ℂ] (Fin (Module.finrank ℂ V₀) → ℂ))
  let j : (Fin (Module.finrank ℂ V₀) → ℂ) →ₗ[ℂ] V := V₀.subtype ∘ₗ (b.symm : _ →ₗ[ℂ] V₀)
  have hj : ∀ x, j x ∈ V₀ := fun x => (b.symm x).2
  have hπ' : ∀ y : V₀, π y = b y := fun y => congrArg (fun L => L y) hπ
  have hjπ : ∀ x ∈ V₀, j (π x) = x := fun x hx => by
    rw [hπ' ⟨x, hx⟩]
    change ((b.symm (b ⟨x, hx⟩) : V₀) : V) = x
    rw [b.symm_apply_apply]
  have hπj : ∀ x, π (j x) = x := fun x => by
    change π (b.symm x : V₀) = x
    rw [hπ', b.apply_symm_apply]
  let A : G → (Fin (Module.finrank ℂ V₀) → ℂ) →L[ℂ] (Fin (Module.finrank ℂ V₀) → ℂ) :=
    fun g => LinearMap.toContinuousLinearMap (π ∘ₗ ω g ∘ₗ j)
  have hA : ∀ g x, A g x = π (ω g (j x)) := fun _ _ => rfl
  have hAc : Continuous A := continuous_clm_apply.2 fun x => continuous_pi fun i =>
    hcont (LinearMap.proj i ∘ₗ π) (j x) (hW (hj x))
  have hA1 : A 1 = 1 := by
    ext1 x
    rw [hA, hone _ (hW (hj x)), hπj]; rfl
  have hAp : ∀ k ∈ K n, ∀ p : ℕ, A (k ^ p) = A k ^ p := fun k hk p => by
    induction p with
    | zero => rw [pow_zero, pow_zero, hA1]
    | succ p ih =>
      ext1 x
      rw [pow_succ', pow_succ', ← ih, mul_apply_eq_comp, hA, hA, hA,
        hjπ _ (hinv _ ((K n).pow_mem hk p) _ (hj x)), hmul k (h0 k hk) _ (h0 _ ((K n).pow_mem hk p)) _ (hW (hj x))]
  have hU : {g | ‖A g - 1‖ < 1 / 2} ∈ 𝓝 (1 : G) :=
    (isOpen_lt (hAc.sub continuous_const).norm continuous_const).mem_nhds (by simp [hA1])
  obtain ⟨m, hm⟩ := hbasis _ hU
  refine ⟨max n m, fun k hk => ?_⟩
  have hkn : k ∈ K n := hanti (le_max_left n m) hk
  have hkm : k ∈ K m := hanti (le_max_right n m) hk
  have hk1 : A k = 1 := eq_one_of_pow_near fun p => by
    rw [← hAp k hkn]
    exact hm ((K m).pow_mem hkm p)
  have := hA k (π φ)
  rw [hk1, hjπ φ hφ₀, one_apply_eq_self] at this
  rw [← hjπ _ (hinv k hkn φ hφ₀), ← this, hjπ φ hφ₀]

end PositivityTheory.ThKH.Locrep
