import Mathlib

namespace GlobalTheory.CompanionTheory.JordanChain

open Module Submodule

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]

def chainVec (f : V →ₗ[K] V) {ι : Type} (e : ι → ℕ) (v : ι → V) : (Σ a, Fin (e a)) → V :=
  fun p => (f ^ (p.2 : ℕ)) (v p.1)

theorem pow_coe_of_restrict {W : Submodule K V} (f : V →ₗ[K] V) (g : W →ₗ[K] W)
    (hg : ∀ x, (g x : V) = f x) (k : ℕ) (x : W) : (((g ^ k) x : W) : V) = (f ^ k) x := by
  induction k generalizing x with
  | zero => simp
  | succ k ih => rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih, hg]

theorem exists_chains_of_range [FiniteDimensional K V] (f : V →ₗ[K] V)
    (g : LinearMap.range f →ₗ[K] LinearMap.range f) (hg : ∀ x, (g x : V) = f x)
    {ι' : Type} [Fintype ι'] (e' : ι' → ℕ) (he' : ∀ b, 0 < e' b) (w : ι' → LinearMap.range f)
    (h0 : ∀ b, (g ^ e' b) (w b) = 0) (hli : LinearIndependent K (chainVec g e' w))
    (hsp : span K (Set.range (chainVec g e' w)) = ⊤) :
    ∃ (ι : Type) (_ : Fintype ι) (e : ι → ℕ) (v : ι → V), (∀ a, 0 < e a) ∧
      (∀ a, (f ^ e a) (v a) = 0) ∧ LinearIndependent K (chainVec f e v) ∧
      span K (Set.range (chainVec f e v)) = ⊤ := by
  classical
  have hu : ∀ b, ∃ u, f u = (w b : V) := fun b => (w b).2
  choose u hu using hu
  have hstep : ∀ (b : ι') (j : ℕ), (f ^ (j + 1)) (u b) = (f ^ j) (w b : V) := by
    intro b j
    rw [pow_succ, Module.End.mul_apply, hu]
  set N := LinearMap.ker f with hN
  let t : ι' → V := fun b => (f ^ e' b) (u b)
  have htN : ∀ b, t b ∈ N := by
    intro b
    have h1 : f (t b) = (f ^ (e' b + 1)) (u b) := by
      simp only [t]
      rw [pow_succ', Module.End.mul_apply]
    rw [hN, LinearMap.mem_ker, h1, hstep, ← pow_coe_of_restrict f g hg, h0]
    rfl
  have hLV : LinearIndependent K (fun p => ((chainVec g e' w p : LinearMap.range f) : V)) :=
    hli.map' (LinearMap.range f).subtype (Submodule.ker_subtype _)
  let idx : ι' → Σ b, Fin (e' b) := fun b => ⟨b, ⟨e' b - 1, by have := he' b; omega⟩⟩
  have hidx : Function.Injective idx := fun a b h => congrArg Sigma.fst h
  have ht : LinearIndependent K t := by
    have h2 := hLV.comp idx hidx
    convert h2 using 1
    funext b
    simp only [t, Function.comp, idx, chainVec]
    rw [pow_coe_of_restrict f g hg, ← hstep]
    congr 2
    have := he' b
    omega
  let tN : ι' → N := fun b => ⟨t b, htN b⟩
  have htNli : LinearIndependent K tN := LinearIndependent.of_comp N.subtype ht
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl (span K (Set.range tN))
  let bC := Module.finBasis K C
  let z : Fin (finrank K C) → V := fun c => ((bC c : C) : N)
  have hz : ∀ c, f (z c) = 0 := fun c => ((bC c : C) : N).2
  let e : ι' ⊕ Fin (finrank K C) → ℕ := Sum.elim (fun b => e' b + 1) (fun _ => 1)
  let v : ι' ⊕ Fin (finrank K C) → V := Sum.elim u z
  let T := span K (Set.range (chainVec f e v))
  have hTu : ∀ (b : ι') (j : ℕ), j ≤ e' b → (f ^ j) (u b) ∈ T := by
    intro b j hj
    exact subset_span ⟨⟨Sum.inl b, ⟨j, Nat.lt_succ_of_le hj⟩⟩, rfl⟩
  have hTz : ∀ c, z c ∈ T := by
    intro c
    exact subset_span ⟨⟨Sum.inr c, ⟨0, Nat.one_pos⟩⟩, by simp [chainVec, v]⟩
  have hkerS : map N.subtype (span K (Set.range tN)) ≤ T := by
    refine (Submodule.map_span_le _ _ _).2 ?_
    rintro _ ⟨b, rfl⟩
    exact hTu b _ le_rfl
  have hkerC : map (N.subtype ∘ₗ C.subtype) ⊤ ≤ T := by
    rw [← bC.span_eq]
    refine (Submodule.map_span_le _ _ _).2 ?_
    rintro _ ⟨c, rfl⟩
    exact hTz c
  have hker : N ≤ T := by
    intro x hx
    have hx' : (⟨x, hx⟩ : N) ∈ span K (Set.range tN) ⊔ C := by rw [hC.sup_eq_top]; trivial
    obtain ⟨s, hs, c, hc, hsc⟩ := Submodule.mem_sup.1 hx'
    have hxe : x = (s : V) + (c : V) := by
      have := congrArg Subtype.val hsc
      simpa using this.symm
    rw [hxe]
    exact T.add_mem (hkerS ⟨s, hs, rfl⟩) (hkerC ⟨⟨c, hc⟩, trivial, rfl⟩)
  have hrange : ∀ y : LinearMap.range f, ∃ x ∈ T, f x = y := by
    have h3 : map (LinearMap.range f).subtype (span K (Set.range (chainVec g e' w))) ≤ map f T := by
      refine (Submodule.map_span_le _ _ _).2 ?_
      rintro _ ⟨⟨b, j⟩, rfl⟩
      refine ⟨(f ^ (j : ℕ)) (u b), hTu b _ j.2.le, ?_⟩
      simp only [chainVec, Submodule.subtype_apply]
      rw [pow_coe_of_restrict f g hg, ← hstep, pow_succ']
      rfl
    intro y
    have hy : (y : V) ∈ map (LinearMap.range f).subtype (span K (Set.range (chainVec g e' w))) := by
      rw [hsp]
      exact ⟨y, trivial, rfl⟩
    obtain ⟨x, hx, hxy⟩ := h3 hy
    exact ⟨x, hx, hxy⟩
  have hTtop : T = ⊤ := by
    refine eq_top_iff.2 fun x _ => ?_
    obtain ⟨x', hx', hxx⟩ := hrange ⟨f x, x, rfl⟩
    have hk : x - x' ∈ N := by
      rw [hN, LinearMap.mem_ker, map_sub, hxx]
      simp
    have := T.add_mem (hker hk) hx'
    simpa using this
  have hcard₁ : finrank K (LinearMap.range f) = ∑ b, e' b := by
    have h4 := finrank_span_eq_card hli
    rw [hsp, finrank_top] at h4
    rw [h4, Fintype.card_sigma]
    simp
  have hcard₂ : finrank K N = Fintype.card ι' + finrank K C := by
    have h5 := Submodule.finrank_add_eq_of_isCompl hC
    rw [finrank_span_eq_card htNli] at h5
    exact h5.symm
  have hcard : Fintype.card (Σ a, Fin (e a)) = finrank K V := by
    have h6 := LinearMap.finrank_range_add_finrank_ker f
    rw [Fintype.card_sigma, ← h6, hcard₁, ← hN, hcard₂]
    simp [e, Fintype.sum_sum_type, Finset.sum_add_distrib]
    omega
  refine ⟨ι' ⊕ Fin (finrank K C), inferInstance, e, v, ?_, ?_, ?_, hTtop⟩
  · rintro (b | c)
    · exact Nat.succ_pos _
    · exact Nat.one_pos
  · rintro (b | c)
    · change (f ^ (e' b + 1)) (u b) = 0
      rw [hstep, ← pow_coe_of_restrict f g hg, h0]
      rfl
    · change (f ^ 1) (z c) = 0
      simpa using hz c
  · exact linearIndependent_of_top_le_span_of_card_eq_finrank hTtop.ge hcard

theorem exists_chains : ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (f : V →ₗ[K] V), finrank K V = n → IsNilpotent f →
    ∃ (ι : Type) (_ : Fintype ι) (e : ι → ℕ) (v : ι → V), (∀ a, 0 < e a) ∧
      (∀ a, (f ^ e a) (v a) = 0) ∧ LinearIndependent K (chainVec f e v) ∧
      span K (Set.range (chainVec f e v)) = ⊤ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro V _ _ _ f hn hf
    by_cases hV : Subsingleton V
    · refine ⟨Empty, inferInstance, fun _ => 0, fun _ => 0, fun a => a.elim, fun a => a.elim,
        ?_, Subsingleton.elim _ _⟩
      exact linearIndependent_empty_type
    · have hnt : Nontrivial V := not_subsingleton_iff_nontrivial.1 hV
      obtain ⟨m, hm⟩ := hf
      have hlt : finrank K (LinearMap.range f) < n := by
        rw [← hn]
        refine Submodule.finrank_lt ?_
        intro htop
        have hsurj : Function.Surjective f := LinearMap.range_eq_top.1 htop
        have hs : Function.Surjective (f ^ m) := by
          rw [Module.End.coe_pow]
          exact hsurj.iterate m
        rw [hm] at hs
        obtain ⟨x, hx⟩ := exists_ne (0 : V)
        obtain ⟨y, hy⟩ := hs x
        exact hx (by simpa using hy.symm)
      let g : LinearMap.range f →ₗ[K] LinearMap.range f :=
        f.restrict (fun x _ => LinearMap.mem_range_self f x)
      have hg : ∀ x, (g x : V) = f x := fun x => rfl
      have hgn : IsNilpotent g := by
        refine ⟨m, LinearMap.ext fun x => Subtype.ext ?_⟩
        rw [pow_coe_of_restrict f g hg, hm]
        rfl
      obtain ⟨ι', _, e', w, he', h0, hli, hsp⟩ := ih _ hlt (LinearMap.range f) g rfl hgn
      exact exists_chains_of_range f g hg e' he' w h0 hli hsp

theorem exists_chain_basis {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (f : V →ₗ[K] V) (hf : IsNilpotent f) :
    ∃ (ι : Type) (_ : Fintype ι) (e : ι → ℕ) (v : ι → V), (∀ a, 0 < e a) ∧
      (∀ a, (f ^ e a) (v a) = 0) ∧
      LinearIndependent K (fun p : Σ a, Fin (e a) => (f ^ (p.2 : ℕ)) (v p.1)) ∧
      span K (Set.range (fun p : Σ a, Fin (e a) => (f ^ (p.2 : ℕ)) (v p.1))) = ⊤ :=
  exists_chains _ V f rfl hf

end GlobalTheory.CompanionTheory.JordanChain
