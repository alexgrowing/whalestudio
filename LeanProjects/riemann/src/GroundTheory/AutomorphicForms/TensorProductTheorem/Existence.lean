import Mathlib
import GroundTheory.AutomorphicForms.TensorProductTheorem.Places

noncomputable section

universe u

namespace GroundTheory.Automorphic

namespace RestrictedTensor

open Filter Function Module Set PiTensorProduct

open scoped TensorProduct RestrictedProduct

section FiniteDim

variable {M : Type*} [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M]

theorem exists_rankOne_simple (T : Set (End ℂ M)) [Nontrivial M] :
    ∃ (N : Submodule ℂ M) (hN : IsStable T N), N ≠ ⊥ ∧ IsSimpleUnder (restrictSet T N hN) ∧
      ∃ p ∈ Algebra.adjoin ℂ T, ∃ n₀ ∈ N, n₀ ≠ 0 ∧ p n₀ = n₀ ∧ ∀ x ∈ N, ∃ c : ℂ, p x = c • n₀ := by
  obtain ⟨N, hNs, hN0, hsimple⟩ := exists_simple_stable T
  have := hsimple.1
  obtain ⟨n, hn⟩ := exists_ne (0 : N)
  obtain ⟨f, hf⟩ : ∃ f : Module.Dual ℂ N, f n = 1 := by
    obtain ⟨f, hf⟩ : ∃ f : Module.Dual ℂ N, f n ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hn ((Module.forall_dual_apply_eq_zero_iff ℂ n).1 hcon)
    exact ⟨(f n)⁻¹ • f, by simp [hf]⟩
  let b : End ℂ N := f.smulRight n
  have hb : b ∈ Algebra.adjoin ℂ (restrictSet T N hNs) := by
    rw [adjoin_eq_top hsimple]; trivial
  obtain ⟨p, hp, hpb⟩ := exists_of_mem_adjoin_restrictSet hNs hb
  refine ⟨N, hNs, hN0, hsimple, p, hp, n, n.2, fun h => hn (Subtype.ext h), ?_, ?_⟩
  · rw [← hpb n]
    simp [b, hf]
  · intro x hx
    refine ⟨f ⟨x, hx⟩, ?_⟩
    rw [← hpb ⟨x, hx⟩]
    simp [b]

variable {ι : Type*} {T : ι → Set (End ℂ M)}

theorem commute_adjoin (hcomm : ∀ v w, v ≠ w → ∀ a ∈ T v, ∀ b ∈ T w, Commute a b)
    {v w : ι} (hvw : v ≠ w) {a b : End ℂ M} (ha : a ∈ Algebra.adjoin ℂ (T v))
    (hb : b ∈ Algebra.adjoin ℂ (T w)) : Commute a b :=
  commute_of_mem_adjoin (fun t ht =>
    (commute_of_mem_adjoin (fun s hs => (hcomm v w hvw s hs t ht).symm) a ha).symm) b hb

theorem eq_zero_of_place (hsimple : IsSimpleUnder (⋃ v, T v))
    (hcomm : ∀ v w, v ≠ w → ∀ a ∈ T v, ∀ b ∈ T w, Commute a b) (v : ι) {N : Submodule ℂ M}
    (hN : N ≠ ⊥) (hNs : IsStable (T v) N) {a : End ℂ M} (ha : a ∈ Algebra.adjoin ℂ (T v))
    (h0 : ∀ x ∈ N, a x = 0) : a = 0 := by
  have hunion : T v ∪ (⋃ w ∈ ({v}ᶜ : Set ι), T w) = ⋃ w, T w := by
    ext t
    simp only [mem_union, mem_iUnion, mem_compl_iff, mem_singleton_iff, exists_prop]
    constructor
    · rintro (ht | ⟨w, -, ht⟩)
      exacts [⟨v, ht⟩, ⟨w, ht⟩]
    · rintro ⟨w, ht⟩
      by_cases hw : w = v
      · subst hw; exact Or.inl ht
      · exact Or.inr ⟨w, hw, ht⟩
  have hc : ∀ s ∈ T v, ∀ t ∈ ⋃ w ∈ ({v}ᶜ : Set ι), T w, Commute s t := by
    intro s hs t ht
    simp only [mem_iUnion, mem_compl_iff, mem_singleton_iff, exists_prop] at ht
    obtain ⟨w, hw, ht⟩ := ht
    exact hcomm v w (Ne.symm hw) s hs t ht
  refine eq_zero_of_forall_mem (hunion ▸ hsimple) hc hN hNs (fun t ht => ?_) h0
  exact (commute_of_mem_adjoin (fun s hs => (hc s hs t ht).symm) a ha).symm

end FiniteDim

section Coefficient

variable {ι : Type*} {G : ι → Type*} [∀ v, Group (G v)] [∀ v, TopologicalSpace (G v)]
  [∀ v, IsTopologicalGroup (G v)] [∀ v, LocallyCompactSpace (G v)] [∀ v, T2Space (G v)]
  [∀ v, TotallyDisconnectedSpace (G v)]
  {K : ∀ v, Subgroup (G v)} [hKo : Fact (∀ v, IsOpen (K v : Set (G v)))]
  [hKc : ∀ v, CompactSpace (K v)]
  {V : Type*} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ (Πʳ v, [G v, K v]) V}
  {W : ι → Type*} [∀ v, AddCommGroup (W v)] [∀ v, Module ℂ (W v)]
  {π : ∀ v, Representation ℂ (G v) (W v)} {ξ : ∀ v, W v}

theorem nonempty_equiv_of_coeff (hρirr : ρ.IsIrreducible) (hπ : ∀ v, IsAdmissible (π v))
    (hirr : ∀ v, (π v).IsIrreducible) (hξ : ∀ᶠ v in cofinite, ξ v ∈ fixedVectors (π v) (K v))
    (hξ0 : ∀ᶠ v in cofinite, ξ v ≠ 0)
    (hgel : ∀ᶠ v in cofinite, ∀ u ∈ fixedVectors (π v) (K v), ∃ c : ℂ, u = c • ξ v)
    (x : V) (Λ : Dual ℂ V) (l : ∀ v, Dual ℂ (W v)) (hl : ∀ᶠ v in cofinite, l v (ξ v) = 1)
    (hcoef : ∀ g : Πʳ v, [G v, K v], Λ (ρ g x) = ∏ᶠ v, l v (π v (g v) (ξ v)))
    (hne : Λ x ≠ 0) :
    Nonempty (ρ.Equiv (restrictedTensorRep π ξ hξ)) := by
  haveI := hρirr
  haveI := isIrreducible_restrictedTensorRep hπ hirr hξ hξ0 hgel
  refine nonempty_equiv_of_matrixCoeff_eq (v := x) (l := Λ)
    (w := ⟨tprod ℂ ξ, tprod_mem_restrictedTensor (isRestricted_self ξ)⟩)
    (m := evalForm ξ l hl ∘ₗ (restrictedTensor ξ).subtype) (fun g => ?_) ⟨1, by rwa [map_one]⟩
  rw [hcoef g]
  have hr : IsRestricted ξ fun v => π v (g v) (ξ v) := by
    filter_upwards [g.2, hξ] with v h1 h2
    exact h2 _ h1
  show _ = evalForm ξ l hl (tensorRep K π g (tprod ℂ ξ))
  rw [tensorRep_tprod, evalForm_tprod hr]

end Coefficient

section Main

variable {ι : Type*} {G : ι → Type*} [∀ v, Group (G v)] [∀ v, TopologicalSpace (G v)]
  [∀ v, IsTopologicalGroup (G v)] [∀ v, LocallyCompactSpace (G v)] [∀ v, T2Space (G v)]
  [∀ v, TotallyDisconnectedSpace (G v)]
  {K : ∀ v, Subgroup (G v)} [hKo : Fact (∀ v, IsOpen (K v : Set (G v)))]
  [hKc : ∀ v, CompactSpace (K v)]
  {V : Type u} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ (Πʳ v, [G v, K v]) V}

theorem isSmooth_comp_singleHom [DecidableEq ι] (hρ : IsSmooth ρ) (v : ι) :
    IsSmooth (ρ.comp (singleHom K v)) := by
  intro u
  obtain ⟨B, hBc, hBo, -, -, hsub⟩ := exists_boxSubgroup_subset
    (fun v => isCompact_iff_compactSpace.2 (hKc v)) ((hρ u).mem_nhds (stabilizerOf ρ u).one_mem)
  refine Subgroup.isOpen_mono (H₁ := B v) (fun k hk => ?_) (hBo v)
  exact hsub (singleHom_mem_boxSubgroup hk)

theorem exists_equiv_restrictedTensorRep (hρ : IsAdmissible ρ) (hirr : ρ.IsIrreducible)
    (hgel : ∀ᶠ v in cofinite, ∀ (W : Type u) [AddCommGroup W] [Module ℂ W]
      (σ : Representation ℂ (G v) W), IsAdmissible σ → σ.IsIrreducible →
        Module.finrank ℂ (fixedVectors σ (K v)) ≤ 1) :
    ∃ (W : ι → Type u) (_ : ∀ v, AddCommGroup (W v)) (_ : ∀ v, Module ℂ (W v))
      (π : ∀ v, Representation ℂ (G v) (W v)) (ξ : ∀ v, W v)
      (hξ : ∀ᶠ v in cofinite, ξ v ∈ fixedVectors (π v) (K v)),
      (∀ v, IsAdmissible (π v)) ∧ (∀ v, (π v).IsIrreducible) ∧ (∀ᶠ v in cofinite, ξ v ≠ 0) ∧
        Nonempty (ρ.Equiv (restrictedTensorRep π ξ hξ)) := by
  classical
  have hρs := hρ.1
  have hKcs : ∀ v, IsCompact (K v : Set (G v)) := fun v => isCompact_iff_compactSpace.2 (hKc v)
  haveI := hirr

  have hVnt := nontrivial_of_isIrreducible hirr
  obtain ⟨x₀, hx₀⟩ := exists_ne (0 : V)
  obtain ⟨K', hK'c, hK'o, -, hK'e, hsub⟩ := exists_boxSubgroup_subset hKcs
    ((hρs x₀).mem_nhds (stabilizerOf ρ x₀).one_mem)
  set H := boxSubgroup K K' with hHdef
  have hHc : IsCompact (H : Set (Πʳ v, [G v, K v])) := isCompact_boxSubgroup_of_eq hK'c hK'e
  have hHo : IsOpen (H : Set (Πʳ v, [G v, K v])) := isOpen_boxSubgroup hK'o hK'e
  set M := fixedVectors ρ H
  have hx₀H : x₀ ∈ M := fun h hh => hsub hh
  have hMne : M ≠ ⊥ := fun h => hx₀ (by
    have : x₀ ∈ (⊥ : Submodule ℂ V) := h ▸ hx₀H
    simpa using this)
  have hMnt : Nontrivial M := Submodule.nontrivial_iff_ne_bot.2 hMne
  have hMfin : FiniteDimensional ℂ M := hρ.2 H hHc hHo
  set Tp : ι → Set (End ℂ M) := fun v => placeOps hρs hK'c hK'o hK'e v

  have hcomm : ∀ v w, v ≠ w → ∀ a ∈ Tp v, ∀ b ∈ Tp w, Commute a b :=
    fun v w h => commute_placeOps hρs hK'c hK'o hK'e h
  have hsimple : IsSimpleUnder (⋃ v, Tp v) := by
    have h0 := isSimpleUnder_heckeOps hρs hHc hHo hMne
    refine ⟨h0.1, fun p hp => h0.2 p ?_⟩
    rintro _ ⟨g, rfl⟩
    have hfin : {v | g v ∉ K' v}.Finite := Filter.eventually_cofinite.1
      ((g.2.and hK'e).mono fun v h => by rw [h.2]; exact h.1)
    have hmem := heckeOp_mem_adjoin hρs hK'c hK'o hK'e hfin.toFinset (g := g)
      (fun v hv => by simpa using hv)
    refine IsStable.adjoin (IsStable.mono hp ?_) _ hmem
    intro t ht
    simp only [mem_iUnion] at ht ⊢
    obtain ⟨v, -, ht⟩ := ht
    exact ⟨v, ht⟩
  have hvanish := fun v (N : Submodule ℂ M) (hN : N ≠ ⊥) (hNs : IsStable (Tp v) N)
      (a : End ℂ M) (ha : a ∈ Algebra.adjoin ℂ (Tp v)) (h0 : ∀ x ∈ N, a x = 0) =>
    eq_zero_of_place hsimple hcomm v hN hNs ha h0

  have hdata := fun v => exists_rankOne_simple (Tp v)
  choose N hNst hN0 hNsimple p hp n hnN hn0 hpn hpN using hdata
  have hTmem : ∀ v (x : G v), heckeOp hρs hHc hHo (singleHom K v x) ∈ Tp v := fun v x => ⟨x, rfl⟩
  have hpp : ∀ v, p v * p v = p v := by
    intro v
    rw [← sub_eq_zero]
    refine hvanish v (N v) (hN0 v) (hNst v) _ (Subalgebra.sub_mem _
      (Subalgebra.mul_mem _ (hp v) (hp v)) (hp v)) fun x hx => ?_
    obtain ⟨d, hd⟩ := hpN v x hx
    rw [LinearMap.sub_apply, Module.End.mul_apply, hd, map_smul, hpn v, sub_self]
  have hcex : ∀ v (x : G v), ∃ c : ℂ,
      p v (heckeOp hρs hHc hHo (singleHom K v x) (n v)) = c • n v :=
    fun v x => hpN v _ (hNst v _ (hTmem v x) (n v) (hnN v))
  choose c hc using hcex
  have hpTp : ∀ v (x : G v), p v * heckeOp hρs hHc hHo (singleHom K v x) * p v = c v x • p v := by
    intro v x
    rw [← sub_eq_zero]
    refine hvanish v (N v) (hN0 v) (hNst v) _ (Subalgebra.sub_mem _ (Subalgebra.mul_mem _
      (Subalgebra.mul_mem _ (hp v) (Algebra.subset_adjoin (hTmem v x))) (hp v))
      (Subalgebra.smul_mem _ (hp v) _)) fun y hy => ?_
    obtain ⟨d, hd⟩ := hpN v y hy
    rw [LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply, hd, map_smul, map_smul,
      hc v x, LinearMap.smul_apply, hd, smul_comm, sub_self]
  have hc1 : ∀ v, ∀ x ∈ K' v, c v x = 1 := by
    intro v x hx
    have h1 := hc v x
    rw [heckeOp_of_mem hρs hHc hHo (singleHom_mem_boxSubgroup hx), Module.End.one_apply,
      hpn v] at h1
    have h2 : (c v x - 1) • n v = 0 := by rw [sub_smul, ← h1, one_smul, sub_self]
    rcases smul_eq_zero.1 h2 with h | h
    · exact sub_eq_zero.1 h
    · exact absurd h (hn0 v)

  have hρv : ∀ v, IsSmooth (ρ.comp (singleHom K v)) := isSmooth_comp_singleHom hρs
  set NV : ∀ v, Submodule ℂ V := fun v => (N v).map M.subtype
  have hNK : ∀ v, NV v ≤ fixedVectors (ρ.comp (singleHom K v)) (K' v) := by
    rintro v _ ⟨m, -, rfl⟩ k hk
    exact m.2 _ (singleHom_mem_boxSubgroup hk)
  have hproj : ∀ v (x : G v) (m : M),
      (fixedProj (ρ.comp (singleHom K v)) (hρv v) (hK'c v) (hK'o v)
        (ρ (singleHom K v x) m) : V) = (heckeOp hρs hHc hHo (singleHom K v x) m : V) :=
    fun v x m => fixedProj_single_eq hρs hK'c hK'o hK'e v (hρv v)
      (fun h hh hv => apply_single_fixed v x m.2 hh hv)
  have hNst' : ∀ v g, ∀ u ∈ NV v, (fixedProj (ρ.comp (singleHom K v)) (hρv v) (hK'c v)
      (hK'o v) ((ρ.comp (singleHom K v)) g u) : V) ∈ NV v := by
    rintro v g _ ⟨m, hm, rfl⟩
    simp only [MonoidHom.coe_comp, Function.comp_apply, Submodule.subtype_apply]
    rw [hproj v g m]
    exact ⟨_, hNst v _ (hTmem v g) m hm, rfl⟩
  have hNV0 : ∀ v, NV v ≠ ⊥ := by
    intro v h
    apply hn0 v
    have : (n v : V) ∈ NV v := ⟨n v, hnN v, rfl⟩
    rw [h, Submodule.mem_bot] at this
    exact Subtype.ext this
  have hNmin : ∀ v, ∀ N₁ : Submodule ℂ V, N₁ ≤ NV v → N₁ ≠ ⊥ →
      (∀ g, ∀ u ∈ N₁, (fixedProj (ρ.comp (singleHom K v)) (hρv v) (hK'c v) (hK'o v)
        ((ρ.comp (singleHom K v)) g u) : V) ∈ N₁) → N₁ = NV v := by
    intro v N₁ hle hne hst
    set q : Submodule ℂ (N v) := (N₁.comap M.subtype).comap (N v).subtype
    have hq : IsStable (restrictSet (Tp v) (N v) (hNst v)) q := by
      rintro _ ⟨⟨_, ⟨x, rfl⟩⟩, rfl⟩ y hy
      show ((heckeOp hρs hHc hHo (singleHom K v x) y : M) : V) ∈ N₁
      rw [← hproj v x y]
      exact hst x _ hy
    have hq0 : q ≠ ⊥ := by
      obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
      obtain ⟨m, hm, rfl⟩ := hle hu
      intro h
      have : (⟨m, hm⟩ : N v) ∈ q := hu
      rw [h, Submodule.mem_bot] at this
      have hm0 : m = 0 := congrArg Subtype.val this
      exact hu0 (by simp [hm0])
    have hqt := ((hNsimple v).2 q hq).resolve_left hq0
    refine le_antisymm hle ?_
    rintro _ ⟨m, hm, rfl⟩
    have : (⟨m, hm⟩ : N v) ∈ q := hqt ▸ Submodule.mem_top
    exact this
  set π : ∀ v, Representation ℂ (G v) _ :=
    fun v => genQuotRep (hρv v) (hK'c v) (hK'o v) (NV v)
  have hπirr : ∀ v, (π v).IsIrreducible := fun v =>
    isIrreducible_genQuotRep (hρv v) (hK'c v) (hK'o v) (hNK v) (hNst' v) (hNV0 v) (hNmin v)

  have hgenfix : ∀ v, ∀ u ∈ (genSubrep (ρ.comp (singleHom K v)) (NV v)).toSubmodule,
      ∀ h ∈ H, h v = 1 → ρ h u = u := by
    intro v u hu
    have hle : (genSubrep (ρ.comp (singleHom K v)) (NV v)).toSubmodule ≤
        { carrier := {u | ∀ h ∈ H, h v = 1 → ρ h u = u}
          add_mem' := fun ha hb h hh hv => by rw [map_add, ha h hh hv, hb h hh hv]
          zero_mem' := fun h _ _ => map_zero _
          smul_mem' := fun c u hu h hh hv => by rw [map_smul, hu h hh hv] } := by
      refine iSup_le fun g => ?_
      rintro _ ⟨_, ⟨m, -, rfl⟩, rfl⟩ h hh hv
      exact apply_single_fixed v g m.2 hh hv
    exact hle hu
  have hπadm : ∀ v, IsAdmissible (π v) := by
    intro v
    refine isAdmissible_genQuotRep (hρv v) (hK'c v) (hK'o v) fun K₁ hK₁c hK₁o => ?_
    set K'' : ∀ w, Subgroup (G w) := Function.update K' v K₁
    have hK''c : ∀ w, IsCompact (K'' w : Set (G w)) := fun w => by
      by_cases hw : w = v
      · subst hw; simpa [K''] using hK₁c
      · simpa [K'', hw] using hK'c w
    have hK''o : ∀ w, IsOpen (K'' w : Set (G w)) := fun w => by
      by_cases hw : w = v
      · subst hw; simpa [K''] using hK₁o
      · simpa [K'', hw] using hK'o w
    have hK''e : ∀ᶠ w in cofinite, K'' w = K w := by
      filter_upwards [hK'e, (Set.finite_singleton v).compl_mem_cofinite] with w h1 h2
      simp only [mem_compl_iff, mem_singleton_iff] at h2
      simp [K'', h2, h1]
    have hfinbox := hρ.2 _ (isCompact_boxSubgroup_of_eq hK''c hK''e)
      (isOpen_boxSubgroup hK''o hK''e)
    have hmap : ∀ u : fixedVectors (genSubrep (ρ.comp (singleHom K v)) (NV v)).toRepresentation K₁,
        ((u : (genSubrep (ρ.comp (singleHom K v)) (NV v)).toSubmodule) : V) ∈
          fixedVectors ρ (boxSubgroup K K'') := by
      intro u h hh
      have hu1 := hgenfix v _ (u : (genSubrep (ρ.comp (singleHom K v)) (NV v)).toSubmodule).2
      have hhv : h v ∈ K₁ := by simpa [K''] using hh v
      have herase : eraseAt v h ∈ H := by
        intro w
        by_cases hw : w = v
        · subst hw; rw [eraseAt_apply_self]; exact (K' w).one_mem
        · rw [eraseAt_apply_of_ne _ hw]; simpa [K'', hw] using hh w
      conv_lhs => rw [← single_mul_eraseAt v h]
      rw [map_mul, Module.End.mul_apply, hu1 _ herase (eraseAt_apply_self v h)]
      have := u.2 (h v) hhv
      exact congrArg Subtype.val this
    let f : fixedVectors (genSubrep (ρ.comp (singleHom K v)) (NV v)).toRepresentation K₁ →ₗ[ℂ]
        fixedVectors ρ (boxSubgroup K K'') :=
      LinearMap.codRestrict _ ((genSubrep (ρ.comp (singleHom K v)) (NV v)).toSubmodule.subtype ∘ₗ
        Submodule.subtype _) hmap
    exact Module.Finite.of_injective f fun a b h => by
      have := congrArg Subtype.val h
      exact Subtype.ext (Subtype.ext this)
  set ξ : ∀ v, _ := fun v => genQuotMk (hρv v) (hK'c v) (hK'o v) (NV v) ⟨n v, ⟨n v, hnN v, rfl⟩⟩
  have hξK' : ∀ v, ξ v ∈ fixedVectors (π v) (K' v) :=
    fun v => genQuotMk_mem_fixedVectors (hρv v) (hK'c v) (hK'o v) (hNK v) _
  have hξ : ∀ᶠ v in cofinite, ξ v ∈ fixedVectors (π v) (K v) :=
    hK'e.mono fun v h => h ▸ hξK' v
  have hξ0 : ∀ v, ξ v ≠ 0 := by
    intro v h
    have := genQuotMk_injective (hρv v) (hK'c v) (hK'o v) (hNK v)
      (a₁ := ⟨n v, ⟨n v, hnN v, rfl⟩⟩) (a₂ := 0) (by rw [map_zero]; exact h)
    exact hn0 v (Subtype.ext (by simpa using congrArg Subtype.val this))

  set S : Finset ι := (Filter.eventually_cofinite.1 (hK'e.and hgel)).toFinset
  have hS : ∀ v ∉ S, K' v = K v ∧ Module.finrank ℂ (fixedVectors (π v) (K v)) ≤ 1 := by
    intro v hv
    simp only [S, Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_not] at hv
    exact ⟨hv.1, hv.2 _ (π v) (hπadm v) (hπirr v)⟩
  have hline : ∀ {E : Type u} [AddCommGroup E] [Module ℂ E] (F : Submodule ℂ E)
      [FiniteDimensional ℂ F], Module.finrank ℂ F ≤ 1 → ∀ e ∈ F, e ≠ 0 → ∀ y ∈ F, ∃ d : ℂ,
        y = d • e := by
    intro E _ _ F _ hF e he he0 y hy
    have hle : Submodule.span ℂ {e} ≤ F := (Submodule.span_singleton_le_iff_mem _ _).2 he
    have heq : Submodule.span ℂ {e} = F := Submodule.eq_of_le_of_finrank_le hle
      (hF.trans (by rw [finrank_span_singleton he0]))
    rw [← heq, Submodule.mem_span_singleton] at hy
    obtain ⟨d, rfl⟩ := hy
    exact ⟨d, rfl⟩
  have hgelξ : ∀ᶠ v in cofinite, ∀ y ∈ fixedVectors (π v) (K v), ∃ d : ℂ, y = d • ξ v := by
    refine Filter.eventually_cofinite.2 (S.finite_toSet.subset fun v hv => ?_)
    by_contra hvS
    apply hv
    have h := hS v hvS
    have : FiniteDimensional ℂ (fixedVectors (π v) (K v)) :=
      (hπadm v).2 _ (hKcs v) (hKo.out v)
    exact hline _ h.2 _ (h.1 ▸ hξK' v) (hξ0 v)
  have hscalar : ∀ v ∉ S, ∀ x : G v, heckeOp hρs hHc hHo (singleHom K v x) =
      algebraMap ℂ (End ℂ M) (c v x) := by
    intro v hv x
    obtain ⟨hK'v, hrank⟩ := hS v hv

    have hNline : ∀ y ∈ N v, ∃ d : ℂ, y = d • n v := by
      let e : N v →ₗ[ℂ] fixedVectors (π v) (K v) :=
        LinearMap.codRestrict _ (genQuotMk (hρv v) (hK'c v) (hK'o v) (NV v) ∘ₗ
          (Submodule.equivMapOfInjective M.subtype M.injective_subtype (N v)).toLinearMap)
          fun y => hK'v ▸ genQuotMk_mem_fixedVectors (hρv v) (hK'c v) (hK'o v) (hNK v) _
      have he : Function.Injective e := fun a b h => by
        have := genQuotMk_injective (hρv v) (hK'c v) (hK'o v) (hNK v)
          (congrArg Subtype.val h)
        exact (Submodule.equivMapOfInjective M.subtype M.injective_subtype (N v)).injective this
      have : FiniteDimensional ℂ (fixedVectors (π v) (K v)) :=
        (hπadm v).2 _ (hKcs v) (hKo.out v)
      have hNr : Module.finrank ℂ (N v) ≤ 1 := (LinearMap.finrank_le_finrank_of_injective he).trans
        hrank
      exact hline (N v) hNr (n v) (hnN v) (hn0 v)
    rw [← sub_eq_zero]
    refine hvanish v (N v) (hN0 v) (hNst v) _ (Subalgebra.sub_mem _
      (Algebra.subset_adjoin (hTmem v x)) (Subalgebra.algebraMap_mem _ _)) fun y hy => ?_
    obtain ⟨d, rfl⟩ := hNline y hy
    obtain ⟨e, he⟩ := hNline _ (hNst v _ (hTmem v x) (n v) (hnN v))
    have hce : c v x = e := by
      have h1 := hc v x
      rw [he, map_smul, hpn v] at h1
      by_contra hne
      have h2 : (e - c v x) • n v = 0 := by rw [sub_smul, h1, sub_self]
      rcases smul_eq_zero.1 h2 with h | h
      · exact hne (sub_eq_zero.1 h).symm
      · exact hn0 v h
    rw [LinearMap.sub_apply, map_smul, he, Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply,
      Module.End.one_apply, hce, smul_comm, sub_self]

  have hpcomm : ∀ v w, v ≠ w → Commute (p v) (p w) :=
    fun v w h => commute_adjoin hcomm h (hp v) (hp w)
  have hvec : ∀ s : Finset ι, ∃ x : M, x ≠ 0 ∧ ∀ v ∈ s, p v x = x := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      obtain ⟨x, hx⟩ := exists_ne (0 : M)
      exact ⟨x, hx, fun v hv => absurd hv (Finset.notMem_empty v)⟩
    | insert a s has ih =>
      obtain ⟨x, hx0, hx⟩ := ih
      let Y : Submodule ℂ M :=
        { carrier := {y | ∀ w ∈ s, p w y = y}
          add_mem' := fun ha hb w hw => by rw [map_add, ha w hw, hb w hw]
          zero_mem' := fun w _ => map_zero _
          smul_mem' := fun c y hy w hw => by rw [map_smul, hy w hw] }
      have hxY : x ∈ Y := hx
      have hY0 : Y ≠ ⊥ := fun h => hx0 (by
        have : x ∈ (⊥ : Submodule ℂ M) := h ▸ hxY
        simpa using this)
      have hYs : IsStable (Tp a) Y := by
        intro t ht y hy w hw
        have hwa : w ≠ a := fun h => has (by rw [← h]; exact hw)
        have hct : Commute (p w) t := commute_adjoin hcomm hwa (hp w) (Algebra.subset_adjoin ht)
        rw [← Module.End.mul_apply, hct.eq, Module.End.mul_apply, hy w hw]
      obtain ⟨y, hyY, hy0⟩ : ∃ y ∈ Y, p a y ≠ 0 := by
        by_contra hcon
        push Not at hcon
        have := hvanish a Y hY0 hYs (p a) (hp a) hcon
        apply hn0 a
        rw [← hpn a, this, LinearMap.zero_apply]
      refine ⟨p a y, hy0, fun w hw => ?_⟩
      rcases Finset.mem_insert.1 hw with rfl | hw
      · rw [← Module.End.mul_apply, hpp]
      · have hwa : w ≠ a := fun h => has (by rw [← h]; exact hw)
        rw [← Module.End.mul_apply, (hpcomm w a hwa).eq, Module.End.mul_apply, hyY w hw]
  obtain ⟨xs, hxs0, hxs⟩ := hvec S
  have hform : ∀ s : Finset ι, s ⊆ S → ∃ φ : Dual ℂ M, φ xs = 1 ∧ ∀ v ∈ s, φ ∘ₗ p v = φ := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro _
      obtain ⟨f, hf⟩ : ∃ f : Dual ℂ M, f xs ≠ 0 := by
        by_contra hcon
        push Not at hcon
        exact hxs0 ((Module.forall_dual_apply_eq_zero_iff ℂ xs).1 hcon)
      exact ⟨(f xs)⁻¹ • f, by simp [hf], fun v hv => absurd hv (Finset.notMem_empty v)⟩
    | insert a s has ih =>
      intro hsub
      obtain ⟨φ, hφ1, hφ⟩ := ih ((Finset.subset_insert a s).trans hsub)
      refine ⟨φ ∘ₗ p a, ?_, fun w hw => ?_⟩
      · rw [LinearMap.comp_apply, hxs a (hsub (Finset.mem_insert_self a s)), hφ1]
      · rcases Finset.mem_insert.1 hw with rfl | hw
        · rw [LinearMap.comp_assoc]
          exact congrArg (φ ∘ₗ ·) (hpp w)
        · have hwa : w ≠ a := fun h => has (by rw [← h]; exact hw)
          rw [LinearMap.comp_assoc, show p a ∘ₗ p w = p a * p w from rfl, ← (hpcomm w a hwa).eq,
            show p w * p a = p w ∘ₗ p a from rfl, ← LinearMap.comp_assoc, hφ w hw]
  obtain ⟨φ, hφ1, hφ⟩ := hform S subset_rfl

  have hcoef : ∀ s : Finset ι, ∀ g : Πʳ v, [G v, K v], (∀ v ∉ s, g v ∈ K' v) →
      φ (heckeOp hρs hHc hHo g xs) = ∏ v ∈ s, c v (g v) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro g hg
      rw [heckeOp_of_mem hρs hHc hHo (show g ∈ H from fun v => hg v (Finset.notMem_empty v)),
        Module.End.one_apply, hφ1, Finset.prod_empty]
    | insert a s has ih =>
      intro g hg
      have herase : ∀ v ∉ s, eraseAt a g v ∈ K' v := by
        intro v hv
        by_cases hva : v = a
        · subst hva; rw [eraseAt_apply_self]; exact (K' v).one_mem
        · rw [eraseAt_apply_of_ne _ hva]
          exact hg v (by simp [hva, hv])
      have hih := ih (eraseAt a g) herase
      have hprod : ∏ v ∈ s, c v (eraseAt a g v) = ∏ v ∈ s, c v (g v) :=
        Finset.prod_congr rfl fun v hv => by
          rw [eraseAt_apply_of_ne _ (fun h => has (by rw [← h]; exact hv))]
      rw [hprod] at hih
      rw [Finset.prod_insert has, ← hih]
      conv_lhs => rw [← single_mul_eraseAt a g]
      rw [heckeOp_single_mul hρs hK'c hK'o hK'e a (g a) (eraseAt_apply_self a g),
        Module.End.mul_apply]
      set y := heckeOp hρs hHc hHo (eraseAt a g) xs
      by_cases haS : a ∈ S
      ·
        have hmem := heckeOp_mem_adjoin hρs hK'c hK'o hK'e s herase
        have hcomm' : Commute (p a) (heckeOp hρs hHc hHo (eraseAt a g)) := by
          refine commute_of_mem_adjoin (fun t ht => ?_) _ hmem
          simp only [mem_iUnion] at ht
          obtain ⟨w, hw, ht⟩ := ht
          exact commute_adjoin hcomm (fun h => has (by subst h; exact hw)) (hp a) (Algebra.subset_adjoin ht)
        have hy : p a y = y := by
          show p a (heckeOp hρs hHc hHo (eraseAt a g) xs) = _
          rw [← Module.End.mul_apply, hcomm'.eq, Module.End.mul_apply, hxs a haS]
        calc φ (heckeOp hρs hHc hHo (singleHom K a (g a)) y)
            = (φ ∘ₗ p a) (heckeOp hρs hHc hHo (singleHom K a (g a)) (p a y)) := by
              rw [hφ a haS, hy]
          _ = φ ((p a * heckeOp hρs hHc hHo (singleHom K a (g a)) * p a) y) := rfl
          _ = c a (g a) * φ y := by
              rw [hpTp, LinearMap.smul_apply, map_smul, hy, smul_eq_mul]
      · rw [hscalar a haS, Algebra.algebraMap_eq_smul_one,
          LinearMap.smul_apply, Module.End.one_apply, map_smul, smul_eq_mul]
  have hcoef' : ∀ g : Πʳ v, [G v, K v], φ (heckeOp hρs hHc hHo g xs) = ∏ᶠ v, c v (g v) := by
    intro g
    have hfin : {v | g v ∉ K' v}.Finite := Filter.eventually_cofinite.1
      ((g.2.and hK'e).mono fun v h => by rw [h.2]; exact h.1)
    rw [hcoef hfin.toFinset g (fun v hv => by simpa using hv)]
    refine (finprod_eq_prod_of_mulSupport_subset _ fun v hv => ?_).symm
    by_contra hvs
    exact hv (hc1 v _ (by simpa using hvs))

  have hχ : ∀ v, ∃ χ : Dual ℂ M, χ (n v) = 1 := by
    intro v
    obtain ⟨f, hf⟩ : ∃ f : Dual ℂ M, f (n v) ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hn0 v ((Module.forall_dual_apply_eq_zero_iff ℂ (n v)).1 hcon)
    exact ⟨(f (n v))⁻¹ • f, by simp [hf]⟩
  choose χ hχ using hχ
  set l : ∀ v, Dual ℂ (fixedVectors (ρ.comp (singleHom K v)) (K' v)) :=
    fun v => χ v ∘ₗ p v ∘ₗ fixedProj ρ hρs hHc hHo ∘ₗ Submodule.subtype _
  set lam : ∀ v, Dual ℂ _ := fun v => genQuotForm (hρv v) (hK'c v) (hK'o v) (N := NV v) (l v)
  have hlam : ∀ v (x : G v), lam v (π v x (ξ v)) = c v x := by
    intro v x
    show genQuotForm (hρv v) (hK'c v) (hK'o v) (l v) (genQuotRep (hρv v) (hK'c v) (hK'o v) (NV v) x
      (genQuotMk (hρv v) (hK'c v) (hK'o v) (NV v) _)) = _
    rw [genQuotForm_apply _ _ _ _ (hNK v)]
    simp only [l, LinearMap.comp_apply, Submodule.subtype_apply]
    have h1 : (fixedProj (ρ.comp (singleHom K v)) (hρv v) (hK'c v) (hK'o v)
        ((ρ.comp (singleHom K v)) x (n v : V)) : V) =
        (heckeOp hρs hHc hHo (singleHom K v x) (n v) : V) := hproj v x (n v)
    rw [h1]
    have h2 : fixedProj ρ hρs hHc hHo (heckeOp hρs hHc hHo (singleHom K v x) (n v) : V) =
        heckeOp hρs hHc hHo (singleHom K v x) (n v) :=
      Subtype.ext (fixedProj_apply_of_mem hρs hHc hHo (Subtype.prop _))
    rw [h2, hc v x, map_smul, hχ v, smul_eq_mul, mul_one]
  have hlam1 : ∀ v, lam v (ξ v) = 1 := fun v => by
    have := hlam v 1
    rwa [map_one, Module.End.one_apply, hc1 v 1 (K' v).one_mem] at this
  have hlamξ : ∀ᶠ v in cofinite, lam v (ξ v) = 1 := Eventually.of_forall hlam1

  set Λ : Dual ℂ V := φ ∘ₗ fixedProj ρ hρs hHc hHo
  have hV : ∀ g, Λ (ρ g xs) = ∏ᶠ v, lam v (π v (g v) (ξ v)) :=
    fun g => (hcoef' g).trans (finprod_congr fun v => (hlam v (g v)).symm)
  have hne : Λ (xs : V) ≠ 0 := by
    have := hV 1
    simp only [map_one, Module.End.one_apply, RestrictedProduct.one_apply] at this
    rw [this, finprod_eq_one_of_forall_eq_one fun v => hlam1 v]
    exact one_ne_zero
  exact ⟨_, fun v => inferInstance, fun v => inferInstance, π, ξ, hξ, hπadm, hπirr,
    Eventually.of_forall hξ0, nonempty_equiv_of_coeff hirr hπadm hπirr hξ (Eventually.of_forall hξ0)
      hgelξ (xs : V) Λ lam hlamξ hV hne⟩

end Main

end RestrictedTensor

end GroundTheory.Automorphic
