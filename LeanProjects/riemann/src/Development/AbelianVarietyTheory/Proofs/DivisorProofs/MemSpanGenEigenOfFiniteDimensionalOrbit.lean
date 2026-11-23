import Mathlib

open Module

namespace GlobalTheory.GenEigenFinOrbit

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem foldr_eq_prod (χ : End ℂ V → ℂ) (zs : List (End ℂ V)) (v : V) :
    zs.foldr (fun z f => z f - χ z • f) v =
      (zs.map (fun z => z - algebraMap ℂ (End ℂ V) (χ z))).prod v := by
  induction zs with
  | nil => simp
  | cons z zs ih => simp [ih, Module.End.mul_apply]

theorem map_lt_of_pow_eq_zero {N : Submodule ℂ V} (g : End ℂ V) (K : ℕ)
    (hg : N.map g ≤ N) (hK : ∀ n ∈ N, (g ^ K) n = 0) (hN : N ≠ ⊥) : N.map g < N := by
  refine lt_of_le_of_ne hg fun h => hN ?_
  have hk : ∀ k : ℕ, N.map (g ^ k) = N := by
    intro k
    induction k with
    | zero => simp [Module.End.one_eq_id]
    | succ k ih => rw [pow_succ, Module.End.mul_eq_comp, Submodule.map_comp, h, ih]
  rw [← hk K, eq_bot_iff]
  rintro _ ⟨n, hn, rfl⟩
  simp [hK n hn]

section Family
variable (G : Set (End ℂ V)) (N : Submodule ℂ V) (K : ℕ)
  (hcomm : ∀ a ∈ G, ∀ b ∈ G, a * b = b * a)
  (hst : ∀ g ∈ G, N.map g ≤ N) (hnil : ∀ g ∈ G, ∀ n ∈ N, (g ^ K) n = 0)

include hst in
theorem map_prod_le (gs : List (End ℂ V)) (hgs : ∀ g ∈ gs, g ∈ G) : N.map gs.prod ≤ N := by
  induction gs with
  | nil => simp [Module.End.one_eq_id]
  | cons g gs ih =>
    rw [List.prod_cons, Module.End.mul_eq_comp, Submodule.map_comp]
    exact (Submodule.map_mono (ih fun x hx => hgs x (by simp [hx]))).trans
      (hst g (hgs g (by simp)))

include hcomm hst hnil in
theorem finrank_map_prod_le [FiniteDimensional ℂ N] (gs : List (End ℂ V))
    (hgs : ∀ g ∈ gs, g ∈ G) :
    finrank ℂ (N.map gs.prod) ≤ finrank ℂ N - gs.length := by
  induction gs with
  | nil => rw [List.prod_nil, Module.End.one_eq_id, Submodule.map_id]; simp
  | cons g gs ih =>
    have hgs' : ∀ x ∈ gs, x ∈ G := fun x hx => hgs x (by simp [hx])
    have hg : g ∈ G := hgs g (by simp)
    specialize ih hgs'
    set M := N.map gs.prod with hM
    have hMN : M ≤ N := map_prod_le G N hst gs hgs'
    haveI : FiniteDimensional ℂ M := Submodule.finiteDimensional_of_le hMN
    have hc : Commute g gs.prod :=
      Commute.list_prod_right _ _ fun x hx => hcomm g hg x (hgs' x hx)
    have hMst : M.map g ≤ M := by
      rw [hM, ← Submodule.map_comp, ← Module.End.mul_eq_comp, hc.eq, Module.End.mul_eq_comp,
        Submodule.map_comp]
      exact Submodule.map_mono (hst g hg)
    rw [List.prod_cons, Module.End.mul_eq_comp, Submodule.map_comp, ← hM, List.length_cons]
    by_cases h0 : M = ⊥
    · rw [h0, Submodule.map_bot]; simp
    · have hlt := Submodule.finrank_lt_finrank_of_lt
        (map_lt_of_pow_eq_zero g K hMst (fun n hn => hnil g hg n (hMN hn)) h0)
      omega

include hcomm hst hnil in
theorem map_prod_eq_bot [FiniteDimensional ℂ N] (gs : List (End ℂ V))
    (hgs : ∀ g ∈ gs, g ∈ G) (hlen : finrank ℂ N ≤ gs.length) : N.map gs.prod = ⊥ := by
  haveI : FiniteDimensional ℂ (N.map gs.prod) :=
    Submodule.finiteDimensional_of_le (map_prod_le G N hst gs hgs)
  rw [← Submodule.finrank_eq_zero]
  have := finrank_map_prod_le G N K hcomm hst hnil gs hgs
  omega

include hcomm hst hnil in
theorem exists_common_kernel [FiniteDimensional ℂ N] (hN : N ≠ ⊥) :
    ∃ n ∈ N, n ≠ 0 ∧ ∀ g ∈ G, g n = 0 := by
  classical
  let Pr : ℕ → Prop := fun l => ∃ gs : List (End ℂ V), (∀ g ∈ gs, g ∈ G) ∧ gs.length = l ∧
    N.map gs.prod ≠ ⊥
  have hex : ∃ l, ¬ Pr l := ⟨finrank ℂ N, fun ⟨gs, hgs, hl, hne⟩ =>
    hne (map_prod_eq_bot G N K hcomm hst hnil gs hgs hl.ge)⟩
  have h0 : Pr 0 := ⟨[], by simp, rfl, by simpa [Module.End.one_eq_id] using hN⟩
  have hpos : 0 < Nat.find hex := by
    rcases Nat.eq_zero_or_pos (Nat.find hex) with h | h
    · exact absurd (h ▸ Nat.find_spec hex) (not_not.2 h0)
    · exact h
  obtain ⟨gs, hgs, hl, hne⟩ : Pr (Nat.find hex - 1) :=
    not_not.1 (Nat.find_min hex (by omega))
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨n, hn, rfl⟩ := hx
  refine ⟨gs.prod n, map_prod_le G N hst gs hgs ⟨n, hn, rfl⟩, hx0, fun g hg => ?_⟩
  by_contra hne'
  apply Nat.find_spec hex
  refine ⟨g :: gs, ?_, by simp [hl]; omega, ?_⟩
  · intro x hx; simp at hx; rcases hx with rfl | hx; exacts [hg, hgs x hx]
  · intro hbot
    apply hne'
    have : (g :: gs).prod n ∈ N.map (g :: gs).prod := ⟨n, hn, rfl⟩
    rw [hbot] at this
    simpa [Module.End.mul_apply] using this

end Family

theorem sub_pow_coe {U : Submodule ℂ V} (z : End ℂ V) (F : End ℂ U)
    (hF : ∀ u : U, (F u : V) = z u) (c : ℂ) (k : ℕ) (u : U) :
    (((F - c • 1) ^ k) u : V) = ((z - algebraMap ℂ (End ℂ V) c) ^ k) (u : V) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, ← ih]
    simp [hF]

end GlobalTheory.GenEigenFinOrbit

namespace GlobalTheory

open GenEigenFinOrbit in

theorem mem_span_genEigen_of_finiteDimensional_orbit :
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (A : Subalgebra ℂ (Module.End ℂ V)),
    (∀ x ∈ A, ∀ y ∈ A, x * y = y * x) → ∀ (X' : Set (Module.End ℂ V → ℂ)) (D : ℕ) (ψ : V),
    FiniteDimensional ℂ (Submodule.span ℂ ((fun z : Module.End ℂ V => z ψ) '' A)) →
    Module.finrank ℂ (Submodule.span ℂ ((fun z : Module.End ℂ V => z ψ) '' A)) ≤ D →
    (∀ (χ' : Module.End ℂ V → ℂ) (u : V),
      u ∈ Submodule.span ℂ ((fun z : Module.End ℂ V => z ψ) '' A) → u ≠ 0 →
      (∀ z ∈ A, z u = χ' z • u) → ∃ χ ∈ X', ∀ z ∈ A, χ' z = χ z) →
    ψ ∈ Submodule.span ℂ {ψ' | ψ' ∈ Submodule.span ℂ ((fun z : Module.End ℂ V => z ψ) '' A) ∧
      ∃ χ ∈ X', ∀ zs : List (Module.End ℂ V), zs.length = D → (∀ z ∈ zs, z ∈ A) →
        zs.foldr (fun z f => z f - χ z • f) ψ' = 0} := by
  intro V _ _ A hA X' D ψ hfin hD hX
  set U := Submodule.span ℂ ((fun z : Module.End ℂ V => z ψ) '' A) with hU
  have hUst : ∀ z ∈ A, Set.MapsTo z U U := by
    intro z hz
    have : U.map z ≤ U := by
      rw [hU, Submodule.map_span, Submodule.span_le]
      rintro _ ⟨_, ⟨w, hw, rfl⟩, rfl⟩
      exact Submodule.subset_span ⟨z * w, A.mul_mem hz hw, rfl⟩
    exact fun u hu => this ⟨u, hu, rfl⟩
  have hψU : ψ ∈ U := Submodule.subset_span ⟨1, A.one_mem, rfl⟩
  obtain ⟨f, hf⟩ : ∃ f : A → End ℂ U, ∀ (i : A) (u : U), (f i u : V) = (i : End ℂ V) u :=
    ⟨fun i => (i : End ℂ V).restrict (hUst i i.2), fun _ _ => rfl⟩
  have hcommAll : ∀ i j, Commute (f i) (f j) := by
    intro i j
    show f i * f j = f j * f i
    ext u
    have := congrArg (fun T : End ℂ V => T (u : V)) (hA i i.2 j j.2)
    simpa [Module.End.mul_apply, hf] using this
  have htop := Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute
    f (fun i j _ => hcommAll i j) (fun i => Module.End.iSup_maxGenEigenspace_eq_top _)
  set T := {ψ' | ψ' ∈ U ∧ ∃ χ ∈ X', ∀ zs : List (Module.End ℂ V), zs.length = D →
        (∀ z ∈ zs, z ∈ A) → zs.foldr (fun z f => z f - χ z • f) ψ' = 0} with hT
  have key : ∀ χ : A → ℂ, ∀ x ∈ ⨅ i, (f i).maxGenEigenspace (χ i),
      (x : V) ∈ Submodule.span ℂ T := by
    classical
    intro χ x hx
    set N := (⨅ i, (f i).maxGenEigenspace (χ i)).map U.subtype with hNdef
    have hxN : (x : V) ∈ N := ⟨x, hx, rfl⟩
    have hNU : N ≤ U := by
      rintro _ ⟨y, _, rfl⟩
      exact y.2
    haveI : FiniteDimensional ℂ N := Submodule.finiteDimensional_of_le hNU
    obtain ⟨χ', hχ'⟩ : ∃ χ' : End ℂ V → ℂ, ∀ z (hz : z ∈ A), χ' z = χ ⟨z, hz⟩ :=
      ⟨fun y => if h : y ∈ A then χ ⟨y, h⟩ else 0, fun z hz => dif_pos hz⟩
    set G : Set (End ℂ V) := {g | ∃ z ∈ A, g = z - algebraMap ℂ _ (χ' z)} with hG
    have hGA : ∀ g ∈ G, g ∈ A := by
      rintro _ ⟨z, hz, rfl⟩
      exact A.sub_mem hz (A.algebraMap_mem _)
    have hcommG : ∀ a ∈ G, ∀ b ∈ G, a * b = b * a :=
      fun a ha b hb => hA a (hGA a ha) b (hGA b hb)
    have hNst : ∀ z ∈ A, N.map z ≤ N := by
      rintro z hz _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      refine ⟨f ⟨z, hz⟩ y, ?_, hf ⟨z, hz⟩ y⟩
      simp only [SetLike.mem_coe, Submodule.mem_iInf] at hy ⊢
      intro i
      exact Module.End.mapsTo_maxGenEigenspace_of_comm (hcommAll i ⟨z, hz⟩) (χ i) (hy i)
    have hstG : ∀ g ∈ G, N.map g ≤ N := by
      rintro _ ⟨z, hz, rfl⟩ _ ⟨v, hv, rfl⟩
      simp only [LinearMap.sub_apply, Module.algebraMap_end_apply]
      exact N.sub_mem (hNst z hz ⟨v, hv, rfl⟩) (N.smul_mem _ hv)
    have hnil : ∀ g ∈ G, ∀ n ∈ N, (g ^ finrank ℂ U) n = 0 := by
      rintro _ ⟨z, hz, rfl⟩ _ ⟨y, hy, rfl⟩
      have hy' := (Submodule.mem_iInf _).1 (SetLike.mem_coe.1 hy) ⟨z, hz⟩
      rw [Module.End.maxGenEigenspace_eq_genEigenspace_finrank, Module.End.mem_genEigenspace_nat,
        LinearMap.mem_ker] at hy'
      rw [hχ' z hz, Submodule.subtype_apply, ← sub_pow_coe z (f ⟨z, hz⟩) (hf ⟨z, hz⟩), hy']
      rfl
    by_cases hN : N = ⊥
    · rw [hN, Submodule.mem_bot] at hxN
      rw [hxN]
      exact zero_mem _
    obtain ⟨n, hnN, hn0, hnker⟩ := exists_common_kernel G N (finrank ℂ U) hcommG hstG hnil hN
    have heig : ∀ z ∈ A, z n = χ' z • n := by
      intro z hz
      have := hnker _ ⟨z, hz, rfl⟩
      simpa [sub_eq_zero] using this
    obtain ⟨χ0, hχ0X, hχ0⟩ := hX χ' n (hNU hnN) hn0 heig
    apply Submodule.subset_span
    refine ⟨hNU hxN, χ0, hχ0X, fun zs hlen hzs => ?_⟩
    rw [foldr_eq_prod]
    have hmap : zs.map (fun z => z - algebraMap ℂ (End ℂ V) (χ0 z)) =
        zs.map (fun z => z - algebraMap ℂ (End ℂ V) (χ' z)) :=
      List.map_congr_left fun z hz => by rw [hχ0 z (hzs z hz)]
    rw [hmap]
    have hbot := map_prod_eq_bot G N (finrank ℂ U) hcommG hstG hnil
      (zs.map fun z => z - algebraMap ℂ (End ℂ V) (χ' z))
      (by
        intro g hg
        obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hg
        exact ⟨z, hzs z hz, rfl⟩)
      (by rw [List.length_map, hlen]; exact (Submodule.finrank_mono hNU).trans hD)
    have hmem : (zs.map fun z => z - algebraMap ℂ (End ℂ V) (χ' z)).prod (x : V) ∈
        N.map (zs.map fun z => z - algebraMap ℂ (End ℂ V) (χ' z)).prod := ⟨_, hxN, rfl⟩
    rw [hbot, Submodule.mem_bot] at hmem
    exact hmem
  have hmem : (⟨ψ, hψU⟩ : U) ∈ ⨆ χ : A → ℂ, ⨅ i, (f i).maxGenEigenspace (χ i) := by
    rw [htop]; exact Submodule.mem_top
  exact Submodule.iSup_induction _ (motive := fun x : U => (x : V) ∈ Submodule.span ℂ T) hmem key
    (by simp) (fun x y hx hy => by simpa using add_mem hx hy)

end GlobalTheory
