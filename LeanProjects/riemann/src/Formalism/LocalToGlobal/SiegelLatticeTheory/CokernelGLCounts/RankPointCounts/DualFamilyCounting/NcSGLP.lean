import Mathlib

noncomputable section

namespace Formalism.L2.SG.Pf.NcS.LT.GLP

variable {K : Type*} [Field K]

theorem surj_equiv {C W : Type*} [AddCommGroup C] [Module K C] [FiniteDimensional K C]
    [AddCommGroup W] [Module K W] (L1 L2 : C →ₗ[K] W) (h1 : Function.Surjective L1)
    (h2 : Function.Surjective L2) : ∃ δ : C ≃ₗ[K] C, ∀ c, L1 (δ c) = L2 c := by
  obtain ⟨s, hs⟩ := LinearMap.exists_rightInverse_of_surjective L1 (LinearMap.range_eq_top.mpr h1)
  obtain ⟨p, hp⟩ := LinearMap.exists_leftInverse_of_injective (LinearMap.ker L2).subtype
    (LinearMap.ker L2).ker_subtype
  have hdim : Module.finrank K (LinearMap.ker L2) = Module.finrank K (LinearMap.ker L1) := by
    have e1 := LinearMap.finrank_range_add_finrank_ker L1
    have e2 := LinearMap.finrank_range_add_finrank_ker L2
    rw [LinearMap.range_eq_top.mpr h1, finrank_top] at e1
    rw [LinearMap.range_eq_top.mpr h2, finrank_top] at e2
    omega
  let e : LinearMap.ker L2 ≃ₗ[K] LinearMap.ker L1 := by
    first
    | exact LinearEquiv.ofFinrankEq _ _ hdim
    | exact LinearEquiv.ofFinrankEq hdim
  let δ : C →ₗ[K] C := s ∘ₗ L2 + (LinearMap.ker L1).subtype ∘ₗ (e.toLinearMap ∘ₗ p)
  have hδ : ∀ c, δ c = s (L2 c) + ((e (p c) : LinearMap.ker L1) : C) := by
    intro c
    first
    | rfl
    | simp [δ]
  have hL1 : ∀ c, L1 (δ c) = L2 c := by
    intro c
    have h1' : L1 (s (L2 c)) = L2 c := by simpa using LinearMap.congr_fun hs (L2 c)
    have h2' : L1 ((e (p c) : LinearMap.ker L1) : C) = 0 := LinearMap.mem_ker.mp (e (p c)).2
    rw [hδ, map_add, h1', h2', add_zero]
  have hinj : Function.Injective δ := by
    refine (injective_iff_map_eq_zero δ).mpr fun c hc => ?_
    have hc2 : L2 c = 0 := by rw [← hL1 c, hc, map_zero]
    have hpc : p c = ⟨c, hc2⟩ := by simpa using LinearMap.congr_fun hp ⟨c, hc2⟩
    rw [hδ, hc2, map_zero, zero_add, hpc] at hc
    have hk : (⟨c, hc2⟩ : LinearMap.ker L2) = 0 := by simpa using hc
    first
    | exact congrArg Subtype.val hk
    | simpa using congrArg Subtype.val hk
  refine ⟨LinearEquiv.ofInjectiveEndo δ hinj, fun c => ?_⟩
  first
  | exact hL1 c
  | simpa using hL1 c

private theorem dual_apply_eq_sum_mul_single {a : ℕ} (μ : Module.Dual K (Fin a → K)) (t : Fin a → K) :
    μ t = ∑ i, t i * μ (Pi.single i 1) := by
  have ht : t = ∑ i, t i • (Pi.single i 1 : Fin a → K) := by
    ext j
    first
    | simp [Finset.sum_apply, Pi.single_apply]
    | simp [Finset.sum_apply, Pi.single_apply, eq_comm]
  calc μ t = μ (∑ i, t i • (Pi.single i 1 : Fin a → K)) := congrArg μ ht
    _ = ∑ i, t i * μ (Pi.single i 1) := by simp [map_sum, map_smul]

theorem pi_surj {V : Type*} [AddCommGroup V] [Module K V] {a : ℕ} (ψ : Fin a → Module.Dual K V)
    (hψ : LinearIndependent K ψ) : Function.Surjective (LinearMap.pi ψ) := by
  rw [← LinearMap.range_eq_top]
  by_contra hne
  obtain ⟨μ, hμ0, hμ⟩ : ∃ μ : Module.Dual K (Fin a → K), μ ≠ 0 ∧ ∀ v, μ (LinearMap.pi ψ v) = 0 := by
    first
    | (obtain ⟨μ, hμ0, hμ⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hne)
       exact ⟨μ, hμ0, fun v => LinearMap.mem_ker.mp (hμ (LinearMap.mem_range_self _ v))⟩)
    | (obtain ⟨μ, hμ0, hμ⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top (lt_top_iff_ne_top.mpr hne)
       refine ⟨μ, hμ0, fun v => ?_⟩
       have hm : μ (LinearMap.pi ψ v) ∈ (LinearMap.range (LinearMap.pi ψ)).map μ :=
         Submodule.mem_map_of_mem (LinearMap.mem_range_self _ v)
       rw [hμ] at hm
       simpa using hm)
  have hsum : ∑ i, μ (Pi.single i 1) • ψ i = 0 := by
    refine LinearMap.ext fun v => ?_
    have hv := hμ v
    rw [dual_apply_eq_sum_mul_single] at hv
    simpa [LinearMap.sum_apply, mul_comm] using hv
  have hzero := Fintype.linearIndependent_iff.mp hψ _ hsum
  exact hμ0 (LinearMap.ext fun t => by rw [dual_apply_eq_sum_mul_single μ t]; simp [hzero])

theorem trans_tuple {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V] {a : ℕ}
    (x y : Fin a → V) (hx : LinearIndependent K x) (hy : LinearIndependent K y) :
    ∃ A : V ≃ₗ[K] V, ∀ j, A (x j) = y j := by
  obtain ⟨CX, hX⟩ := Submodule.exists_isCompl (Submodule.span K (Set.range x))
  obtain ⟨CY, hY⟩ := Submodule.exists_isCompl (Submodule.span K (Set.range y))
  have hdim : Module.finrank K CX = Module.finrank K CY := by
    have h1 := Submodule.finrank_add_eq_of_isCompl hX
    have h2 := Submodule.finrank_add_eq_of_isCompl hY
    rw [finrank_span_eq_card hx] at h1
    rw [finrank_span_eq_card hy] at h2
    omega
  let bx := Module.Basis.span hx
  let bY := Module.Basis.span hy
  let e1 := bx.equiv bY (Equiv.refl (Fin a))
  let e2 : CX ≃ₗ[K] CY := by
    first
    | exact LinearEquiv.ofFinrankEq _ _ hdim
    | exact LinearEquiv.ofFinrankEq hdim
  let P : (Submodule.span K (Set.range x) × CX) ≃ₗ[K] (Submodule.span K (Set.range y) × CY) := by
    first
    | exact LinearEquiv.prodCongr e1 e2
    | exact LinearEquiv.prod e1 e2
  have hsymm : ∀ j, (Submodule.prodEquivOfIsCompl _ _ hX).symm (x j) = (bx j, 0) := by
    intro j
    rw [LinearEquiv.symm_apply_eq]
    first
    | (rw [Submodule.coe_prodEquivOfIsCompl']; simp [bx, Module.Basis.span_apply])
    | simp [bx, Module.Basis.span_apply]
    | simp [bx]
  refine ⟨(Submodule.prodEquivOfIsCompl _ _ hX).symm.trans (P.trans (Submodule.prodEquivOfIsCompl _ _ hY)),
    fun j => ?_⟩
  rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, hsymm j]
  have hP : P (bx j, 0) = (bY j, 0) := by
    first
    | (show (e1 (bx j), e2 0) = (bY j, 0)
       rw [map_zero]
       simp [e1, Module.Basis.equiv_apply])
    | simp [P, e1, Module.Basis.equiv_apply]
    | simp [P, e1]
  rw [hP]
  first
  | (rw [Submodule.coe_prodEquivOfIsCompl']; simp [bY, Module.Basis.span_apply])
  | simp [bY, Module.Basis.span_apply]
  | simp [bY]

private theorem eq_zero_of_mem_of_disjoint {V : Type*} [AddCommGroup V] [Module K V] {S T : Submodule K V}
    (h : Disjoint S T) {v : V} (hS : v ∈ S) (hT : v ∈ T) : v = 0 :=
  (Submodule.mem_bot K).mp (h.le_bot (Submodule.mem_inf.mpr ⟨hS, hT⟩))

private theorem exists_not_mem_of_ne_top_of_ne_top {V : Type*} [AddCommGroup V] [Module K V]
    (U W : Submodule K V) (hU : U ≠ ⊤) (hW : W ≠ ⊤) : ∃ v, v ∉ U ∧ v ∉ W := by
  obtain ⟨u, hu⟩ : ∃ u, u ∉ U := by
    by_contra hcon
    push_neg at hcon
    exact hU (Submodule.eq_top_iff'.mpr hcon)
  obtain ⟨w, hw⟩ : ∃ w, w ∉ W := by
    by_contra hcon
    push_neg at hcon
    exact hW (Submodule.eq_top_iff'.mpr hcon)
  by_cases huW : u ∈ W
  · by_cases hwU : w ∈ U
    · refine ⟨u + w, fun h => hu ?_, fun h => hw ?_⟩
      · simpa using U.sub_mem h hwU
      · simpa using W.sub_mem h huW
    · exact ⟨w, hwU, hw⟩
  · exact ⟨u, hu, huW⟩

private theorem exists_common_complement_of_finrank_eq {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (n : ℕ) : ∀ U W : Submodule K V, Module.finrank K U = Module.finrank K W →
      Module.finrank K V = Module.finrank K U + n →
      ∃ T : Submodule K V, Disjoint T U ∧ Disjoint T W ∧
        Module.finrank K V = Module.finrank K U + Module.finrank K T := by
  induction n with
  | zero =>
    intro U W _ hn
    refine ⟨⊥, disjoint_bot_left, disjoint_bot_left, ?_⟩
    rw [finrank_bot]
    omega
  | succ n ih =>
    intro U W hUW hn
    have hU : U ≠ ⊤ := by
      rintro rfl
      rw [finrank_top] at hn
      omega
    have hW : W ≠ ⊤ := by
      rintro rfl
      rw [finrank_top] at hUW
      omega
    obtain ⟨v, hvU, hvW⟩ := exists_not_mem_of_ne_top_of_ne_top U W hU hW
    have hv0 : v ≠ 0 := fun h => hvU (by rw [h]; exact U.zero_mem)
    have hback : ∀ S : Submodule K V, ∀ c : K, c ≠ 0 → c • v ∈ S → v ∈ S := by
      intro S c hc hcv
      have hm := S.smul_mem c⁻¹ hcv
      first
      | (rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at hm)
      | simpa [hc] using hm
    have hinf : ∀ S : Submodule K V, v ∉ S → S ⊓ Submodule.span K {v} = ⊥ := by
      intro S hvS
      rw [eq_bot_iff]
      intro z hz
      rw [Submodule.mem_bot]
      obtain ⟨hzS, hzv⟩ := Submodule.mem_inf.mp hz
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hzv
      by_cases hc : c = 0
      · simp [hc]
      · exact (hvS (hback S c hc hzS)).elim
    have key : ∀ S : Submodule K V, v ∉ S →
        Module.finrank K ↥(S ⊔ Submodule.span K {v}) = Module.finrank K S + 1 := by
      intro S hvS
      have h := Submodule.finrank_sup_add_finrank_inf_eq S (Submodule.span K {v})
      rw [hinf S hvS, finrank_bot, finrank_span_singleton hv0] at h
      omega
    obtain ⟨T, hTU, hTW, hT⟩ := ih (U ⊔ Submodule.span K {v}) (W ⊔ Submodule.span K {v})
      (by rw [key U hvU, key W hvW, hUW]) (by rw [key U hvU]; omega)
    have hvT : v ∉ T := fun h => hv0 (eq_zero_of_mem_of_disjoint hTU h
      (Submodule.mem_sup_right (Submodule.mem_span_singleton_self v)))
    have disj : ∀ S : Submodule K V, v ∉ S → Disjoint T (S ⊔ Submodule.span K {v}) →
        Disjoint (T ⊔ Submodule.span K {v}) S := by
      intro S hvS hTS
      rw [disjoint_iff, eq_bot_iff]
      intro z hz
      rw [Submodule.mem_bot]
      obtain ⟨hz1, hzS⟩ := Submodule.mem_inf.mp hz
      obtain ⟨t, ht, w', hw', rfl⟩ := Submodule.mem_sup.mp hz1
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw'
      have ht0 : t = 0 := by
        refine eq_zero_of_mem_of_disjoint hTS ht ?_
        have htt : t = (t + c • v) - c • v := by abel
        rw [htt]
        exact Submodule.sub_mem _ (Submodule.mem_sup_left hzS)
          (Submodule.mem_sup_right (Submodule.smul_mem _ c (Submodule.mem_span_singleton_self v)))
      subst ht0
      by_cases hc : c = 0
      · simp [hc]
      · exact (hvS (hback S c hc (by simpa using hzS))).elim
    refine ⟨T ⊔ Submodule.span K {v}, disj U hvU hTU, disj W hvW hTW, ?_⟩
    rw [key T hvT]
    rw [key U hvU] at hT
    omega

theorem fix_tuple {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V] {a : ℕ}
    (x : Fin a → V) (hx : LinearIndependent K x) (φ ψ : Fin a → Module.Dual K V)
    (hφ : LinearIndependent K φ) (hψ : LinearIndependent K ψ) (h : ∀ i j, φ i (x j) = ψ i (x j)) :
    ∃ B : V ≃ₗ[K] V, (∀ j, B (x j) = x j) ∧ ∀ i v, ψ i (B v) = φ i v := by
  let Φ : V →ₗ[K] (Fin a → K) := LinearMap.pi φ
  let Ψ : V →ₗ[K] (Fin a → K) := LinearMap.pi ψ
  have hΦ : Function.Surjective Φ := pi_surj φ hφ
  have hΨ : Function.Surjective Ψ := pi_surj ψ hψ
  have eΦ := LinearMap.finrank_range_add_finrank_ker Φ
  have eΨ := LinearMap.finrank_range_add_finrank_ker Ψ
  rw [LinearMap.range_eq_top.mpr hΦ, finrank_top] at eΦ
  rw [LinearMap.range_eq_top.mpr hΨ, finrank_top] at eΨ
  obtain ⟨T, hTΦ, hTΨ, hT⟩ := exists_common_complement_of_finrank_eq
    (Module.finrank K V - Module.finrank K (LinearMap.ker Φ)) (LinearMap.ker Φ) (LinearMap.ker Ψ)
    (by omega) (by omega)
  have hTdim : Module.finrank K T = Module.finrank K (Fin a → K) := by omega
  let f : T →ₗ[K] (Fin a → K) := Ψ.domRestrict T
  have hfinj : Function.Injective f := by
    refine (injective_iff_map_eq_zero f).mpr fun t ht => ?_
    have h0 : (t : V) = 0 := eq_zero_of_mem_of_disjoint hTΨ t.2 (LinearMap.mem_ker.mpr ht)
    first
    | exact Subtype.ext h0
    | simpa using h0
  have hfsurj : Function.Surjective f := by
    first
    | exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hTdim).mp hfinj
    | exact LinearMap.range_eq_top.mp
        ((LinearMap.ker_eq_bot_iff_range_eq_top_of_finrank_eq_finrank hTdim).mp
          (LinearMap.ker_eq_bot.mpr hfinj))
  let eT : T ≃ₗ[K] (Fin a → K) := LinearEquiv.ofBijective f ⟨hfinj, hfsurj⟩
  let s : (Fin a → K) →ₗ[K] V := T.subtype ∘ₗ eT.symm.toLinearMap
  have hs : ∀ t, Ψ (s t) = t := by
    intro t
    have h1 : Ψ (s t) = eT (eT.symm t) := by
      first
      | rfl
      | exact (LinearEquiv.ofBijective_apply f _ (eT.symm t)).symm
    rw [h1, LinearEquiv.apply_symm_apply]
  have hsT : ∀ t, s t ∈ T := fun t => (eT.symm t).2
  let B : V →ₗ[K] V := LinearMap.id + s ∘ₗ (Φ - Ψ)
  have hBv : ∀ v, B v = v + s (Φ v - Ψ v) := by
    intro v
    first
    | rfl
    | simp [B]
  have hΨB : ∀ v, Ψ (B v) = Φ v := by
    intro v
    rw [hBv, map_add, hs]
    abel
  have hBx : ∀ j, B (x j) = x j := by
    intro j
    have hM : Φ (x j) = Ψ (x j) := funext fun i => h i j
    rw [hBv, hM, sub_self, map_zero, add_zero]
  have hinj : Function.Injective B := by
    refine (injective_iff_map_eq_zero B).mpr fun v hv => ?_
    have hΦv : Φ v = 0 := by rw [← hΨB v, hv, map_zero]
    have hvT : v ∈ T := by
      rw [hBv] at hv
      rw [eq_neg_of_add_eq_zero_left hv]
      exact T.neg_mem (hsT _)
    exact eq_zero_of_mem_of_disjoint hTΦ hvT (LinearMap.mem_ker.mpr hΦv)
  refine ⟨LinearEquiv.ofInjectiveEndo B hinj, fun j => ?_, fun i v => ?_⟩
  · first
    | exact hBx j
    | simpa using hBx j
  · first
    | exact congrFun (hΨB v) i
    | simpa using congrFun (hΨB v) i

theorem glPair {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V] {a : ℕ}
    (x y : Fin a → V) (ξ η : Fin a → Module.Dual K V) (hx : LinearIndependent K x)
    (hy : LinearIndependent K y) (hξ : LinearIndependent K ξ) (hη : LinearIndependent K η)
    (h : ∀ i j, ξ i (x j) = η i (y j)) :
    ∃ A : V ≃ₗ[K] V, (∀ j, A (x j) = y j) ∧ ∀ i v, η i (A v) = ξ i v := by
  obtain ⟨A0, hA0⟩ := trans_tuple x y hx hy
  have hψ' : LinearIndependent K (fun i => (η i).comp A0.toLinearMap) := by
    rw [Fintype.linearIndependent_iff] at hη ⊢
    intro g hg
    apply hη g
    refine LinearMap.ext fun v => ?_
    have hgv := LinearMap.congr_fun hg (A0.symm v)
    first
    | simpa using hgv
    | simpa [LinearMap.sum_apply] using hgv
  obtain ⟨B, hB1, hB2⟩ := fix_tuple x hx ξ
    (fun i => (η i).comp A0.toLinearMap) hξ hψ' (fun i j => by
      show ξ i (x j) = η i (A0 (x j))
      rw [hA0 j, h i j])
  refine ⟨B.trans A0, fun j => ?_, fun i v => ?_⟩
  · rw [LinearEquiv.trans_apply, hB1 j, hA0 j]
  · rw [LinearEquiv.trans_apply]
    exact hB2 i v

end Formalism.L2.SG.Pf.NcS.LT.GLP
