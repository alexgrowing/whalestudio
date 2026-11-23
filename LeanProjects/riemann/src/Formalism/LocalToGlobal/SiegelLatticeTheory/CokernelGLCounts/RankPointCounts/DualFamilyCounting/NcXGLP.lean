import Mathlib

noncomputable section

namespace Formalism.L2.SG.Pf.NcX.LT.GLP

variable {K : Type*} [Field K]

theorem surj_equiv {C W : Type*} [AddCommGroup C] [Module K C] [FiniteDimensional K C]
    [AddCommGroup W] [Module K W] (L1 L2 : C →ₗ[K] W) (h1 : Function.Surjective L1)
    (h2 : Function.Surjective L2) : ∃ δ : C ≃ₗ[K] C, ∀ c, L1 (δ c) = L2 c := by
  obtain ⟨D1, hD1⟩ := Submodule.exists_isCompl (LinearMap.ker L1)
  obtain ⟨D2, hD2⟩ := Submodule.exists_isCompl (LinearMap.ker L2)
  let e1 : D1 ≃ₗ[K] W := (Submodule.quotientEquivOfIsCompl _ _ hD1).symm.trans (L1.quotKerEquivOfSurjective h1)
  let e2 : D2 ≃ₗ[K] W := (Submodule.quotientEquivOfIsCompl _ _ hD2).symm.trans (L2.quotKerEquivOfSurjective h2)
  have he1 : ∀ d : D1, e1 d = L1 d := fun d => by
    simp [e1, Submodule.quotientEquivOfIsCompl_symm_apply]
  have he2 : ∀ d : D2, e2 d = L2 d := fun d => by
    simp [e2, Submodule.quotientEquivOfIsCompl_symm_apply]
  have : FiniteDimensional K W := Module.Finite.of_surjective L1 h1
  have hk : Module.finrank K (LinearMap.ker L2) = Module.finrank K (LinearMap.ker L1) := by
    have a1 := LinearMap.finrank_range_add_finrank_ker L1
    have a2 := LinearMap.finrank_range_add_finrank_ker L2
    rw [LinearMap.range_eq_top.2 h1, finrank_top] at a1
    rw [LinearMap.range_eq_top.2 h2, finrank_top] at a2
    omega
  let k : LinearMap.ker L2 ≃ₗ[K] LinearMap.ker L1 := LinearEquiv.ofFinrankEq _ _ hk
  let δ : C ≃ₗ[K] C := (Submodule.prodEquivOfIsCompl _ _ hD2).symm.trans
    ((k.prodCongr (e2.trans e1.symm)).trans (Submodule.prodEquivOfIsCompl _ _ hD1))
  refine ⟨δ, fun c => ?_⟩
  set p := (Submodule.prodEquivOfIsCompl _ _ hD2).symm c with hp
  have hc : c = (p.1 : C) + (p.2 : C) := by
    rw [← Submodule.coe_prodEquivOfIsCompl' _ _ hD2, hp, LinearEquiv.apply_symm_apply]
  have hδ : δ c = ((k p.1 : LinearMap.ker L1) : C) + ((e1.symm (e2 p.2) : D1) : C) := by
    simp only [δ, LinearEquiv.trans_apply, ← hp]
    rw [Submodule.coe_prodEquivOfIsCompl']
    rfl
  rw [hδ, map_add, LinearMap.mem_ker.1 (k p.1).2, zero_add, ← he1, LinearEquiv.apply_symm_apply, he2]
  conv_rhs => rw [hc]
  rw [map_add, LinearMap.mem_ker.1 p.1.2, zero_add]

theorem pi_surj {V : Type*} [AddCommGroup V] [Module K V] {a : ℕ} (ψ : Fin a → Module.Dual K V)
    (hψ : LinearIndependent K ψ) : Function.Surjective (LinearMap.pi ψ) := by
  rw [← LinearMap.range_eq_top]
  by_contra hne
  obtain ⟨f, hf0, hfk⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
  apply hf0
  have hsum : ∑ i, f (Pi.single i 1) • ψ i = 0 := by
    ext v
    have hv : f (LinearMap.pi ψ v) = 0 := hfk ⟨v, rfl⟩
    have hdec : LinearMap.pi ψ v = ∑ i, ψ i v • (Pi.single i 1 : Fin a → K) := by
      ext j
      simp [Finset.sum_apply, Pi.single_apply]
    rw [hdec, map_sum] at hv
    simpa [smul_eq_mul, mul_comm] using hv
  have hc := Fintype.linearIndependent_iff.1 hψ _ hsum
  apply LinearMap.pi_ext'
  intro i
  ext
  simp [hc i]

theorem trans_tuple {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V] {a : ℕ}
    (x y : Fin a → V) (hx : LinearIndependent K x) (hy : LinearIndependent K y) :
    ∃ A : V ≃ₗ[K] V, ∀ j, A (x j) = y j := by
  set U := Submodule.span K (Set.range x)
  set U' := Submodule.span K (Set.range y)
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl U
  obtain ⟨C', hC'⟩ := Submodule.exists_isCompl U'
  let bx := Module.Basis.span hx
  let by' := Module.Basis.span hy
  have hU : Module.finrank K U = a := by rw [Module.finrank_eq_card_basis bx, Fintype.card_fin]
  have hU' : Module.finrank K U' = a := by rw [Module.finrank_eq_card_basis by', Fintype.card_fin]
  have h1 := Submodule.finrank_add_eq_of_isCompl hC
  have h2 := Submodule.finrank_add_eq_of_isCompl hC'
  let eC : C ≃ₗ[K] C' := LinearEquiv.ofFinrankEq _ _ (by omega)
  let eU : U ≃ₗ[K] U' := bx.equiv by' (Equiv.refl _)
  refine ⟨(Submodule.prodEquivOfIsCompl _ _ hC).symm.trans
    ((eU.prodCongr eC).trans (Submodule.prodEquivOfIsCompl _ _ hC')), fun j => ?_⟩
  have hxj : x j ∈ U := Submodule.subset_span ⟨j, rfl⟩
  simp only [LinearEquiv.trans_apply]
  rw [Submodule.prodEquivOfIsCompl_symm_apply_left _ _ hC ⟨x j, hxj⟩]
  rw [Submodule.coe_prodEquivOfIsCompl']
  have : eU ⟨x j, hxj⟩ = ⟨y j, Submodule.subset_span ⟨j, rfl⟩⟩ := by
    have hb : (⟨x j, hxj⟩ : U) = bx j := by ext; simp [bx, Module.Basis.span_apply]
    rw [hb]
    simp only [eU, Module.Basis.equiv_apply, Equiv.refl_apply]
    exact Module.Basis.span_apply hy j
  simp [LinearEquiv.prodCongr_apply, this]

theorem fix_tuple {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V] {a : ℕ}
    (x : Fin a → V) (hx : LinearIndependent K x) (φ ψ : Fin a → Module.Dual K V)
    (hφ : LinearIndependent K φ) (hψ : LinearIndependent K ψ) (h : ∀ i j, φ i (x j) = ψ i (x j)) :
    ∃ B : V ≃ₗ[K] V, (∀ j, B (x j) = x j) ∧ ∀ i v, ψ i (B v) = φ i v := by
  set U := Submodule.span K (Set.range x)
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl U
  set Φ := LinearMap.pi φ
  set Ψ := LinearMap.pi ψ
  have hUeq : Φ ∘ₗ U.subtype = Ψ ∘ₗ U.subtype := by
    apply (Module.Basis.span hx).ext
    intro j
    ext i
    simp [Φ, Ψ, Module.Basis.span_apply, h i j]
  have hUv : ∀ u : U, Φ u = Ψ u := fun u => LinearMap.congr_fun hUeq u
  have hsplit : ∀ v : V, ∃ u ∈ U, ∃ c ∈ C, u + c = v := fun v =>
    Submodule.mem_sup.1 (by rw [hC.sup_eq_top]; exact Submodule.mem_top)
  set R := LinearMap.range (Ψ ∘ₗ U.subtype)
  have hsurj : ∀ Θ : V →ₗ[K] (Fin a → K), Function.Surjective Θ → (∀ u : U, Θ u = Ψ u) →
      Function.Surjective (R.mkQ ∘ₗ Θ ∘ₗ C.subtype) := by
    intro Θ hΘ hΘU w
    obtain ⟨w', rfl⟩ := R.mkQ_surjective w
    obtain ⟨v, rfl⟩ := hΘ w'
    obtain ⟨u, hu, c, hc, rfl⟩ := hsplit v
    refine ⟨⟨c, hc⟩, ?_⟩
    have h0 : R.mkQ (Θ u) = 0 := by
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact ⟨⟨u, hu⟩, (hΘU ⟨u, hu⟩).symm⟩
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, map_add, h0, zero_add]
  obtain ⟨δ, hδ⟩ := surj_equiv (R.mkQ ∘ₗ Ψ ∘ₗ C.subtype) (R.mkQ ∘ₗ Φ ∘ₗ C.subtype)
    (hsurj Ψ (pi_surj ψ hψ) fun _ => rfl) (hsurj Φ (pi_surj φ hφ) hUv)
  set D : C →ₗ[K] (Fin a → K) := Φ ∘ₗ C.subtype - Ψ ∘ₗ C.subtype ∘ₗ δ.toLinearMap
  have hD : ∀ c, D c ∈ R := by
    intro c
    have e := hδ c
    simp only [LinearMap.comp_apply, Submodule.mkQ_apply] at e
    exact (Submodule.Quotient.eq R).1 e.symm
  obtain ⟨s, hs⟩ := LinearMap.exists_rightInverse_of_surjective (Ψ ∘ₗ U.subtype).rangeRestrict
    (LinearMap.range_rangeRestrict _)
  set β : C →ₗ[K] U := s ∘ₗ D.codRestrict R hD
  have hβ : ∀ c, Ψ (β c : V) = D c := by
    intro c
    have e := congrArg Subtype.val (LinearMap.congr_fun hs (D.codRestrict R hD c))
    simpa [β] using e
  set P := (Submodule.prodEquivOfIsCompl _ _ hC).symm
  have hP : ∀ (u : U) (c : C), P ((u : V) + c) = (u, c) := by
    intro u c
    have e : (u : V) + c = Submodule.prodEquivOfIsCompl _ _ hC (u, c) :=
      (Submodule.coe_prodEquivOfIsCompl' _ _ hC (u, c)).symm
    rw [e]
    exact LinearEquiv.symm_apply_apply _ _
  set B0 : V →ₗ[K] V := (U.subtype ∘ₗ LinearMap.fst K U C + U.subtype ∘ₗ β ∘ₗ LinearMap.snd K U C +
    C.subtype ∘ₗ δ.toLinearMap ∘ₗ LinearMap.snd K U C) ∘ₗ P.toLinearMap
  have hB0 : ∀ (u : U) (c : C), B0 ((u : V) + c) = (u : V) + (β c : V) + (δ c : V) := by
    intro u c
    simp [B0, hP u c]
  have hinj : Function.Injective B0 := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    obtain ⟨u, hu, c, hc, rfl⟩ := hsplit v
    have e := hB0 ⟨u, hu⟩ ⟨c, hc⟩
    rw [hv] at e
    have hδU : (δ ⟨c, hc⟩ : V) ∈ U := by
      have : (δ ⟨c, hc⟩ : V) = -(u + (β ⟨c, hc⟩ : V)) := eq_neg_of_add_eq_zero_right e.symm
      rw [this]
      exact U.neg_mem (U.add_mem hu (β _).2)
    have h1 : (δ ⟨c, hc⟩ : V) = 0 := Submodule.disjoint_def.1 hC.disjoint _ hδU (δ _).2
    have h2 : (⟨c, hc⟩ : C) = 0 := δ.injective (by rw [map_zero]; exact Subtype.ext h1)
    have hc0 : c = 0 := congrArg Subtype.val h2
    subst hc0
    have hβ0 : (β ⟨0, hc⟩ : V) = 0 := by
      rw [show (⟨0, hc⟩ : C) = 0 from rfl, map_zero]; rfl
    rw [h1, hβ0, add_zero, add_zero] at e
    rw [add_zero]
    exact e.symm
  refine ⟨LinearEquiv.ofInjectiveEndo B0 hinj, fun j => ?_, fun i v => ?_⟩
  · have hxj : x j ∈ U := Submodule.subset_span ⟨j, rfl⟩
    have e := hB0 ⟨x j, hxj⟩ 0
    simp only [map_zero, Submodule.coe_zero, add_zero] at e
    exact e
  · obtain ⟨u, hu, c, hc, rfl⟩ := hsplit v
    have hv : Ψ (B0 (u + c)) = Φ (u + c) := by
      rw [show u + c = ((⟨u, hu⟩ : U) : V) + ((⟨c, hc⟩ : C) : V) from rfl, hB0]
      simp only [map_add, hβ, hUv ⟨u, hu⟩, D, LinearMap.sub_apply, LinearMap.comp_apply,
        Submodule.subtype_apply, LinearEquiv.coe_coe]
      abel
    exact congrFun hv i

theorem glPair {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V] {a : ℕ}
    (x y : Fin a → V) (ξ η : Fin a → Module.Dual K V) (hx : LinearIndependent K x)
    (hy : LinearIndependent K y) (hξ : LinearIndependent K ξ) (hη : LinearIndependent K η)
    (h : ∀ i j, ξ i (x j) = η i (y j)) :
    ∃ A : V ≃ₗ[K] V, (∀ j, A (x j) = y j) ∧ ∀ i v, η i (A v) = ξ i v := by
  obtain ⟨A0, hA0⟩ := trans_tuple x y hx hy
  set η' : Fin a → Module.Dual K V := fun i => η i ∘ₗ A0.toLinearMap
  have hη' : LinearIndependent K η' := by
    rw [Fintype.linearIndependent_iff] at hη ⊢
    intro c hc i
    apply hη c _ i
    ext v
    have e := LinearMap.congr_fun hc (A0.symm v)
    simpa [η'] using e
  obtain ⟨B, hBx, hB⟩ := fix_tuple x hx ξ η' hξ hη' (fun i j => by simp [η', hA0, h])
  refine ⟨B.trans A0, fun j => by simp [hBx, hA0], fun i v => ?_⟩
  simpa [η'] using hB i v

end Formalism.L2.SG.Pf.NcX.LT.GLP
