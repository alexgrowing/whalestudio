import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisCochains.GLinkQuot

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module UpperTheory.V UpperTheory.V.Fr UpperTheory.V.GC

namespace UpperTheory.V.GC

private theorem inflKer_lin {k W P H : Type} [Field k] [AddCommGroup W] [Module k W] [AddCommGroup P] [Module k P]
    [AddCommGroup H] [Module k H] [Module.Finite k P] (r : W →ₗ[k] P) (τ : W →ₗ[k] H)
    (h : LinearMap.ker r ≤ LinearMap.ker τ) (U : Submodule k P) (hU : U ≤ (LinearMap.ker τ).map r) :
    Module.Finite k (LinearMap.range τ) ∧ finrank k (LinearMap.range τ) + finrank k U ≤ finrank k P := by
  let K := (LinearMap.ker τ).map r
  let s : W →ₗ[k] P ⧸ K := K.mkQ.comp r
  have hs : LinearMap.ker s = LinearMap.ker τ := by
    rw [LinearMap.ker_comp, Submodule.ker_mkQ, Submodule.comap_map_eq, sup_eq_left.2 h]
  have e : LinearMap.range s ≃ₗ[k] LinearMap.range τ :=
    s.quotKerEquivRange.symm.trans ((Submodule.quotEquivOfEq _ _ hs).trans τ.quotKerEquivRange)
  refine ⟨Module.Finite.equiv e, ?_⟩
  rw [← e.finrank_eq, ← K.finrank_quotient_add_finrank]
  exact add_le_add (Submodule.finrank_le _) (Submodule.finrank_mono hU)

section

variable {Γ' Γ k M : Type} [Group Γ'] [TopologicalSpace Γ'] [IsTopologicalGroup Γ'] [Group Γ] [TopologicalSpace Γ]
  [Field k] [AddCommGroup M] [Module k M] [TopologicalSpace M] [DiscreteTopology M]
  (p : Γ' →* Γ) (hp : Continuous p) (ρ : Representation k Γ M)

private def inflW : Submodule k (Z2 ρ × (Γ' → M)) where
  carrier := {x | Continuous x.2 ∧ x.2 1 = 0 ∧ ∀ g h, ρ (p g) (x.2 h) - x.2 (g * h) + x.2 g = x.1.1 (p g, p h)}
  zero_mem' := ⟨continuous_const, rfl, by simp⟩
  add_mem' := by
    rintro x y ⟨a1, a2, a3⟩ ⟨b1, b2, b3⟩
    refine ⟨a1.add b1, by simp [a2, b2], fun g h => ?_⟩
    simp only [Prod.snd_add, Prod.fst_add, Pi.add_apply, map_add, Submodule.coe_add, ← a3, ← b3]
    abel
  smul_mem' := by
    rintro c x ⟨a1, a2, a3⟩
    refine ⟨a1.const_smul c, by simp [a2], fun g h => ?_⟩
    simp only [Prod.smul_snd, Prod.smul_fst, Pi.smul_apply, map_smul, Submodule.coe_smul, ← a3, smul_add, smul_sub]

omit [IsTopologicalGroup Γ'] in
private theorem inflW_mul (x : inflW p ρ) (n : Γ') (hn : p n = 1) (g : Γ') :
    x.1.2 (n * g) = x.1.2 n + x.1.2 g ∧ x.1.2 (g * n) = x.1.2 g + ρ (p g) (x.1.2 n) := by
  obtain ⟨⟨z, β⟩, -, h1, h⟩ := x
  dsimp only at h1 h ⊢
  have a := h 1 g
  have b := h g 1
  have c := h n g
  have d := h g n
  simp only [h1, hn, map_one, one_mul, mul_one, map_zero, Module.End.one_apply] at a b c d
  rw [← a] at c
  rw [← b] at d
  constructor
  · linear_combination (norm := abel1) -c
  · linear_combination (norm := abel1) -d

omit [IsTopologicalGroup Γ'] in
private theorem inflW_conj (x : inflW p ρ) (n : Γ') (hn : p n = 1) (g : Γ') :
    x.1.2 (g * n * g⁻¹) = ρ (p g) (x.1.2 n) := by
  have a := (inflW_mul p ρ x (g * n * g⁻¹) (by simp [hn]) g).1
  have b := (inflW_mul p ρ x n hn g).2
  rw [inv_mul_cancel_right, b, add_comm] at a
  exact (add_right_cancel a).symm

private theorem inflW_desc [CompactSpace Γ'] [T2Space Γ] (hp : Continuous p) (hs : Function.Surjective p)
    (S : Set Γ') (hS : p.ker = (Subgroup.normalClosure S).topologicalClosure) (x : inflW p ρ)
    (hx : ∀ s ∈ S, x.1.2 s = 0) : ∃ b : Γ → M, Continuous b ∧ ∀ g, b (p g) = x.1.2 g := by
  let N : Subgroup Γ' :=
    { carrier := {n | p n = 1 ∧ x.1.2 n = 0}
      one_mem' := ⟨map_one _, x.2.2.1⟩
      mul_mem' := by
        rintro a b ⟨a1, a2⟩ ⟨b1, b2⟩
        exact ⟨by simp [a1, b1], by rw [(inflW_mul p ρ x a a1 b).1, a2, b2, add_zero]⟩
      inv_mem' := by
        rintro a ⟨a1, a2⟩
        refine ⟨by simp [a1], ?_⟩
        have := (inflW_mul p ρ x a a1 a⁻¹).1
        rw [mul_inv_cancel, x.2.2.1, a2, zero_add] at this
        exact this.symm }
  haveI : N.Normal := ⟨fun n hn g => ⟨by simp [hn.1], by rw [inflW_conj p ρ x n hn.1, hn.2, map_zero]⟩⟩
  have hc : IsClosed (N : Set Γ') :=
    (isClosed_eq hp continuous_const).inter (isClosed_eq x.2.1 continuous_const)
  have hN : p.ker ≤ N := by
    rw [hS]
    refine Subgroup.topologicalClosure_minimal _ (Subgroup.normalClosure_le_normal fun s h => ⟨?_, hx s h⟩) hc
    have : s ∈ p.ker := hS ▸ Subgroup.le_topologicalClosure _ (Subgroup.subset_normalClosure h)
    exact this
  have hb : ∀ g, x.1.2 (Function.surjInv hs (p g)) = x.1.2 g := fun g => by
    have h1 : p (g⁻¹ * Function.surjInv hs (p g)) = 1 := by simp [Function.surjInv_eq hs]
    have := (inflW_mul p ρ x _ h1 g).2
    rw [mul_inv_cancel_left, (hN h1).2, map_zero, add_zero] at this
    exact this
  refine ⟨fun γ => x.1.2 (Function.surjInv hs γ), ?_, hb⟩
  rw [(hp.isClosedMap.isQuotientMap hp hs).continuous_iff]
  exact x.2.1.congr fun g => (hb g).symm

private def inflR {T : Type} (Dq Jq : T → Subgroup Γ') (hJ : ∀ q, Jq q ≤ p.ker) :
    inflW p ρ →ₗ[k] ∀ q, eqHom (ρ.comp p) (Dq q) (Jq q) where
  toFun x q := ⟨fun j => x.1.2 j, (IsLocallyConstant.iff_continuous _).2 (x.2.1.comp continuous_subtype_val),
    fun a b => (inflW_mul p ρ x a (hJ q a.2) b).1, fun d _ j j' h => by
      dsimp only
      rw [h]
      exact inflW_conj p ρ x j (hJ q j.2) d⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def inflJ : Z1 (ρ.comp p) →ₗ[k] inflW p ρ where
  toFun f := ⟨(0, f.1), f.2.1, by simpa using f.2.2 1 1, fun g h => by
    dsimp only
    rw [f.2.2]
    simp⟩
  map_add' _ _ := by ext <;> simp
  map_smul' _ _ := by ext <;> simp

omit [IsTopologicalGroup Γ'] in
private theorem inflW_range :
    LinearMap.range ((Submodule.mkQ _ : Z2 ρ →ₗ[k] H2 ρ) ∘ₗ LinearMap.fst _ _ _ ∘ₗ (inflW p ρ).subtype) =
      LinearMap.ker (resH2 ρ p hp) := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    refine (Submodule.Quotient.mk_eq_zero _).2 ((separated_dvr_second_cohomology_mem _ _).2 ⟨x.1.2, x.2.1, ?_⟩)
    funext q
    exact x.2.2.2 q.1 q.2
  · intro y hy
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    obtain ⟨β, hβ, he⟩ := (separated_dvr_second_cohomology_mem _ _).1 ((Submodule.Quotient.mk_eq_zero _).1 hy)
    have he' : ∀ g h, ρ (p g) (β h) - β (g * h) + β g = z.1 (p g, p h) := fun g h => congrFun he (g, h)
    let c : Z2 ρ := ⟨fun q => ρ q.1 (β 1), ?_, fun g h k => by simp⟩
    · refine ⟨⟨(z - c, fun g => β g - β 1), hβ.sub continuous_const, sub_self _, fun g h => ?_⟩, ?_⟩
      · simp only [c, Submodule.coe_sub, Pi.sub_apply, ← he', map_sub]
        abel
      · refine (Submodule.Quotient.eq _).2 ((separated_dvr_second_cohomology_mem _ _).2 ⟨fun _ => -β 1, continuous_const, ?_⟩)
        funext q
        simp [c, d1]
    · have h1 : β 1 = z.1 (1, 1) := by simpa using he' 1 1
      have h2 : ∀ g, ρ g (z.1 (1, 1)) = z.1 (g, 1) := fun g => by
        have := z.2.2 g 1 1
        simp only [mul_one, sub_add_cancel] at this
        exact sub_eq_zero.1 this
      simp only [h1, h2]
      exact z.2.1.comp (continuous_fst.prodMk continuous_const)

end

end UpperTheory.V.GC

theorem UpperTheory.V.GC.inflKer :
    ∀ (l : ℕ) [Fact l.Prime] (Γ' : Type) [Group Γ'] [TopologicalSpace Γ'] [IsTopologicalGroup Γ'] [CompactSpace Γ'] [T2Space Γ'] [TotallyDisconnectedSpace Γ'] (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [T2Space Γ] [TotallyDisconnectedSpace Γ] (p : Γ' →* Γ) (hp : Continuous p), Function.Surjective p →
    ∀ (k : Type) [Field k] [Finite k] [CharP k l] (M : Type) [AddCommGroup M] [Module k M] [Module.Finite k M] [TopologicalSpace M] [DiscreteTopology M] (ρ : Representation k Γ M), ContAction ρ → ∀ (T : Type) [Fintype T] (Dq Jq : T → Subgroup Γ'), p.ker = (Subgroup.normalClosure (⋃ q, (Jq q : Set Γ'))).topologicalClosure →
    (∀ q, Module.Finite k (eqHom (ρ.comp p) (Dq q) (Jq q))) → Module.Finite k (H1 (ρ.comp p)) →
    Module.Finite k (H1 ρ) ∧ Module.Finite k (LinearMap.ker (resH2 ρ p hp)) ∧
    finrank k (LinearMap.ker (resH2 ρ p hp)) + finrank k (H1 (ρ.comp p)) ≤ finrank k (H1 ρ) + ∑ q, finrank k (eqHom (ρ.comp p) (Dq q) (Jq q)) := by
  intro l _ Γ' _ _ _ _ _ _ Γ _ _ _ _ _ _ p hp hs k _ _ _ M _ _ _ _ _ ρ _ T _ Dq Jq hker hfin hH
  have hJ : ∀ q, Jq q ≤ p.ker := fun q s h =>
    hker ▸ Subgroup.le_topologicalClosure _ (Subgroup.subset_normalClosure (Set.mem_iUnion.2 ⟨q, h⟩))
  let r := inflR p ρ Dq Jq hJ
  have hd : ∀ x, r x = 0 → ∃ b : Γ → M, Continuous b ∧ ∀ g, b (p g) = x.1.2 g := fun x hx =>
    inflW_desc p ρ hp hs _ hker x fun s h => by
      obtain ⟨q, hq⟩ := Set.mem_iUnion.1 h
      exact congrFun (congrArg Subtype.val (congrFun hx q)) ⟨s, hq⟩
  have hinj : Function.Injective (resH1 ρ p hp) := by
    rw [injective_iff_map_eq_zero]
    intro y hy
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    obtain ⟨m, hm⟩ := (mem_coboundaries1 _ _).1 ((Submodule.Quotient.mk_eq_zero _).1 hy)
    refine (Submodule.Quotient.mk_eq_zero _).2 ((mem_coboundaries1 _ _).2 ⟨m, fun g => ?_⟩)
    obtain ⟨g, rfl⟩ := hs g
    exact hm g
  haveI hF : Module.Finite k (H1 ρ) := Module.Finite.of_injective _ hinj
  let r1 : H1 (ρ.comp p) →ₗ[k] ∀ q, eqHom (ρ.comp p) (Dq q) (Jq q) :=
    Submodule.liftQ _ (r.comp (inflJ p ρ)) fun f hf => by
      obtain ⟨m, hm⟩ := (mem_coboundaries1 _ _).1 hf
      funext q
      refine Subtype.ext (funext fun j => (hm j).trans ?_)
      have : p j = 1 := hJ q j.2
      simp [this]
  have hk1 : LinearMap.ker r1 ≤ LinearMap.range (resH1 ρ p hp) := by
    intro y hy
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    obtain ⟨b, hb, he⟩ := hd (inflJ p ρ z) hy
    refine ⟨Submodule.Quotient.mk ⟨b, hb, fun g h => ?_⟩, congrArg _ (Subtype.ext (funext he))⟩
    obtain ⟨g, rfl⟩ := hs g
    obtain ⟨h, rfl⟩ := hs h
    rw [← map_mul, he, he, he]
    exact z.2.2 g h
  obtain ⟨h1, h2⟩ := inflKer_lin r
    ((Submodule.mkQ _ : Z2 ρ →ₗ[k] H2 ρ) ∘ₗ LinearMap.fst _ _ _ ∘ₗ (inflW p ρ).subtype) (fun x hx => by
      obtain ⟨b, hb, he⟩ := hd x hx
      refine (Submodule.Quotient.mk_eq_zero _).2 ((separated_dvr_second_cohomology_mem _ _).2 ⟨b, hb, ?_⟩)
      funext ⟨g, h⟩
      obtain ⟨g, rfl⟩ := hs g
      obtain ⟨h, rfl⟩ := hs h
      rw [d1_apply, ← map_mul, he, he, he]
      exact x.2.2.2 g h) (LinearMap.range r1) (by
      rintro _ ⟨y, rfl⟩
      obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      exact ⟨inflJ p ρ z, (Submodule.mkQ _).map_zero, rfl⟩)
  rw [inflW_range p hp ρ] at h1 h2
  refine ⟨hF, h1, ?_⟩
  rw [Module.finrank_pi_fintype] at h2
  have h3 := r1.finrank_range_add_finrank_ker
  have h4 := (Submodule.finrank_mono hk1).trans (LinearMap.finrank_range_le _)
  have h5 : finrank k (H1 (ρ.comp p)) ≤ finrank k (LinearMap.range r1) + finrank k (H1 ρ) :=
    h3.symm.le.trans (Nat.add_le_add_left h4 _)
  refine (Nat.add_le_add_left h5 _).trans ?_
  rw [← add_assoc, add_comm]
  exact Nat.add_le_add_left h2 _
