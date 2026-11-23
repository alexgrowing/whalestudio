import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.RCountAt
import Development.AutomorphicArithmetic.Foundations.Convolution.WeightRankUnits.USide
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAutFormsWeightLevelFiniteSumFixedVectorsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeOperatorTestFamilyPreservesLevelFormsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryHeckeOperatorLevelIndicatorEqInvIndex
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexNeZeroOfSubsetCpt
open UpperTheory.V.Z.Mult UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open scoped Classical

namespace UpperTheory.V.Z.Mult.LevelTrace

section Generic

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]

private theorem mem_fixed_iff (ρ : Representation ℂ G V) (U : Subgroup G) (v : V) :
    v ∈ fixed ρ U ↔ ∀ k ∈ U, ρ k v = v := by
  constructor
  · intro h k hk
    simpa using h ⟨k, hk⟩
  · intro h k
    simpa using h k k.2

private theorem fixed_anti (ρ : Representation ℂ G V) {U₂ U₁ : Subgroup G} (h : U₂ ≤ U₁) :
    fixed ρ U₁ ≤ fixed ρ U₂ := fun v hv =>
  (mem_fixed_iff ρ U₂ v).2 fun k hk => (mem_fixed_iff ρ U₁ v).1 hv k (h hk)

private theorem trOn_eq_of_range (M₁ M₂ : Submodule ℂ V) [FiniteDimensional ℂ M₁] [FiniteDimensional ℂ M₂]
    (hle : M₂ ≤ M₁) (L₁ L₂ : V →ₗ[ℂ] V) (h : ∀ v ∈ M₁, L₁ v ∈ M₂) (he : ∀ v ∈ M₂, L₁ v = L₂ v) :
    trOn M₁ L₁ = trOn M₂ L₂ := by
  have h₁ : ∀ v ∈ M₁, L₁ v ∈ M₁ := fun v hv => hle (h v hv)
  have h₂ : ∀ v ∈ M₂, L₂ v ∈ M₂ := fun v hv => by
    rw [← he v hv]
    exact h v (hle hv)
  unfold trOn
  rw [dif_pos h₁, dif_pos h₂]
  let g : M₁ →ₗ[ℂ] M₂ := L₁.restrict h
  let i : M₂ →ₗ[ℂ] M₁ := Submodule.inclusion hle
  have e₁ : L₁.restrict h₁ = i ∘ₗ g := by
    ext v
    rfl
  have e₂ : L₂.restrict h₂ = g ∘ₗ i := by
    ext v
    exact (he v v.2).symm
  rw [e₁, e₂]
  exact LinearMap.trace_comp_comm' g i

private theorem apply_finsum (ρ : Representation ℂ G V) (U : Subgroup G) (F : G → ℂ) (v : V) :
    (∑ᶠ q : G ⧸ U, F q.out • (ρ q.out ∘ₗ (LinearMap.id : V →ₗ[ℂ] V))) v = ∑ᶠ q : G ⧸ U, F q.out • ρ q.out v := by
  by_cases hv : v = 0
  · subst hv
    simp
  have hinj : ∀ g : G, ρ g v ≠ 0 := by
    intro g h0
    apply hv
    have h1 : ρ g⁻¹ (ρ g v) = v := by
      rw [← Module.End.mul_apply, ← map_mul]
      simp
    rw [← h1, h0, map_zero]
  have hs : (Function.support fun q : G ⧸ U => F q.out • (ρ q.out ∘ₗ (LinearMap.id : V →ₗ[ℂ] V))) =
      Function.support fun q : G ⧸ U => F q.out • ρ q.out v := by
    ext q
    simp only [Function.mem_support]
    constructor
    · intro h h0
      rcases smul_eq_zero.1 h0 with h1 | h1
      · exact h (by rw [h1, zero_smul])
      · exact hinj _ h1
    · intro h h0
      apply h
      have := congrArg (fun L : V →ₗ[ℂ] V => L v) h0
      simpa using this
  by_cases hf : (Function.support fun q : G ⧸ U => F q.out • (ρ q.out ∘ₗ (LinearMap.id : V →ₗ[ℂ] V))).Finite
  · exact map_finsum (LinearMap.applyₗ v) hf
  · rw [finsum_of_infinite_support hf, finsum_of_infinite_support (hs ▸ hf)]
    simp

private theorem out_inv {X : Type} (U : Subgroup G) (c : G → X) (hc : ∀ u ∈ U, ∀ x, c (x * u) = c x) (g : G) :
    c (Quotient.out (g : G ⧸ U)) = c g := by
  have h : (Quotient.out (g : G ⧸ U))⁻¹ * g ∈ U := QuotientGroup.eq.1 (QuotientGroup.out_eq' _)
  have := hc _ h (Quotient.out (g : G ⧸ U))
  rw [mul_inv_cancel_left] at this
  exact this.symm

private theorem levOp_mem_fixed (ρ : Representation ℂ G V) (K U₂ U₁ : Subgroup G) (F : G → ℂ)
    (hl : ∀ k ∈ U₁, ∀ x, F (k * x) = F x) (hr : ∀ k ∈ U₂, ∀ x, F (x * k) = F x) {v : V} (hv : v ∈ fixed ρ U₂) :
    levOp ρ K U₂ F LinearMap.id v ∈ fixed ρ U₁ := by
  have hfix := (mem_fixed_iff ρ U₂ v).1 hv
  rw [mem_fixed_iff]
  intro k hk
  let c : G → V := fun g => F g • ρ g v
  have hc : ∀ u ∈ U₂, ∀ x, c (x * u) = c x := by
    intro u hu x
    simp only [c]
    rw [hr u hu x, map_mul, Module.End.mul_apply, hfix u hu]
  let e : V ≃+ V :=
    { toFun := ρ k
      invFun := ρ k⁻¹
      left_inv := fun x => by
        rw [← Module.End.mul_apply, ← map_mul]
        simp
      right_inv := fun x => by
        rw [← Module.End.mul_apply, ← map_mul]
        simp
      map_add' := map_add _ }
  have key : ∀ q : G ⧸ U₂, e (c q.out) = c ((k • q : G ⧸ U₂).out) := by
    intro q
    have hq : k • q = ((k * q.out : G) : G ⧸ U₂) := by
      conv_lhs => rw [← QuotientGroup.out_eq' q]
      rfl
    rw [hq, out_inv U₂ c hc]
    show ρ k (F q.out • ρ q.out v) = F (k * q.out) • ρ (k * q.out) v
    rw [hl k hk, map_smul, map_mul, Module.End.mul_apply]
  have hsum : ρ k (∑ᶠ q : G ⧸ U₂, c q.out) = ∑ᶠ q : G ⧸ U₂, c q.out := by
    show e (∑ᶠ q : G ⧸ U₂, c q.out) = _
    rw [AddEquiv.map_finsum, finsum_congr key]
    exact finsum_comp_equiv (MulAction.toPerm k) (f := fun q : G ⧸ U₂ => c q.out)
  unfold levOp
  rw [LinearMap.smul_apply, apply_finsum, map_smul]
  exact congrArg _ hsum

private theorem finsum_fibre {U₂ U₁ : Subgroup G} (hle : U₂ ≤ U₁) (hN : U₂.relIndex U₁ ≠ 0) (c : G → V)
    (hc : ∀ u ∈ U₁, ∀ x, c (x * u) = c x) :
    ∑ᶠ q : G ⧸ U₂, c q.out = U₂.relIndex U₁ • ∑ᶠ p : G ⧸ U₁, c p.out := by
  let e := Subgroup.quotientEquivProdOfLE hle
  haveI : Finite (U₁ ⧸ U₂.subgroupOf U₁) := Nat.finite_of_card_ne_zero hN
  have h1 : ∀ q : G ⧸ U₂, c q.out = c (e q).1.out := by
    intro q
    have : (e q).1 = ((q.out : G) : G ⧸ U₁) := by
      conv_lhs => rw [← QuotientGroup.out_eq' q]
      rfl
    rw [this, out_inv U₁ c hc]
  rw [finsum_congr h1, finsum_comp_equiv e (f := fun x : (G ⧸ U₁) × (U₁ ⧸ U₂.subgroupOf U₁) => c x.1.out)]
  by_cases hb : (Function.support fun p : G ⧸ U₁ => c p.out).Finite
  · have hs : (Function.support fun x : (G ⧸ U₁) × (U₁ ⧸ U₂.subgroupOf U₁) => c x.1.out).Finite :=
      (hb.prod (Set.finite_univ (α := U₁ ⧸ U₂.subgroupOf U₁))).subset fun x hx => ⟨hx, trivial⟩
    rw [finsum_curry _ hs]
    have h2 : ∀ p : G ⧸ U₁, ∑ᶠ _ : U₁ ⧸ U₂.subgroupOf U₁, c p.out = U₂.relIndex U₁ • c p.out := by
      intro p
      haveI := Fintype.ofFinite (U₁ ⧸ U₂.subgroupOf U₁)
      rw [finsum_eq_sum_of_fintype, Finset.sum_const, Finset.card_univ]
      simp [Subgroup.relIndex, Subgroup.index, Nat.card_eq_fintype_card]
    simp only [h2]
    exact (map_finsum (nsmulAddMonoidHom (U₂.relIndex U₁)) hb).symm
  · rw [finsum_of_infinite_support hb, smul_zero, finsum_of_infinite_support]
    intro hfin
    apply hb
    refine (hfin.image Prod.fst).subset fun p hp => ?_
    exact ⟨(p, ((1 : U₁) : U₁ ⧸ U₂.subgroupOf U₁)), hp, rfl⟩

private theorem levOp_eq (ρ : Representation ℂ G V) (K U₂ U₁ : Subgroup G) (F : G → ℂ) (hle : U₂ ≤ U₁) (hK : U₁ ≤ K)
    (hN : U₂.relIndex U₁ ≠ 0) (hr : ∀ k ∈ U₁, ∀ x, F (x * k) = F x) {v : V} (hv : v ∈ fixed ρ U₁) :
    levOp ρ K U₂ F LinearMap.id v = levOp ρ K U₁ F LinearMap.id v := by
  have hfix := (mem_fixed_iff ρ U₁ v).1 hv
  have hc : ∀ u ∈ U₁, ∀ x, (fun g : G => F g • ρ g v) (x * u) = (fun g : G => F g • ρ g v) x := by
    intro u hu x
    simp only
    rw [hr u hu x, map_mul, Module.End.mul_apply, hfix u hu]
  have hs := finsum_fibre hle hN (fun g : G => F g • ρ g v) hc
  unfold levOp
  rw [LinearMap.smul_apply, LinearMap.smul_apply, apply_finsum, apply_finsum, hs,
    ← Subgroup.relIndex_mul_relIndex U₂ U₁ K hle hK, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  congr 1
  have hN' : ((U₂.relIndex U₁ : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hN
  rw [Nat.cast_mul, mul_inv, mul_right_comm, inv_mul_cancel₀ hN', one_mul]

private theorem trOn_levOp_eq (ρ : Representation ℂ G V) (K U₂ U₁ : Subgroup G) (F : G → ℂ) (hle : U₂ ≤ U₁)
    (hK : U₁ ≤ K) (hN : U₂.relIndex U₁ ≠ 0) (hr : ∀ k ∈ U₁, ∀ x, F (x * k) = F x) (M₂ M₁ : Submodule ℂ V)
    [FiniteDimensional ℂ M₂] [FiniteDimensional ℂ M₁] (hM : M₁ ≤ M₂) (hfix : M₁ ≤ fixed ρ U₁)
    (hmap : ∀ v ∈ M₂, levOp ρ K U₂ F LinearMap.id v ∈ M₁) :
    trOn M₂ (levOp ρ K U₂ F LinearMap.id) = trOn M₁ (levOp ρ K U₁ F LinearMap.id) :=
  trOn_eq_of_range M₂ M₁ hM _ _ hmap fun _ hv => levOp_eq ρ K U₂ U₁ F hle hK hN hr (hfix hv)

end Generic

section Global

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

private theorem globLev_mono (S : Set (Pl E)) {K₂ K₁ : ∀ w : Pl E, Subgroup (UL n w)} (h : ∀ w, K₂ w ≤ K₁ w) :
    globLev S K₂ ≤ globLev S K₁ := by
  intro k hk
  rw [mem_globLev_iff] at hk ⊢
  intro w hw
  obtain ⟨a, ha, e⟩ := hk w hw
  exact ⟨a, h w ha, e⟩

private theorem relIndex_glob_ne (hU : GlobalTheory.BCT.Unr E) (S : Set (Pl E)) (hS : IsSection S)
    (K : ∀ w : Pl E, Subgroup (UL n w)) (hK : IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K) :
    (globLev S K).relIndex (globLev S (KL n)) ≠ 0 := by
  have h := HopLev2.relIndex_globLev hU S hS K (fun w => (hK.1 w).2.1) hK.2
  have h2 : (∏ᶠ w ∈ S, (((K w).relIndex (KL n w) : ℕ) : ℂ)) ≠ 0 :=
    finprod_mem_induction (· ≠ 0) one_ne_zero (fun _ _ => mul_ne_zero) fun w _ =>
      Nat.cast_ne_zero.2 (GlobalTheory.LocFinU.relIndex_ne_zero_of_subset_cpt _ _ (hK.1 w).1 _
        (GlobalTheory.LocFinU.isCompact_KL n w) subset_rfl)
  rw [← h] at h2
  exact_mod_cast h2

private theorem forms_le_fixed (S : Set (Pl E)) (lam : InfinitePlace E → DomWeight n)
    (K : ∀ w : Pl E, Subgroup (UL n w)) : forms S lam K ≤ fixed (RF E n) (globLev S K) :=
  iSup₂_le fun _ _ => inf_le_right

private theorem forms_mono (S : Set (Pl E)) (lam : InfinitePlace E → DomWeight n)
    {K₂ K₁ : ∀ w : Pl E, Subgroup (UL n w)} (h : ∀ w, K₂ w ≤ K₁ w) : forms S lam K₁ ≤ forms S lam K₂ :=
  iSup₂_mono fun _ _ => inf_le_inf_left _ (fixed_anti _ (globLev_mono S h))

private theorem hop_mem_forms (S : Set (Pl E)) (hS : IsSection S) (lam : InfinitePlace E → DomWeight n)
    (K₂ K₁ : ∀ w : Pl E, Subgroup (UL n w))
    (hK₂ : IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K₂)
    (hUle : globLev S K₂ ≤ globLev S K₁) (f : ∀ w : Pl E, UL n w → ℂ) (hf₂ : GlobalTheory.BCT.IsTest (KL n) K₂ f)
    (hl : ∀ k ∈ globLev S K₁, ∀ x, globFn S f (k * x) = globFn S f x)
    (hr : ∀ k ∈ globLev S K₂, ∀ x, globFn S f (x * k) = globFn S f x) :
    ∀ v ∈ forms S lam K₂, hop S K₂ f v ∈ forms S lam K₁ := by
  have hmap : forms S lam K₂ ≤ (forms S lam K₁).comap (hop S K₂ f) := by
    refine iSup₂_le fun π hπ v hv => ?_
    have h1 : hop S K₂ f v ∈ π ⊓ fixed (RF E n) (globLev S K₂) :=
      GlobalTheory.T.heckeOperator_testFamily_preserves_level_forms E n S hS K₂ hK₂ f hf₂ π hπ.1 v hv
    have h2 : levOp (RF E n) (globLev S (KL n)) (globLev S K₂) (globFn S f) LinearMap.id v ∈
        fixed (RF E n) (globLev S K₁) :=
      levOp_mem_fixed (RF E n) (globLev S (KL n)) (globLev S K₂) (globLev S K₁) (globFn S f) hl hr
        (Submodule.mem_inf.1 hv).2
    have h3 : π ⊓ fixed (RF E n) (globLev S K₁) ≤ forms S lam K₁ := by
      unfold forms
      exact le_iSup₂_of_le π hπ le_rfl
    exact h3 (Submodule.mem_inf.2 ⟨(Submodule.mem_inf.1 h1).1, h2⟩)
  exact fun v hv => hmap hv

end Global

end UpperTheory.V.Z.Mult.LevelTrace

open UpperTheory.V.Z.Mult.LevelTrace in
theorem UpperTheory.V.Z.Mult.levTr :
    UpperTheory.V.Z.Mult.LevTr := by
  intro E _ _ _ hU n hn S hS lam K' K'' hK' hK'' hle f hf
  have hf'' : GlobalTheory.BCT.IsTest (KL n) K'' f :=
    ⟨fun w => ⟨(hf.1 w).1, fun k hk => (hf.1 w).2 k (hle w hk)⟩, hf.2⟩
  have hUle : globLev S K'' ≤ globLev S K' := globLev_mono S hle
  have hK0 : globLev S K' ≤ globLev S (KL n) := globLev_mono S fun w => (hK'.1 w).2.1
  have hN : (globLev S K'').relIndex (globLev S K') ≠ 0 := by
    have := relIndex_glob_ne hU S hS K'' hK''
    rw [← Subgroup.relIndex_mul_relIndex _ _ _ hUle hK0] at this
    exact left_ne_zero_of_mul this
  have hF := globFn_inv S K' f fun w => (hf.1 w).2
  haveI := (GlobalTheory.T.unitaryAutForms_weight_level_finite_sum_fixed_vectors E hU n hn S hS lam K' hK').1
  haveI := (GlobalTheory.T.unitaryAutForms_weight_level_finite_sum_fixed_vectors E hU n hn S hS lam K'' hK'').1
  exact trOn_levOp_eq (RF E n) (globLev S (KL n)) (globLev S K'') (globLev S K') (globFn S f) hUle hK0 hN
    (fun k hk x => (hF k hk x).2) (forms S lam K'') (forms S lam K') (forms_mono S lam hle)
    (forms_le_fixed S lam K')
    (hop_mem_forms S hS lam K'' K' hK'' hUle f hf'' (fun k hk x => (hF k hk x).1)
      (fun k hk x => (hF k (hUle hk) x).2))
