import Mathlib
import GroundTheory.AutomorphicForms.GeometricLemma
import GroundTheory.AutomorphicForms.LeviStagesInduction
import GroundTheory.AutomorphicForms.LeviStagesExact
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Automorphic

namespace Parabolic

open Matrix Iwasawa GLnLocal Topology MeasureTheory Measure

universe u

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}

theorem sqrtModularLeviPar_of_mem_unipotentRadical {β γ δ : Fin n → ℕ} (q : leviPar F n β γ)
    (hq : (q : GL (Fin n) F) ∈ unipotentRadical F n δ) : sqrtModularLeviPar F n β γ q = 1 := by
  obtain ⟨e, he⟩ := exists_unipotentCompactG_of_isCompact (γ := δ)
    (isCompact_singleton (x := (q : GL (Fin n) F))) (by simpa using hq)
  have hk : rankTorus F n δ e * q * (rankTorus F n δ e)⁻¹ ∈ integralGL F n :=
    (mem_unipotentCompactG.1 (he rfl)).2
  have ht : rankTorus F n δ e ∈ leviPar F n β γ :=
    ⟨diagGL_mem_levi _, levi_le_blockUpper (diagGL_mem_levi _)⟩
  have hkL : rankTorus F n δ e * q * (rankTorus F n δ e)⁻¹ ∈ leviPar F n β γ :=
    (leviPar F n β γ).mul_mem ((leviPar F n β γ).mul_mem ht q.2) ((leviPar F n β γ).inv_mem ht)
  have h1 : sqrtModularLeviPar F n β γ ⟨_, hkL⟩ = 1 := by
    show ((NNReal.sqrt (modularCharacter (⟨_, hkL⟩ : leviPar F n β γ)) : ℝ) : ℂ) = 1
    rw [modularCharacter_leviPar_eq_one_of_mem_integralGL _ hk]
    simp
  have : q = ⟨_, ht⟩⁻¹ * ⟨_, hkL⟩ * ⟨_, ht⟩ := Subtype.ext (by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group)
  rw [this, map_mul, map_mul, h1, mul_one, ← map_mul, inv_mul_cancel, map_one]

section Stages

variable {β γ δ : Fin n → ℕ} {U : Type*} [AddCommGroup U] [Module ℂ U]
  {ρ : Representation ℂ (levi F n β) U}

theorem mk_mk_apply_of_mem_leviUnipotent (h : Refines β γ) (hγδ : Refines γ δ)
    (u : leviUnipotent F n β δ) (w : U) :
    Representation.Coinvariants.mk ((leviJacquetRep h ρ).comp (leviUnipotent F n γ δ).subtype)
        (Representation.Coinvariants.mk (ρ.comp (leviUnipotent F n β γ).subtype)
          (ρ (u : levi F n β) w)) =
      Representation.Coinvariants.mk _ (Representation.Coinvariants.mk _ w) := by
  have huN : ((u : levi F n β) : GL (Fin n) F) ∈ unipotentRadical F n δ :=
    Subgroup.mem_subgroupOf.1 u.2
  obtain ⟨huP, hu1⟩ := mem_unipotentRadical.1 huN
  set p : blockUpper F n γ := ⟨_, hγδ.blockUpper_le F huP⟩
  set m := leviProj F n γ p
  have hmN : ((m : levi F n γ) : GL (Fin n) F) ∈ unipotentRadical F n δ := by
    refine mem_unipotentRadical.2 ⟨fun i j hij => ?_, fun i j hij => ?_⟩
    · show ((m : levi F n γ) : GL (Fin n) F) i j = 0
      rw [leviProj_apply]
      split_ifs
      · exact huP hij
      · rfl
    · rw [leviProj_apply, if_pos (hγδ.eq_of_eq hij)]
      exact hu1 i j hij
  have hn' := leviProj_inv_mul_mem p
  set n' : levi F n β := (h.leviIncl F m)⁻¹ * (u : levi F n β)
  have hcoe : ((n' : levi F n β) : GL (Fin n) F) =
      (((leviIncl m)⁻¹ * p : blockUpper F n γ) : GL (Fin n) F) := by
    simp only [n', Subgroup.coe_mul, Subgroup.coe_inv, Refines.coe_leviIncl, leviIncl_coe]
    rfl
  have hn'N : ((n' : levi F n β) : GL (Fin n) F) ∈ unipotentRadical F n γ := by
    rw [hcoe]
    exact hn'
  have hu : (u : levi F n β) = h.leviIncl F m * n' := by simp [n']
  have hn'w : Representation.Coinvariants.mk (ρ.comp (leviUnipotent F n β γ).subtype) (ρ n' w) =
      Representation.Coinvariants.mk _ w :=
    Representation.Coinvariants.mk_self_apply (ρ.comp (leviUnipotent F n β γ).subtype)
      ⟨n', Subgroup.mem_subgroupOf.2 hn'N⟩ w
  have hsq : sqrtModularLeviPar F n β γ (h.leviToLeviPar F m) = 1 :=
    sqrtModularLeviPar_of_mem_unipotentRadical _ hmN
  have e1 : ρ (u : levi F n β) w = ρ (h.leviIncl F m) (ρ n' w) := by
    rw [hu, map_mul ρ, Module.End.mul_apply]
  have key : Representation.Coinvariants.mk (ρ.comp (leviUnipotent F n β γ).subtype)
      (ρ (u : levi F n β) w) =
      leviJacquetRep h ρ m (Representation.Coinvariants.mk _ w) :=
    calc _ = Representation.Coinvariants.mk (ρ.comp (leviUnipotent F n β γ).subtype)
          (ρ (h.leviIncl F m) (ρ n' w)) := congrArg _ e1
      _ = sqrtModularLeviPar F n β γ (h.leviToLeviPar F m) •
          leviJacquetRep h ρ m (Representation.Coinvariants.mk _ (ρ n' w)) :=
        mk_leviIncl_apply ρ h m _
      _ = leviJacquetRep h ρ m (Representation.Coinvariants.mk _ w) :=
        (congrArg (· • leviJacquetRep h ρ m (Representation.Coinvariants.mk _ (ρ n' w))) hsq).trans
          ((one_smul ℂ _).trans (congrArg (leviJacquetRep h ρ m) hn'w))
  exact (congrArg _ key).trans (Representation.Coinvariants.mk_self_apply
    ((leviJacquetRep h ρ).comp (leviUnipotent F n γ δ).subtype)
    ⟨m, Subgroup.mem_subgroupOf.2 hmN⟩ _)

theorem subsingleton_coinvariants_leviJacquetRep (h : Refines β γ) (hγδ : Refines γ δ)
    (hs : Subsingleton (LeviJacquetModule β δ ρ)) :
    Subsingleton (Representation.Coinvariants
      ((leviJacquetRep h ρ).comp (leviUnipotent F n γ δ).subtype)) := by
  set q' := Representation.Coinvariants.mk
    ((leviJacquetRep h ρ).comp (leviUnipotent F n γ δ).subtype)
  set q := Representation.Coinvariants.mk (ρ.comp (leviUnipotent F n β γ).subtype)
  have hker : Representation.Coinvariants.ker (ρ.comp (leviUnipotent F n β δ).subtype) ≤
      LinearMap.ker (q' ∘ₗ q) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨⟨u, w⟩, rfl⟩
    show q' (q (ρ (u : levi F n β) w - w)) = 0
    rw [map_sub q, map_sub q', sub_eq_zero]
    exact mk_mk_apply_of_mem_leviUnipotent h hγδ u w
  have hzero : ∀ x : U, q' (q x) = 0 := by
    intro x
    have hx : x ∈ Representation.Coinvariants.ker (ρ.comp (leviUnipotent F n β δ).subtype) :=
      (Representation.Coinvariants.mk_eq_zero _).1 (Subsingleton.elim _ _)
    exact hker hx
  refine ⟨fun a b => ?_⟩
  obtain ⟨a, rfl⟩ := Representation.Coinvariants.mk_surjective _ a
  obtain ⟨a, rfl⟩ := Representation.Coinvariants.mk_surjective _ a
  obtain ⟨b, rfl⟩ := Representation.Coinvariants.mk_surjective _ b
  obtain ⟨b, rfl⟩ := Representation.Coinvariants.mk_surjective _ b
  exact (hzero a).trans (hzero b).symm

end Stages

section Generation

variable {β γ : Fin n → ℕ}

theorem exists_leviPar_mul_integral (h : Refines β γ) (g : levi F n β) :
    ∃ q : leviPar F n β γ, ∃ k : levi F n β, (k : GL (Fin n) F) ∈ integralGL F n ∧
      (g : GL (Fin n) F) = q * k := by
  obtain ⟨p, hp, k, hk, hg⟩ := exists_blockUpper_mul_integralGL' (β := γ) (g : GL (Fin n) F)
  have hpβ : p ∈ blockUpper F n β := h.blockUpper_le F hp
  have hkβ : k ∈ blockUpper F n β := by
    have : k = p⁻¹ * g := by rw [hg]; group
    rw [this]
    exact (blockUpper F n β).mul_mem ((blockUpper F n β).inv_mem hpβ) (levi_le_blockUpper g.2)
  set pβ : blockUpper F n β := ⟨p, hpβ⟩
  set kβ : blockUpper F n β := ⟨k, hkβ⟩
  have hqγ : ((leviProj F n β pβ : levi F n β) : GL (Fin n) F) ∈ blockUpper F n γ := by
    intro i j hij
    show ((leviProj F n β pβ : levi F n β) : GL (Fin n) F) i j = 0
    rw [leviProj_apply]
    split_ifs
    · exact hp hij
    · rfl
  refine ⟨⟨_, (leviProj F n β pβ).2, hqγ⟩, leviProj F n β kβ, leviProj_mem_integralGL hk, ?_⟩
  have hgβ : (⟨g, levi_le_blockUpper g.2⟩ : blockUpper F n β) = pβ * kβ := Subtype.ext hg
  have := congrArg (fun x => ((leviProj F n β x : levi F n β) : GL (Fin n) F)) hgβ
  simp only [map_mul, Subgroup.coe_mul, leviProj_of_mem_levi g.2] at this
  exact this

variable {U : Type*} [AddCommGroup U] [Module ℂ U] {ρ : Representation ℂ (levi F n β) U}

theorem exists_finset_span_leviJacquetRep (h : Refines β γ) (hρ : IsSmooth ρ) {v : U}
    (hv : Submodule.span ℂ (Set.range fun g : levi F n β => ρ g v) = ⊤) :
    ∃ S : Finset (LeviJacquetModule β γ ρ),
      Submodule.span ℂ {x | ∃ m, ∃ s ∈ S, x = leviJacquetRep h ρ m s} = ⊤ := by
  classical
  obtain ⟨m₀, hm₀⟩ := exists_congruence_fixed hρ v
  set K₀ : Subgroup (levi F n β) := (integralGL F n).subgroupOf (levi F n β)
  set Km : Subgroup (levi F n β) := (congruenceSubgroup F n m₀).subgroupOf (levi F n β)
  have hvK : v ∈ fixedVectors ρ Km := fun k hk => hm₀ k (Subgroup.mem_subgroupOf.1 hk)
  have : CompactSpace K₀ :=
    isCompact_iff_compactSpace.1 (isCompact_subgroupOf_levi (isCompact_integralGL F n))
  have hQ : Finite (K₀ ⧸ Km.subgroupOf K₀) := by
    refine Subgroup.quotient_finite_of_isOpen _ ?_
    rw [Subgroup.coe_subgroupOf]
    exact (isOpen_subgroupOf_levi (isOpen_congruenceSubgroup F n m₀)).preimage
      continuous_subtype_val
  have := Fintype.ofFinite (K₀ ⧸ Km.subgroupOf K₀)
  let R : Finset (levi F n β) :=
    Finset.univ.image fun q : K₀ ⧸ Km.subgroupOf K₀ => ((Quotient.out q : K₀) : levi F n β)
  have hR : ∀ k ∈ K₀, ∃ r ∈ R, ρ k v = ρ r v := by
    intro k hk
    refine ⟨_, Finset.mem_image_of_mem _ (Finset.mem_univ (QuotientGroup.mk (⟨k, hk⟩ : K₀))), ?_⟩
    exact act_eq_of_mk_eq ρ hvK (a := ⟨k, hk⟩)
      (b := Quotient.out (QuotientGroup.mk (⟨k, hk⟩ : K₀) : K₀ ⧸ Km.subgroupOf K₀))
      (QuotientGroup.out_eq' _).symm
  set q := Representation.Coinvariants.mk (ρ.comp (leviUnipotent F n β γ).subtype)
  refine ⟨R.image fun r => q (ρ r v), ?_⟩
  set T := Submodule.span ℂ {x | ∃ m, ∃ s ∈ R.image fun r => q (ρ r v),
    x = leviJacquetRep h ρ m s}
  have hclaim : ∀ g : levi F n β, q (ρ g v) ∈ T := by
    intro g
    obtain ⟨qq, k, hk, hg⟩ := exists_leviPar_mul_integral h g
    obtain ⟨r, hr, hrv⟩ := hR k (Subgroup.mem_subgroupOf.2 hk)
    set pγ : blockUpper F n γ := ⟨qq, qq.2.2⟩
    set m := leviProj F n γ pγ
    have hn : ((pγ * (leviIncl m)⁻¹ : blockUpper F n γ) : GL (Fin n) F) ∈
        unipotentRadical F n γ := by
      rw [mem_unipotentRadical_iff_leviProj, map_mul, map_inv, leviProj_leviIncl, mul_inv_cancel]
    have hnβ : ((pγ * (leviIncl m)⁻¹ : blockUpper F n γ) : GL (Fin n) F) ∈ levi F n β := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, leviIncl_coe]
      exact (levi F n β).mul_mem qq.2.1 ((levi F n β).inv_mem (h.levi_le F m.2))
    set n' : levi F n β := ⟨_, hnβ⟩
    have hgeq : g = n' * h.leviIncl F m * k := by
      apply Subtype.ext
      simp only [n', Subgroup.coe_mul, Subgroup.coe_inv, leviIncl_coe, Refines.coe_leviIncl, hg]
      show (qq : GL (Fin n) F) * k = (qq : GL (Fin n) F) * (m : GL (Fin n) F)⁻¹ * m * k
      group
    have hn'v : ∀ x, q (ρ n' x) = q x := fun x =>
      Representation.Coinvariants.mk_self_apply (ρ.comp (leviUnipotent F n β γ).subtype)
        ⟨n', Subgroup.mem_subgroupOf.2 hn⟩ x
    have e1 : ρ g v = ρ n' (ρ (h.leviIncl F m) (ρ r v)) := by
      rw [hgeq, map_mul ρ, map_mul ρ, Module.End.mul_apply, Module.End.mul_apply, hrv]
    have e2 : q (ρ g v) = sqrtModularLeviPar F n β γ (h.leviToLeviPar F m) •
        leviJacquetRep h ρ m (q (ρ r v)) :=
      (congrArg q e1).trans ((hn'v _).trans (mk_leviIncl_apply ρ h m _))
    rw [e2]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, q (ρ r v),
      Finset.mem_image_of_mem _ hr, rfl⟩)
  rw [eq_top_iff]
  intro x _
  obtain ⟨y, rfl⟩ := Representation.Coinvariants.mk_surjective _ x
  have hy : y ∈ Submodule.span ℂ (Set.range fun g : levi F n β => ρ g v) := by
    rw [hv]
    exact Submodule.mem_top
  have hmap : Submodule.map q (Submodule.span ℂ (Set.range fun g : levi F n β => ρ g v)) ≤ T := by
    rw [Submodule.map_span]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨_, ⟨g, rfl⟩, rfl⟩
    exact hclaim g
  exact hmap ⟨y, hy, rfl⟩

end Generation

section Embedding

variable {β : Fin n → ℕ}

theorem Refines.trans {β γ δ : Fin n → ℕ} (h₁ : Refines β γ) (h₂ : Refines γ δ) :
    Refines β δ :=
  fun i j h => h₂ i j (h₁ i j h)

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in

theorem eq_one_of_mem_leviUnipotent_self (u : leviUnipotent F n β β) :
    ((u : levi F n β) : GL (Fin n) F) = 1 := by
  have hu := mem_unipotentRadical.1 (Subgroup.mem_subgroupOf.1 u.2)
  have hl := mem_levi.1 (u : levi F n β).2
  apply Units.ext
  ext i j
  by_cases hij : β i = β j
  · exact hu.2 i j hij
  · rw [hl i j hij, Units.val_one, one_apply_ne fun e => hij (by rw [e])]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in

theorem nontrivial_leviJacquetModule_self {U : Type*} [AddCommGroup U] [Module ℂ U]
    [Nontrivial U] (ρ : Representation ℂ (levi F n β) U) :
    Nontrivial (LeviJacquetModule β β ρ) := by
  obtain ⟨v, hv⟩ := exists_ne (0 : U)
  refine ⟨⟨Representation.Coinvariants.mk _ v, 0, fun h => hv ?_⟩⟩
  have hmem := (Representation.Coinvariants.mk_eq_zero _).1 h
  have hle : Representation.Coinvariants.ker (ρ.comp (leviUnipotent F n β β).subtype) ≤ ⊥ := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨⟨u, x⟩, rfl⟩
    have hu : (u : levi F n β) = 1 := Subtype.ext (eq_one_of_mem_leviUnipotent_self u)
    simp [hu]
  exact (Submodule.mem_bot ℂ).1 (hle hmem)

set_option maxHeartbeats 1000000 in

theorem exists_embedding_leviParabolicInd {U : Type u} [AddCommGroup U] [Module ℂ U]
    {ρ : Representation ℂ (levi F n β) U} [ρ.IsIrreducible] (hρ : IsSmooth ρ) :
    ∃ (γ : Fin n → ℕ) (_ : Refines β γ) (W : Type u) (_ : AddCommGroup W) (_ : Module ℂ W)
      (τ : Representation ℂ (levi F n γ) W), τ.IsIrreducible ∧ IsSmooth τ ∧ IsCuspidal τ ∧
        ∃ Φ : Representation.IntertwiningMap ρ (leviParabolicInd F n β γ τ), Function.Injective Φ := by
  classical
  obtain ⟨v, hv0⟩ := exists_ne_zero_of_isIrreducible (ρ := ρ)
  have : Nontrivial U := ⟨⟨v, 0, hv0⟩⟩
  have hspan := span_range_eq_top_of_isIrreducible (ρ := ρ) hv0

  let P : ℕ → Prop := fun k => ∃ γ : Fin n → ℕ, Refines β γ ∧ (Finset.univ.image γ).card = k ∧
    Nontrivial (LeviJacquetModule β γ ρ)
  have hbound : ∀ γ : Fin n → ℕ, (Finset.univ.image γ).card ≤ n := fun γ =>
    (Finset.card_image_le).trans (by simp)
  have hP0 : P (Finset.univ.image β).card :=
    ⟨β, Refines.refl β, rfl, nontrivial_leviJacquetModule_self ρ⟩
  obtain ⟨γ, hγ, hγcard, hγnt⟩ := Nat.findGreatest_spec (hbound _) hP0
  have hfinest : ∀ δ : Fin n → ℕ, (∃ i j, γ i = γ j ∧ δ i ≠ δ j) →
      Subsingleton (LeviJacquetModule β (refineFun γ δ) ρ) := by
    intro δ hδ
    have hlt := card_image_lt_refineFun hδ
    rw [hγcard] at hlt
    have := Nat.findGreatest_is_greatest hlt (hbound _)
    rw [← not_nontrivial_iff_subsingleton]
    exact fun hnt => this ⟨_, hγ.trans (refines_refineFun γ δ), rfl, hnt⟩

  obtain ⟨S, hS⟩ := exists_finset_span_leviJacquetRep hγ hρ hspan
  have : Nontrivial (LeviJacquetModule β γ ρ) := hγnt
  obtain ⟨Y, hY, hirr⟩ := exists_irreducible_quotient (τ := leviJacquetRep hγ ρ) S hS
  let τ := Representation.quotient (leviJacquetRep hγ ρ) Y hY
  have hτs : IsSmooth τ := isSmooth_quotient (isSmooth_leviJacquetRep hγ hρ) Y hY
  have hτc : IsCuspidal τ := by
    intro δ hδ
    have h1 := subsingleton_coinvariants_leviJacquetRep hγ (refines_refineFun γ δ) (hfinest δ hδ)
    rw [← leviUnipotent_refineFun] at h1
    exact subsingleton_coinvariants_of_surjective (quotientMk Y hY) (quotientMk_surjective Y hY) h1
  refine ⟨γ, hγ, _, inferInstance, inferInstance, τ, hirr, hτs, hτc, ?_⟩

  set Φ := (leviFrobenius ρ τ hγ hρ).symm (quotientMk Y hY)
  refine ⟨Φ, ?_⟩
  rcases Representation.IsIrreducible.injective_or_eq_zero Φ with hΦ | hΦ
  · exact hΦ
  · exfalso
    have h0 : quotientMk Y hY = 0 := by
      rw [← (leviFrobenius ρ τ hγ hρ).apply_symm_apply (quotientMk Y hY)]
      show leviFrobenius ρ τ hγ hρ Φ = 0
      rw [hΦ, map_zero]
    obtain ⟨w, hw⟩ := exists_ne_zero_of_isIrreducible (ρ := τ)
    obtain ⟨x, rfl⟩ := quotientMk_surjective Y hY w
    exact hw (by rw [h0]; rfl)

end Embedding

end Parabolic

end GroundTheory.Automorphic
