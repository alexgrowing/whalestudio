import Development.AbelianVarietyTheory.Proofs.DivisorProofs.T2SpaceFiniteAdeleRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwOrbEqFinsumTwTerm
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CptPartRestr

open Set
open scoped Pointwise

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]

def cptSub (T : Subgroup G) (hT : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a) : Subgroup G where
  carrier := {t | t ∈ T ∧ IsCompact (closure (Subgroup.zpowers t : Set G))}
  one_mem' := by
    refine ⟨T.one_mem, ?_⟩
    rw [Subgroup.zpowers_one_eq_bot, Subgroup.coe_bot, closure_singleton]
    exact isCompact_singleton
  mul_mem' := by
    rintro a b ⟨haT, ha⟩ ⟨hbT, hb⟩
    refine ⟨T.mul_mem haT hbT, ?_⟩
    have hc : Commute a b := hT a haT b hbT
    have hsub : closure (Subgroup.zpowers (a * b) : Set G) ⊆
        closure (Subgroup.zpowers a : Set G) * closure (Subgroup.zpowers b : Set G) := by
      refine closure_minimal ?_ (ha.mul hb).isClosed
      rintro _ ⟨n, rfl⟩
      simp only [hc.mul_zpow]
      exact Set.mul_mem_mul (subset_closure (Subgroup.zpow_mem_zpowers a n))
        (subset_closure (Subgroup.zpow_mem_zpowers b n))
    exact (ha.mul hb).of_isClosed_subset isClosed_closure hsub
  inv_mem' := by
    rintro a ⟨haT, ha⟩
    refine ⟨T.inv_mem haT, ?_⟩
    rw [Subgroup.zpowers_inv]
    exact ha

theorem mem_cptPart_iff (T : Subgroup G) (hT : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a) (x : G) :
    x ∈ cptPart T ↔ x ∈ T ∧ IsCompact (closure (Subgroup.zpowers x : Set G)) := by
  have : cptPart T = cptSub T hT := Subgroup.closure_eq (cptSub T hT)
  rw [this]
  rfl

section Restr

variable {X V : Type} {Y : V → Type} [Group X] [TopologicalSpace X] [IsTopologicalGroup X] [T2Space X]
  [∀ v, Group (Y v)] [∀ v, TopologicalSpace (Y v)] [∀ v, IsTopologicalGroup (Y v)] [∀ v, T2Space (Y v)]
  {pf : ∀ v, X →* Y v} {K : ∀ v, Subgroup (Y v)}

theorem isClosed_setOf_forall_mem (hX : GlobalTheory.RestrMeas.IsRestrGroup (GlobalTheory.RestrMeas.noArch X) pf K)
    (C : ∀ v, Set (Y v)) (hC : ∀ v, IsCompact (C v)) : IsClosed {z : X | ∀ v, pf v z ∈ C v} := by
  simp only [Set.setOf_forall]
  exact isClosed_iInter fun v => (hC v).isClosed.preimage (hX.continuous_pf v)

theorem isCompact_setOf_forall_mem (hX : GlobalTheory.RestrMeas.IsRestrGroup (GlobalTheory.RestrMeas.noArch X) pf K)
    (S : Finset V) : ∀ C : ∀ v, Set (Y v), (∀ v, IsCompact (C v)) → (∀ v ∉ S, C v ⊆ K v) →
      IsCompact {z : X | ∀ v, pf v z ∈ C v} := by
  induction S using Finset.induction_on with
  | empty =>
    intro C hC hCK
    have hKg := hX.isCompact_level (fun e => e.elim) (fun e => e.elim)
    exact hKg.of_isClosed_subset (isClosed_setOf_forall_mem hX C hC)
      fun z hz => ⟨fun e => e.elim, fun v => hCK v (Finset.notMem_empty v) (hz v)⟩
  | @insert v₀ S hv₀ ih =>
    intro C hC hCK
    obtain ⟨t, hcov⟩ := (hC v₀).elim_finite_subcover (fun c : C v₀ => (c : Y v₀) • (K v₀ : Set (Y v₀)))
      (fun c => (hX.isOpen_K v₀).smul _)
      (fun y hy => Set.mem_iUnion.2 ⟨⟨y, hy⟩, ⟨1, (K v₀).one_mem, by simp⟩⟩)
    set C' : ∀ v, Set (Y v) := Function.update C v₀ (K v₀ : Set (Y v₀)) with hC'def
    have hC' : ∀ v, IsCompact (C' v) := by
      intro v
      by_cases h : v = v₀
      · subst h; simp only [hC'def, Function.update_self]; exact hX.isCompact_K v
      · simp only [hC'def, Function.update_of_ne h]; exact hC v
    have hC'K : ∀ v ∉ S, C' v ⊆ K v := by
      intro v hv
      by_cases h : v = v₀
      · subst h; simp only [hC'def, Function.update_self]; exact subset_rfl
      · simp only [hC'def, Function.update_of_ne h]
        exact hCK v (by simp [h, hv])
    have hM' := ih C' hC' hC'K
    have hl : ∀ c : Y v₀, ∃ x : X, ∀ v, pf v x = Pi.mulSingle v₀ c v := by
      intro c
      have hev : ∀ᶠ v in cofinite, (Pi.mulSingle v₀ c : ∀ v, Y v) v ∈ K v := by
        rw [Filter.eventually_cofinite]
        refine (Set.finite_singleton v₀).subset fun v hv => ?_
        by_contra h
        exact hv (by rw [Pi.mulSingle_eq_of_ne h]; exact (K v).one_mem)
      obtain ⟨x, -, hx⟩ := hX.exists_eq (fun e => e.elim) _ hev
      exact ⟨x, hx⟩
    choose xc hxc using hl
    have hU : IsCompact (⋃ i ∈ t, xc (i : Y v₀) • {z : X | ∀ v, pf v z ∈ C' v}) :=
      t.isCompact_biUnion fun i _ => hM'.smul _
    refine hU.of_isClosed_subset (isClosed_setOf_forall_mem hX C hC) fun z hz => ?_
    obtain ⟨i, hi, hzi⟩ := Set.mem_iUnion₂.1 (hcov (hz v₀))
    obtain ⟨k, hk, hik⟩ := Set.mem_smul_set.1 hzi
    refine Set.mem_iUnion₂.2 ⟨i, hi, Set.mem_smul_set_iff_inv_smul_mem.2 fun v => ?_⟩
    rw [smul_eq_mul, map_mul, map_inv, hxc]
    by_cases h : v = v₀
    · subst h
      simp only [Pi.mulSingle_eq_same, hC'def, Function.update_self]
      rw [← hik, smul_eq_mul, inv_mul_cancel_left]
      exact hk
    · simp only [Pi.mulSingle_eq_of_ne h, inv_one, one_mul, hC'def, Function.update_of_ne h]
      exact hz v

theorem isCompact_closure_zpowers_iff (hX : GlobalTheory.RestrMeas.IsRestrGroup (GlobalTheory.RestrMeas.noArch X) pf K) (x : X) :
    IsCompact (closure (Subgroup.zpowers x : Set X)) ↔
      ∀ v, IsCompact (closure (Subgroup.zpowers (pf v x) : Set (Y v))) := by
  constructor
  · intro h v
    have hi := h.image (hX.continuous_pf v)
    refine hi.of_isClosed_subset isClosed_closure (closure_minimal ?_ hi.isClosed)
    rintro _ ⟨n, rfl⟩
    exact ⟨x ^ n, subset_closure (Subgroup.zpow_mem_zpowers x n), map_zpow _ _ _⟩
  · intro h
    have hfin := Filter.eventually_cofinite.1 (hX.eventually_mem x)
    have hCK : ∀ v ∉ hfin.toFinset, closure (Subgroup.zpowers (pf v x) : Set (Y v)) ⊆ K v := by
      intro v hv
      rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_not] at hv
      exact closure_minimal (fun y hy => Subgroup.zpowers_le.2 hv hy) (hX.isCompact_K v).isClosed
    have hM := isCompact_setOf_forall_mem hX hfin.toFinset _ h hCK
    refine hM.of_isClosed_subset isClosed_closure
      (closure_minimal ?_ (isClosed_setOf_forall_mem hX _ h))
    rintro _ ⟨n, rfl⟩ v
    rw [map_zpow]
    exact subset_closure (Subgroup.zpow_mem_zpowers _ n)

end Restr

theorem mem_cptPart_iff_forall : ∀ {X V : Type} {Y : V → Type} [Group X] [TopologicalSpace X] [IsTopologicalGroup X] [T2Space X] [∀ v, Group (Y v)] [∀ v, TopologicalSpace (Y v)] [∀ v, IsTopologicalGroup (Y v)] [∀ v, T2Space (Y v)] (pf : ∀ v, X →* Y v) (K : ∀ v, Subgroup (Y v)), GlobalTheory.RestrMeas.IsRestrGroup (GlobalTheory.RestrMeas.noArch X) pf K → ∀ (T : Subgroup X) (Tv : ∀ v, Subgroup (Y v)), (∀ x, x ∈ T ↔ ∀ v, pf v x ∈ Tv v) → (∀ v, ∀ a ∈ Tv v, ∀ b ∈ Tv v, a * b = b * a) → ∀ x, x ∈ cptPart T ↔ ∀ v, pf v x ∈ cptPart (Tv v) := by
  intro X V Y _ _ _ _ _ _ _ _ pf K hX T Tv hT hTv x
  have hTc : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a := fun a ha b hb =>
    hX.ext _ _ (fun e => e.elim) fun v => by
      rw [map_mul, map_mul]; exact hTv v _ ((hT a).1 ha v) _ ((hT b).1 hb v)
  rw [mem_cptPart_iff T hTc, hT, isCompact_closure_zpowers_iff hX]
  simp only [mem_cptPart_iff _ (hTv _)]
  exact ⟨fun h v => ⟨h.1 v, h.2 v⟩, fun h => ⟨fun v => (h v).1, fun v => (h v).2⟩⟩

end GlobalTheory.CptPartRestr
