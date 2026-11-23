import ReciprocityTheory.GroupCohomology.CupConnRightStatement
import ReciprocityTheory.GroupCohomology.DEqZeroOfMemB
import ReciprocityTheory.GroupCohomology.ResNormalHolds
import ReciprocityTheory.GroupCohomology.InfRes

namespace ReciprocityTheory.Coh

open ReciprocityTheory.Gal Topology
open scoped Pointwise

universe u

namespace FiniteLevelCohomology

theorem exists_nhds_right_const {K X : Type*} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
    [CompactSpace K] [TopologicalSpace X] [DiscreteTopology X] (f : K → X) (hf : Continuous f) :
    ∃ V ∈ 𝓝 (1 : K), ∀ g v, v ∈ V → f (g * v) = f g := by
  have hfin : (Set.range f).Finite := (isCompact_range hf).finite_of_discrete
  have hV : ∀ x ∈ Set.range f, ∃ V ∈ 𝓝 (1 : K), f ⁻¹' {x} * V ⊆ f ⁻¹' {x} := by
    intro x _
    have hc : IsClosed (f ⁻¹' {x}) := (isClosed_discrete {x}).preimage hf
    exact compact_open_separated_mul_right hc.isCompact ((isOpen_discrete {x}).preimage hf) subset_rfl
  choose! V hV1 hV2 using hV
  refine ⟨⋂ x ∈ hfin.toFinset, V x, ?_, ?_⟩
  · exact (Filter.biInter_finset_mem _).2 fun x hx => hV1 x (hfin.mem_toFinset.1 hx)
  · intro g v hv
    have hx : f g ∈ Set.range f := ⟨g, rfl⟩
    have hvx : v ∈ V (f g) := Set.mem_iInter₂.1 hv (f g) (hfin.mem_toFinset.2 hx)
    exact hV2 (f g) hx (Set.mul_mem_mul (show f g ∈ ({f g} : Set X) from rfl) hvx)

variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

theorem stab_mem_nhds (M : TRep R G) [DiscreteTopology M.V] (m : M.V) :
    {a : G | M.rho a m = m} ∈ 𝓝 (1 : G) := by
  have hc : Continuous fun a : G => M.rho a m :=
    M.cont.comp (Continuous.prodMk continuous_id continuous_const)
  exact (hc.isOpen_preimage {m} (isOpen_discrete _)).mem_nhds (by simp)

theorem exists_open_normal [CompactSpace G] [TotallyDisconnectedSpace G] (M : TRep R G)
    [DiscreteTopology M.V] {n : ℕ} (c : (Fin n → G) → M.V) (hc : Continuous c) :
    ∃ N : Subgroup G, N.Normal ∧ IsOpen (N : Set G) ∧
      (∀ (g v : Fin n → G), (∀ i, v i ∈ N) → c (g * v) = c g) ∧
      ∀ g, ∀ a ∈ N, M.rho a (c g) = c g := by
  classical
  obtain ⟨V0, hV0, hV0c⟩ := exists_nhds_right_const c hc
  rw [nhds_pi, Filter.mem_pi] at hV0
  obtain ⟨I, -, t, ht, htV⟩ := hV0
  have hU : (⋂ i, t i) ∈ 𝓝 (1 : G) := Filter.iInter_mem.mpr fun i => ht i
  have hfin : (Set.range c).Finite := (isCompact_range hc).finite_of_discrete
  have hS : (⋂ m ∈ Set.range c, {a : G | M.rho a m = m}) ∈ 𝓝 (1 : G) :=
    (Filter.biInter_mem hfin).mpr fun m _ => stab_mem_nhds M m
  have hW : (⋂ i, t i) ∩ (⋂ m ∈ Set.range c, {a : G | M.rho a m = m}) ∈ 𝓝 (1 : G) :=
    Filter.inter_mem hU hS
  obtain ⟨H, hH⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one isOpen_interior
    (mem_interior_iff_mem_nhds.mpr hW)
  refine ⟨H.toOpenSubgroup.toSubgroup, H.isNormal', H.toOpenSubgroup.isOpen', fun g v hv => ?_,
    fun g a ha => ?_⟩
  · apply hV0c g v
    apply htV
    intro i _
    have hvi := interior_subset (hH (hv i))
    exact Set.mem_iInter.mp hvi.1 i
  · have hai := interior_subset (hH ha)
    exact Set.mem_iInter₂.mp hai.2 (c g) ⟨g, rfl⟩

end FiniteLevelCohomology

namespace FiniteLevelCohomology

variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

theorem exists_level [CompactSpace G] [TotallyDisconnectedSpace G] (M : TRep R G)
    [DiscreteTopology M.V] (n : ℕ) (x : M.H n) :
    ∃ (N : Subgroup G) (_ : N.Normal), IsOpen (N : Set G) ∧ ∀ (Q : TRep R (G ⧸ N)) (P : Pair Q M),
      IsInvRep M N Q P → x ∈ LinearMap.range (P.hom.H n) := by
  obtain ⟨⟨c, hc⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have hc' : M.coch.d n c = 0 := hc
  obtain ⟨N, hN, hNo, hconst, hfix⟩ := exists_open_normal M c.1 c.2
  refine ⟨N, hN, hNo, fun Q P hP => ?_⟩
  have := QuotientGroup.discreteTopology hNo
  obtain ⟨hφ, hemb, hrange⟩ := hP
  have hval : ∀ q : Fin n → G ⧸ N, ∃ y, P.u y = c.1 (fun i => (q i).out) :=
    fun q => (hrange _).2 fun a ha => hfix _ a ha
  choose f' hf' using hval
  have hout : ∀ g : Fin n → G,
      c.1 (fun i => (QuotientGroup.mk (s := N) (g i) : G ⧸ N).out) = c.1 g := by
    intro g
    choose v hv using fun i => QuotientGroup.mk_out_eq_mul N (g i)
    have e : (fun i => (QuotientGroup.mk (s := N) (g i) : G ⧸ N).out) = g * fun i => (v i : G) :=
      funext fun i => hv i
    rw [e]
    exact hconst g _ fun i => (v i).2
  have hPf : ∀ g : Fin n → G, P.u (f' fun i => P.φ (g i)) = c.1 g := by
    intro g
    rw [hφ]
    exact (hf' _).trans (hout g)
  let F : Q.coch.X n := ⟨f', continuous_of_discreteTopology⟩
  have h2 : P.hom.f n F = c := Subtype.ext (funext hPf)
  have hF : Q.coch.d n F = 0 := by
    have h1 : P.hom.f (n + 1) (Q.coch.d n F) = M.coch.d n (P.hom.f n F) := P.hom.comm n F
    rw [h2, hc'] at h1
    apply Subtype.ext
    funext q
    have h3 := congrFun (congrArg Subtype.val h1) (fun i => (q i).out)
    have h4 : (fun i => P.φ ((q i).out)) = q := by
      funext i
      rw [hφ]
      exact QuotientGroup.out_eq' (q i)
    change P.u ((Q.coch.d n F).1 fun i => P.φ ((q i).out)) = 0 at h3
    rw [h4] at h3
    exact hemb.injective (h3.trans (map_zero _).symm)
  refine ⟨Submodule.Quotient.mk ⟨F, hF⟩, ?_⟩
  rw [Cx.Hom.H, Submodule.mapQ_apply]
  congr 1
  exact Subtype.ext h2

theorem sum_neg_one_pow (k : ℕ) :
    (1 : R) + ∑ j : Fin (k + 1), (-1 : R) ^ ((j : ℕ) + 1) = if Even k then 0 else 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Fin.sum_univ_castSucc, ← add_assoc]
    simp only [Fin.coe_castSucc, Fin.val_last]
    rw [ih]
    rcases Nat.even_or_odd k with hk | hk
    · have h1 : ¬ Even (k + 1) := Nat.not_even_iff_odd.2 (Even.add_one hk)
      rw [if_pos hk, if_neg h1, pow_succ, pow_succ, Even.neg_one_pow hk]
      ring
    · have h1 : Even (k + 1) := Odd.add_one hk
      rw [if_neg (Nat.not_even_iff_odd.2 hk), if_pos h1, pow_succ, pow_succ, Odd.neg_one_pow hk]
      ring

theorem dn_subsingleton {K : Type u} [Group K] [TopologicalSpace K] [Subsingleton K]
    (M : TRep R K) (k : ℕ) (f : (Fin k → K) → M.V) (g : Fin (k + 1) → K) :
    dn M.rho k f g = (if Even k then (0 : R) else 1) • f (fun _ => 1) := by
  have e : ∀ x : Fin k → K, f x = f (fun _ => 1) := fun x => congrArg f (Subsingleton.elim _ _)
  have hs : (∑ j : Fin (k + 1), (-1 : R) ^ ((j : ℕ) + 1) • f (Fin.contractNth j (· * ·) g)) =
      ∑ j : Fin (k + 1), (-1 : R) ^ ((j : ℕ) + 1) • f (fun _ => 1) :=
    Finset.sum_congr rfl fun j _ => by rw [e (Fin.contractNth j (· * ·) g)]
  rw [dn_apply, Subsingleton.elim (g 0) 1, map_one, e (fun i => g i.succ), hs, ← Finset.sum_smul,
    ← sum_neg_one_pow k, add_smul, one_smul]
  rfl

theorem H_succ_trivial {K : Type u} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
    [Subsingleton K] (M : TRep R K) (m : ℕ) (z : M.H (m + 1)) : z = 0 := by
  classical
  obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  rw [Submodule.Quotient.mk_eq_zero]
  have hwf : ∀ g, dn M.rho (m + 1) w.1.1 g = 0 := fun g => by
    have h := congrArg (fun x : M.coch.X (m + 1 + 1) => x.1 g) w.2
    exact h
  show (w : M.coch.X (m + 1)) ∈ LinearMap.range (M.coch.d m)
  rcases Nat.even_or_odd m with hm | hm
  · have h1 : w.1.1 (fun _ => 1) = 0 := by
      have h := hwf (fun _ => 1)
      rwa [dn_subsingleton, if_neg (Nat.even_add_one.not.mpr (not_not.mpr hm)), one_smul] at h
    refine ⟨0, ?_⟩
    rw [map_zero]
    symm
    apply Subtype.ext
    funext g
    show w.1.1 g = 0
    rw [Subsingleton.elim g (fun _ => 1)]
    exact h1
  · refine ⟨⟨fun _ => w.1.1 (fun _ => 1), ?_⟩, ?_⟩
    · exact continuous_const
    · apply Subtype.ext
      funext g
      show dn M.rho m (fun _ => w.1.1 (fun _ => 1)) g = w.1.1 g
      rw [dn_subsingleton, if_neg (Nat.not_even_iff_odd.mpr hm), one_smul]
      rw [Subsingleton.elim g (fun _ => 1)]

theorem torsion_finite {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [DiscreteTopology H] [Finite H] (Q : TRep R H) (m : ℕ) (y : Q.H (m + 1)) :
    Nat.card H • y = 0 := by
  have : Subsingleton (⊥ : Subgroup H) :=
    ⟨fun a b => Subtype.ext ((Subgroup.mem_bot.1 a.2).trans (Subgroup.mem_bot.1 b.2).symm)⟩
  obtain ⟨cor, -, hcor⟩ := cor_holds R H Q ⊥ (isOpen_discrete _)
  have h := hcor (m + 1) y
  rw [H_succ_trivial _ m ((Pair.res Q (⊥ : Subgroup H).subtype continuous_subtype_val).hom.H (m + 1) y),
    map_zero, Subgroup.index_bot] at h
  exact h.symm

end FiniteLevelCohomology

theorem finiteLevel_holds : FiniteLevelStatement.{u} := by
  intro R _ G _ _ _ _ _ _ M _ n x
  obtain ⟨N, hN, hNo, hlev⟩ := FiniteLevelCohomology.exists_level M n x
  refine ⟨⟨N, hN, hNo, hlev⟩, fun hn => ?_⟩
  obtain ⟨y, hy⟩ := hlev _ _ (InflationRestrictionInvariants.invariants_isInvRep M N)
  haveI : DiscreteTopology (G ⧸ N) := QuotientGroup.discreteTopology hNo
  haveI : Finite (G ⧸ N) := Subgroup.quotient_finite_of_isOpen N hNo
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  refine ⟨Nat.card (G ⧸ N), Nat.card_pos, ?_⟩
  rw [← hy, ← map_nsmul, FiniteLevelCohomology.torsion_finite _ m y, map_zero]

end ReciprocityTheory.Coh
