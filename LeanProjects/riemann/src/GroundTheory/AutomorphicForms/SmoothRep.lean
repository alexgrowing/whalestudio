import Mathlib
import GroundTheory.AutomorphicForms.LocallyProfinite
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.StabilizerOf

noncomputable section

namespace GroundTheory.Automorphic

open Set Filter Topology

section General

variable {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module ℂ V]
  (ρ : Representation ℂ G V)

noncomputable def stabilizerOf (v : V) : Subgroup G :=
  @_root_.UpperTheory.Reformulated.B.StabilizerOf.stabilizerOf G _ V _ _ ρ v

variable {ρ} in
theorem mem_stabilizerOf {v : V} {g : G} : g ∈ stabilizerOf ρ v ↔ ρ g v = v := Iff.rfl

def fixedVectors (H : Subgroup G) : Submodule ℂ V where
  carrier := {v | ∀ h ∈ H, ρ h v = v}
  add_mem' {v w} hv hw h hh := by simp [hv h hh, hw h hh]
  zero_mem' h _ := map_zero _
  smul_mem' c v hv h hh := by simp [hv h hh]

variable {ρ} in
theorem mem_fixedVectors {H : Subgroup G} {v : V} :
    v ∈ fixedVectors ρ H ↔ ∀ h ∈ H, ρ h v = v := Iff.rfl

variable {ρ} in
theorem mem_fixedVectors_iff_le {H : Subgroup G} {v : V} :
    v ∈ fixedVectors ρ H ↔ H ≤ stabilizerOf ρ v := Iff.rfl

theorem fixedVectors_eq_invariants (H : Subgroup G) :
    fixedVectors ρ H = Representation.invariants (ρ.comp H.subtype) := by
  ext v
  simp [mem_fixedVectors, Representation.mem_invariants]

theorem fixedVectors_antitone {H₁ H₂ : Subgroup G} (h : H₁ ≤ H₂) :
    fixedVectors ρ H₂ ≤ fixedVectors ρ H₁ :=
  fun _ hv g hg => hv g (h hg)

abbrev coinvariantsKer (H : Subgroup G) : Submodule ℂ V :=
  Representation.Coinvariants.ker (ρ.comp H.subtype)

variable {ρ} in
theorem sub_mem_coinvariantsKer {H : Subgroup G} {h : G} (hh : h ∈ H) (v : V) :
    ρ h v - v ∈ coinvariantsKer ρ H :=
  Representation.Coinvariants.sub_mem_ker (ρ := ρ.comp H.subtype) ⟨h, hh⟩ v

theorem map_mem_fixedVectors {W : Type*} [AddCommGroup W] [Module ℂ W]
    {σ : Representation ℂ G W} (f : Representation.IntertwiningMap ρ σ) {H : Subgroup G} {v : V}
    (hv : v ∈ fixedVectors ρ H) : f v ∈ fixedVectors σ H := fun h hh => by
  rw [← f.isIntertwining, hv h hh]

theorem map_coinvariantsKer_le {W : Type*} [AddCommGroup W] [Module ℂ W]
    {σ : Representation ℂ G W} (f : Representation.IntertwiningMap ρ σ) (H : Subgroup G) :
    coinvariantsKer ρ H ≤ (coinvariantsKer σ H).comap f.toLinearMap := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨⟨h, v⟩, rfl⟩
  simp only [SetLike.mem_coe, Submodule.mem_comap, map_sub, MonoidHom.coe_comp,
    Function.comp_apply, Subgroup.coe_subtype, Representation.IntertwiningMap.toLinearMap_apply,
    f.isIntertwining]
  exact sub_mem_coinvariantsKer h.2 (f v)

variable {ρ} in

theorem coinvariantsKer_le_ker_of_invariant {W : Type*} [AddCommGroup W] [Module ℂ W]
    {K : Subgroup G} {f : V →ₗ[ℂ] W} (hf : ∀ k ∈ K, ∀ v, f (ρ k v) = f v) :
    coinvariantsKer ρ K ≤ LinearMap.ker f := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨⟨k, v⟩, rfl⟩
  simp [hf k k.2 v]

def fixedMap {W : Type*} [AddCommGroup W] [Module ℂ W] {σ : Representation ℂ G W}
    (f : Representation.IntertwiningMap ρ σ) (H : Subgroup G) :
    fixedVectors ρ H →ₗ[ℂ] fixedVectors σ H :=
  f.toLinearMap.restrict fun _ hv => map_mem_fixedVectors ρ f hv

theorem coe_fixedMap_apply {W : Type*} [AddCommGroup W] [Module ℂ W]
    {σ : Representation ℂ G W} (f : Representation.IntertwiningMap ρ σ) (H : Subgroup G)
    (v : fixedVectors ρ H) : (fixedMap ρ f H v : W) = f v := rfl

theorem fixedVectors_sup_le_inf (K L : Subgroup G) :
    fixedVectors ρ K ⊔ fixedVectors ρ L ≤ fixedVectors ρ (K ⊓ L) :=
  sup_le (fixedVectors_antitone ρ inf_le_left) (fixedVectors_antitone ρ inf_le_right)

section CosetSum

variable (K N : Subgroup G)

def cosetSum : Module.End ℂ V :=
  ∑ᶠ q : K ⧸ N.subgroupOf K, ρ ((Quotient.out q : K) : G)

variable {K N}

theorem cosetSum_apply [Fintype (K ⧸ N.subgroupOf K)] (v : V) :
    cosetSum ρ K N v = ∑ q : K ⧸ N.subgroupOf K, ρ ((Quotient.out q : K) : G) v := by
  rw [cosetSum, finsum_eq_sum_of_fintype, LinearMap.sum_apply]

theorem act_eq_of_mk_eq {v : V} (hv : v ∈ fixedVectors ρ N) {a b : K}
    (h : (a : K ⧸ N.subgroupOf K) = b) : ρ (a : G) v = ρ (b : G) v := by
  rw [QuotientGroup.eq] at h
  have hab : ρ ((a⁻¹ * b : K) : G) v = v := hv _ (Subgroup.mem_subgroupOf.1 h)
  calc ρ (a : G) v = ρ (a : G) (ρ ((a⁻¹ * b : K) : G) v) := by rw [hab]
    _ = ρ (b : G) v := by
      rw [← Module.End.mul_apply, ← map_mul]
      simp

theorem cosetSum_mem_fixedVectors (hnorm : ∀ k ∈ K, ∀ n ∈ N, k * n * k⁻¹ ∈ N)
    [Fintype (K ⧸ N.subgroupOf K)] {v : V} (hv : v ∈ fixedVectors ρ N) :
    cosetSum ρ K N v ∈ fixedVectors ρ K := by
  have : (N.subgroupOf K).Normal :=
    ⟨fun n hn g => Subgroup.mem_subgroupOf.2 (by simpa using hnorm g g.2 n hn)⟩
  intro k hk
  rw [cosetSum_apply, map_sum]
  refine Fintype.sum_equiv (Equiv.mulLeft ((⟨k, hk⟩ : K) : K ⧸ N.subgroupOf K)) _ _ fun q => ?_
  rw [← Module.End.mul_apply, ← map_mul]
  have := act_eq_of_mk_eq ρ hv (a := ⟨k, hk⟩ * Quotient.out q)
    (b := Quotient.out (((⟨k, hk⟩ : K) : K ⧸ N.subgroupOf K) * q)) (by
      rw [QuotientGroup.out_eq', QuotientGroup.mk_mul, QuotientGroup.out_eq'])
  simpa using this

theorem cosetSum_apply_act (hnorm : ∀ k ∈ K, ∀ n ∈ N, k * n * k⁻¹ ∈ N)
    [Fintype (K ⧸ N.subgroupOf K)] {u : V} (hu : u ∈ fixedVectors ρ N) {k : G} (hk : k ∈ K) :
    cosetSum ρ K N (ρ k u) = cosetSum ρ K N u := by
  have : (N.subgroupOf K).Normal :=
    ⟨fun n hn g => Subgroup.mem_subgroupOf.2 (by simpa using hnorm g g.2 n hn)⟩
  rw [cosetSum_apply, cosetSum_apply]
  refine Fintype.sum_equiv (Equiv.mulRight ((⟨k, hk⟩ : K) : K ⧸ N.subgroupOf K)) _ _ fun q => ?_
  rw [← Module.End.mul_apply, ← map_mul]
  have := act_eq_of_mk_eq ρ hu (a := Quotient.out q * ⟨k, hk⟩)
    (b := Quotient.out (q * ((⟨k, hk⟩ : K) : K ⧸ N.subgroupOf K))) (by
      rw [QuotientGroup.out_eq', QuotientGroup.mk_mul, QuotientGroup.out_eq'])
  simpa using this

theorem cosetSum_of_mem [Fintype (K ⧸ N.subgroupOf K)] {v : V} (hv : v ∈ fixedVectors ρ K) :
    cosetSum ρ K N v = (Fintype.card (K ⧸ N.subgroupOf K) : ℂ) • v := by
  rw [cosetSum_apply, Nat.cast_smul_eq_nsmul, ← Finset.card_univ, ← Finset.sum_const]
  exact Finset.sum_congr rfl fun q _ => hv _ (Quotient.out q).2

end CosetSum

theorem fixedMap_injective {W : Type*} [AddCommGroup W] [Module ℂ W]
    {σ : Representation ℂ G W} {K : Subgroup G} {f : Representation.IntertwiningMap ρ σ}
    (hf : Function.Injective f) : Function.Injective (fixedMap ρ f K) :=
  fun x y h => Subtype.ext (hf (by simpa [Subtype.ext_iff, coe_fixedMap_apply] using h))

variable [TopologicalSpace G]

def IsSmooth : Prop := ∀ v : V, IsOpen (stabilizerOf ρ v : Set G)

variable [IsTopologicalGroup G]

def smoothVectors : Submodule ℂ V where
  carrier := {v | IsOpen (stabilizerOf ρ v : Set G)}
  add_mem' {v w} hv hw := by
    refine Subgroup.isOpen_mono (H₁ := stabilizerOf ρ v ⊓ stabilizerOf ρ w) ?_ ?_
    · intro g hg
      simp [mem_stabilizerOf, mem_stabilizerOf.1 (Subgroup.mem_inf.1 hg).1,
        mem_stabilizerOf.1 (Subgroup.mem_inf.1 hg).2]
    · rw [Subgroup.coe_inf]
      exact hv.inter hw
  zero_mem' := by
    have : (stabilizerOf ρ (0 : V) : Set G) = univ := by
      ext g
      simp [mem_stabilizerOf]
    simp only [Set.mem_ofPred_eq, this, isOpen_univ]
  smul_mem' c v hv := Subgroup.isOpen_mono (H₁ := stabilizerOf ρ v)
    (fun g hg => by simp [mem_stabilizerOf, mem_stabilizerOf.1 hg]) hv

variable {ρ} in
theorem mem_smoothVectors {v : V} : v ∈ smoothVectors ρ ↔ IsOpen (stabilizerOf ρ v : Set G) :=
  Iff.rfl

theorem isSmooth_iff_smoothVectors_eq_top : IsSmooth ρ ↔ smoothVectors ρ = ⊤ := by
  rw [eq_top_iff]
  exact ⟨fun h v _ => h v, fun h v => h Submodule.mem_top⟩

theorem smooth_apply_mem {v : V} (hv : v ∈ smoothVectors ρ) (g : G) :
    ρ g v ∈ smoothVectors ρ := by
  rw [mem_smoothVectors] at hv ⊢
  apply Subgroup.isOpen_of_mem_nhds (g := 1) _
  have hc : Continuous fun x : G => g⁻¹ * x * g := by fun_prop
  have h1 : (fun x : G => g⁻¹ * x * g) ⁻¹' (stabilizerOf ρ v : Set G) ∈ 𝓝 (1 : G) :=
    (hv.preimage hc).mem_nhds (by simp)
  refine mem_of_superset h1 fun x hx => ?_
  simp only [Set.mem_preimage, SetLike.mem_coe, mem_stabilizerOf] at hx ⊢
  conv_rhs => rw [← hx]
  rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
  congr 2
  group

def smoothPart : Representation ℂ G (smoothVectors ρ) :=
  ρ.subrepresentation (smoothVectors ρ) fun g _ hv => smooth_apply_mem ρ hv g

@[simp]
theorem coe_smoothPart_apply (g : G) (v : smoothVectors ρ) :
    ((smoothPart ρ g v : smoothVectors ρ) : V) = ρ g v := rfl

theorem isSmooth_smoothPart : IsSmooth (smoothPart ρ) := by
  intro v
  have : (stabilizerOf (smoothPart ρ) v : Set G) = stabilizerOf ρ (v : V) := by
    ext g
    simp [mem_stabilizerOf, Subtype.ext_iff]
  rw [this]
  exact v.2

def IsAdmissible : Prop :=
  IsSmooth ρ ∧ ∀ K : Subgroup G, IsCompact (K : Set G) → IsOpen (K : Set G) →
    FiniteDimensional ℂ (fixedVectors ρ K)

end General

section LocallyProfinite

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
  {V : Type*} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)

theorem mem_smoothVectors_iff {v : V} :
    v ∈ smoothVectors ρ ↔ ∃ K : Subgroup G, IsCompact (K : Set G) ∧ IsOpen (K : Set G) ∧
      v ∈ fixedVectors ρ K := by
  constructor
  · intro hv
    obtain ⟨K, hKc, hKv⟩ :=
      exists_openSubgroup_isCompact_subset (hv.mem_nhds (one_mem (stabilizerOf ρ v)))
    exact ⟨K, hKc, K.isOpen, fun k hk => hKv hk⟩
  · rintro ⟨K, -, hKo, hv⟩
    exact Subgroup.isOpen_mono (mem_fixedVectors_iff_le.1 hv) hKo

theorem isSmooth_iff_forall_exists :
    IsSmooth ρ ↔ ∀ v : V, ∃ K : Subgroup G, IsCompact (K : Set G) ∧ IsOpen (K : Set G) ∧
      v ∈ fixedVectors ρ K :=
  forall_congr' fun _ => mem_smoothVectors_iff ρ

theorem isSmooth_iff_iUnion_fixedVectors :
    IsSmooth ρ ↔ ⋃ (K : Subgroup G) (_ : IsCompact (K : Set G)) (_ : IsOpen (K : Set G)),
      (fixedVectors ρ K : Set V) = univ := by
  rw [isSmooth_iff_forall_exists, eq_univ_iff_forall]
  simp only [mem_iUnion, SetLike.mem_coe, exists_prop]

section Average

variable {K : Subgroup G}

theorem exists_normal_subgroup (hKc : IsCompact (K : Set G)) (hKo : IsOpen (K : Set G))
    {U : Set G} (hU : U ∈ 𝓝 (1 : G)) :
    ∃ N : Subgroup G, IsOpen (N : Set G) ∧ N ≤ K ∧ (N : Set G) ⊆ U ∧
      (∀ k ∈ K, ∀ n ∈ N, k * n * k⁻¹ ∈ N) ∧ Finite (K ⧸ N.subgroupOf K) := by
  obtain ⟨N, -, hNU, hnorm⟩ := exists_compactOpenSubgroup_normalized hKc
    (inter_mem hU (hKo.mem_nhds (one_mem K)))
  refine ⟨N, N.isOpen, fun x hx => (hNU hx).2, fun x hx => (hNU hx).1, hnorm, ?_⟩
  have : CompactSpace K := isCompact_iff_compactSpace.1 hKc
  refine Subgroup.quotient_finite_of_isOpen _ ?_
  rw [Subgroup.coe_subgroupOf]
  exact N.isOpen.preimage continuous_subtype_val

end Average

section Decomposition

variable {ρ} {K : Subgroup G}

omit [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in

theorem exists_nhds_cosetSum_eq_zero (hρ : IsSmooth ρ) {x : V} (hx : x ∈ coinvariantsKer ρ K) :
    ∃ U ∈ 𝓝 (1 : G), ∀ N : Subgroup G, (N : Set G) ⊆ U →
      (∀ k ∈ K, ∀ n ∈ N, k * n * k⁻¹ ∈ N) → ∀ _ : Fintype (K ⧸ N.subgroupOf K),
        cosetSum ρ K N x = 0 := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨k, u⟩, rfl⟩ := hx
    refine ⟨stabilizerOf ρ u, (hρ u).mem_nhds (one_mem _), fun N hNU hnorm _ => ?_⟩
    have hu : u ∈ fixedVectors ρ N := fun n hn => hNU hn
    simp only [MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype, map_sub]
    rw [cosetSum_apply_act ρ hnorm hu k.2, sub_self]
  | zero => exact ⟨univ, univ_mem, fun _ _ _ _ => map_zero _⟩
  | add x y _ _ hx hy =>
    obtain ⟨U₁, hU₁, h₁⟩ := hx
    obtain ⟨U₂, hU₂, h₂⟩ := hy
    refine ⟨U₁ ∩ U₂, inter_mem hU₁ hU₂, fun N hNU hnorm hfin => ?_⟩
    rw [map_add, h₁ N (hNU.trans inter_subset_left) hnorm hfin,
      h₂ N (hNU.trans inter_subset_right) hnorm hfin, add_zero]
  | smul c x _ hx =>
    obtain ⟨U, hU, h⟩ := hx
    exact ⟨U, hU, fun N hNU hnorm hfin => by rw [map_smul, h N hNU hnorm hfin, smul_zero]⟩

theorem disjoint_fixedVectors_coinvariantsKer (hρ : IsSmooth ρ) (hKc : IsCompact (K : Set G))
    (hKo : IsOpen (K : Set G)) : Disjoint (fixedVectors ρ K) (coinvariantsKer ρ K) := by
  rw [Submodule.disjoint_def]
  intro w hw hw'
  obtain ⟨U, hU, hUw⟩ := exists_nhds_cosetSum_eq_zero hρ hw'
  obtain ⟨N, -, -, hNU, hnorm, hfin⟩ := exists_normal_subgroup hKc hKo hU
  have := Fintype.ofFinite (K ⧸ N.subgroupOf K)
  have h := hUw N hNU hnorm inferInstance
  rw [cosetSum_of_mem ρ hw] at h
  exact (smul_eq_zero.1 h).resolve_left (Nat.cast_ne_zero.2 Fintype.card_ne_zero)

theorem codisjoint_fixedVectors_coinvariantsKer (hρ : IsSmooth ρ) (hKc : IsCompact (K : Set G))
    (hKo : IsOpen (K : Set G)) : Codisjoint (fixedVectors ρ K) (coinvariantsKer ρ K) := by
  rw [codisjoint_iff, eq_top_iff]
  intro v _
  obtain ⟨N, -, hNK, hNU, hnorm, hfin⟩ := exists_normal_subgroup hKc hKo ((hρ v).mem_nhds
    (one_mem (stabilizerOf ρ v)))
  have := Fintype.ofFinite (K ⧸ N.subgroupOf K)
  have hv : v ∈ fixedVectors ρ N := fun n hn => hNU hn
  set n : ℂ := (Fintype.card (K ⧸ N.subgroupOf K) : ℂ)
  have hn : n ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  refine Submodule.mem_sup.2 ⟨n⁻¹ • cosetSum ρ K N v,
    Submodule.smul_mem _ _ (cosetSum_mem_fixedVectors ρ hnorm hv), v - n⁻¹ • cosetSum ρ K N v,
    ?_, add_sub_cancel _ _⟩
  have heq : v - n⁻¹ • cosetSum ρ K N v =
      n⁻¹ • ∑ q : K ⧸ N.subgroupOf K, (v - ρ ((Quotient.out q : K) : G) v) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, ← cosetSum_apply, smul_sub,
      ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hn, one_smul]
  rw [heq]
  refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun q _ => ?_)
  rw [← neg_sub]
  exact Submodule.neg_mem _ (sub_mem_coinvariantsKer (Quotient.out q).2 v)

theorem isCompl_fixedVectors_coinvariantsKer (hρ : IsSmooth ρ) (hKc : IsCompact (K : Set G))
    (hKo : IsOpen (K : Set G)) : IsCompl (fixedVectors ρ K) (coinvariantsKer ρ K) :=
  ⟨disjoint_fixedVectors_coinvariantsKer hρ hKc hKo,
    codisjoint_fixedVectors_coinvariantsKer hρ hKc hKo⟩

variable (ρ) in

def fixedProj (hρ : IsSmooth ρ) (hKc : IsCompact (K : Set G)) (hKo : IsOpen (K : Set G)) :
    V →ₗ[ℂ] fixedVectors ρ K :=
  Submodule.projectionOnto _ _ (isCompl_fixedVectors_coinvariantsKer hρ hKc hKo)

variable (hρ : IsSmooth ρ) (hKc : IsCompact (K : Set G)) (hKo : IsOpen (K : Set G))
include hρ hKc hKo

theorem fixedProj_apply_of_mem {v : V} (hv : v ∈ fixedVectors ρ K) :
    (fixedProj ρ hρ hKc hKo v : V) = v := by
  rw [fixedProj, Submodule.projectionOnto_apply_of_mem_left _ hv]

theorem fixedProj_apply_of_mem_coinvariantsKer {v : V} (hv : v ∈ coinvariantsKer ρ K) :
    fixedProj ρ hρ hKc hKo v = 0 :=
  (Submodule.projectionOnto_apply_eq_zero_iff _).2 hv

theorem ker_fixedProj : LinearMap.ker (fixedProj ρ hρ hKc hKo) = coinvariantsKer ρ K :=
  Submodule.ker_projectionOnto _

theorem sub_fixedProj_mem (v : V) : v - fixedProj ρ hρ hKc hKo v ∈ coinvariantsKer ρ K := by
  have := Submodule.sub_projection_mem (isCompl_fixedVectors_coinvariantsKer hρ hKc hKo) v
  rwa [Submodule.projection_apply] at this

theorem fixedProj_eq_iff {v : V} {w : fixedVectors ρ K} :
    fixedProj ρ hρ hKc hKo v = w ↔ v - w ∈ coinvariantsKer ρ K := by
  constructor
  · rintro rfl
    exact sub_fixedProj_mem hρ hKc hKo v
  · intro h
    have h1 := fixedProj_apply_of_mem_coinvariantsKer hρ hKc hKo h
    rw [map_sub] at h1
    rw [sub_eq_zero.1 h1]
    exact Subtype.ext (fixedProj_apply_of_mem hρ hKc hKo w.2)

theorem fixedProj_apply_act {k : G} (hk : k ∈ K) (v : V) :
    fixedProj ρ hρ hKc hKo (ρ k v) = fixedProj ρ hρ hKc hKo v := by
  rw [← sub_eq_zero, ← map_sub]
  exact fixedProj_apply_of_mem_coinvariantsKer hρ hKc hKo (sub_mem_coinvariantsKer hk v)

theorem eq_of_invariant_of_eqOn {W : Type*} [AddCommGroup W] [Module ℂ W] {f g : V →ₗ[ℂ] W}
    (hf : ∀ k ∈ K, ∀ v, f (ρ k v) = f v) (hg : ∀ k ∈ K, ∀ v, g (ρ k v) = g v)
    (h : ∀ v ∈ fixedVectors ρ K, f v = g v) : f = g := by
  ext v
  have hs := sub_fixedProj_mem hρ hKc hKo v
  have e1 : f v = f (fixedProj ρ hρ hKc hKo v) := by
    rw [← sub_eq_zero, ← map_sub]; exact coinvariantsKer_le_ker_of_invariant hf hs
  have e2 : g v = g (fixedProj ρ hρ hKc hKo v) := by
    rw [← sub_eq_zero, ← map_sub]; exact coinvariantsKer_le_ker_of_invariant hg hs
  rw [e1, e2, h _ (fixedProj ρ hρ hKc hKo v).2]

omit hρ in

theorem fixedProj_map {W : Type*} [AddCommGroup W] [Module ℂ W] {σ : Representation ℂ G W}
    (hρ : IsSmooth ρ) (hσ : IsSmooth σ) (f : Representation.IntertwiningMap ρ σ) (v : V) :
    fixedProj σ hσ hKc hKo (f v) = fixedMap ρ f K (fixedProj ρ hρ hKc hKo v) := by
  rw [fixedProj_eq_iff, coe_fixedMap_apply, ← map_sub]
  exact map_coinvariantsKer_le ρ f K (sub_fixedProj_mem hρ hKc hKo v)

end Decomposition

section Exactness

variable {W X : Type*} [AddCommGroup W] [Module ℂ W] [AddCommGroup X] [Module ℂ X]
  {ρ} {σ : Representation ℂ G W} {τ : Representation ℂ G X} {K : Subgroup G}

theorem exact_fixedMap (hρ : IsSmooth ρ) (hσ : IsSmooth σ) (hKc : IsCompact (K : Set G))
    (hKo : IsOpen (K : Set G)) {f : Representation.IntertwiningMap ρ σ}
    {g : Representation.IntertwiningMap σ τ} (hfg : Function.Exact f g) :
    Function.Exact (fixedMap ρ f K) (fixedMap σ g K) := by
  intro y
  constructor
  · intro hy
    have hy' : g (y : W) = 0 := by simpa [Subtype.ext_iff, coe_fixedMap_apply] using hy
    obtain ⟨v, hv⟩ := (hfg (y : W)).1 hy'
    refine ⟨fixedProj ρ hρ hKc hKo v, ?_⟩
    rw [← fixedProj_map hKc hKo hρ hσ f, hv]
    exact Subtype.ext (fixedProj_apply_of_mem hσ hKc hKo y.2)
  · rintro ⟨x, rfl⟩
    apply Subtype.ext
    simp only [coe_fixedMap_apply, ZeroMemClass.coe_zero]
    exact (hfg _).2 ⟨x, rfl⟩

theorem fixedMap_surjective (hρ : IsSmooth ρ) (hσ : IsSmooth σ) (hKc : IsCompact (K : Set G))
    (hKo : IsOpen (K : Set G)) {f : Representation.IntertwiningMap ρ σ}
    (hf : Function.Surjective f) : Function.Surjective (fixedMap ρ f K) := by
  intro y
  obtain ⟨v, hv⟩ := hf y
  refine ⟨fixedProj ρ hρ hKc hKo v, ?_⟩
  rw [← fixedProj_map hKc hKo hρ hσ f, hv]
  exact Subtype.ext (fixedProj_apply_of_mem hσ hKc hKo y.2)

end Exactness

end LocallyProfinite

end GroundTheory.Automorphic
