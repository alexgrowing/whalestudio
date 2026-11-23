import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.TwistedIndependenceLemma.TwistedIndependence

noncomputable section

open GlobalTheory.PRep

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

namespace GlobalTheory.CompanionTheory.HeckeFixed

section Abstract

variable {H V : Type} [Group H] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ H V)

def stab (v : V) : Subgroup H where
  carrier := {h | ρ h v = v}
  one_mem' := by
    change ρ 1 v = v
    simp
  mul_mem' {a b} ha hb := by
    change ρ a v = v at ha
    change ρ b v = v at hb
    change ρ (a * b) v = v
    rw [map_mul, Module.End.mul_apply, hb, ha]
  inv_mem' {a} ha := by
    change ρ a v = v at ha
    change ρ a⁻¹ v = v
    conv_lhs => rw [← ha]
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

def coK : Submodule ℂ V := Submodule.span ℂ (Set.range fun p : H × V => ρ p.1 p.2 - p.2)

theorem sub_mem_coK (h : H) (v : V) : ρ h v - v ∈ coK ρ :=
  Submodule.subset_span ⟨(h, v), rfl⟩

def avg (S : Subgroup H) [S.FiniteIndex] : Module.End ℂ V := ∑ q : H ⧸ S, ρ (Quotient.out q)

theorem avg_apply (S : Subgroup H) [S.FiniteIndex] (x : V) :
    avg ρ S x = ∑ q : H ⧸ S, ρ (Quotient.out q) x := by
  simp [avg, LinearMap.sum_apply]

variable {ρ}

theorem act_eq_out {S : Subgroup H} {x : V} (hx : S ≤ stab ρ x) (h : H) :
    ρ h x = ρ (Quotient.out (h : H ⧸ S)) x := by
  have h1 : (Quotient.out (h : H ⧸ S))⁻¹ * h ∈ S :=
    QuotientGroup.eq.1 (QuotientGroup.out_eq' (h : H ⧸ S))
  have h2 : ρ ((Quotient.out (h : H ⧸ S))⁻¹ * h) x = x := hx h1
  conv_lhs => rw [show h = Quotient.out (h : H ⧸ S) * ((Quotient.out (h : H ⧸ S))⁻¹ * h) by group]
  rw [map_mul, Module.End.mul_apply, h2]

theorem avg_act {S : Subgroup H} [S.Normal] [S.FiniteIndex] {x : V} (hx : S ≤ stab ρ x) (k : H) :
    avg ρ S (ρ k x) = avg ρ S x := by
  rw [avg_apply, avg_apply]
  refine Fintype.sum_equiv (Equiv.mulRight (k : H ⧸ S)) _ _ fun q => ?_
  rw [← Module.End.mul_apply, ← map_mul, act_eq_out hx]
  congr 3
  rw [Equiv.coe_mulRight, QuotientGroup.mk_mul, QuotientGroup.out_eq']

theorem act_avg {S : Subgroup H} [S.Normal] [S.FiniteIndex] {x : V} (hx : S ≤ stab ρ x) (k : H) :
    ρ k (avg ρ S x) = avg ρ S x := by
  rw [avg_apply, map_sum]
  refine Fintype.sum_equiv (Equiv.mulLeft (k : H ⧸ S)) _ _ fun q => ?_
  rw [← Module.End.mul_apply, ← map_mul, act_eq_out hx]
  congr 3
  rw [Equiv.coe_mulLeft, QuotientGroup.mk_mul, QuotientGroup.out_eq']

theorem avg_of_mem_invariants (S : Subgroup H) [S.FiniteIndex] {x : V}
    (hx : x ∈ Representation.invariants ρ) :
    avg ρ S x = (Fintype.card (H ⧸ S) : ℂ) • x := by
  rw [avg_apply]
  simp only [(Representation.mem_invariants ρ x).1 hx, Finset.sum_const, Finset.card_univ,
    Nat.cast_smul_eq_nsmul]

theorem card_smul_sub_avg_mem (S : Subgroup H) [S.FiniteIndex] (x : V) :
    (Fintype.card (H ⧸ S) : ℂ) • x - avg ρ S x ∈ coK ρ := by
  have h : (Fintype.card (H ⧸ S) : ℂ) • x - avg ρ S x =
      -∑ q : H ⧸ S, (ρ (Quotient.out q) x - x) := by
    rw [avg_apply, Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_univ, Nat.cast_smul_eq_nsmul]
    abel
  rw [h]
  exact Submodule.neg_mem _ (Submodule.sum_mem _ fun q _ => sub_mem_coK ρ _ x)

theorem exists_avg_eq_zero (hfin : ∀ v, (stab ρ v).FiniteIndex) {x : V} (hx : x ∈ coK ρ) :
    ∃ S₀ : Subgroup H, S₀.Normal ∧ S₀.FiniteIndex ∧
      ∀ (S : Subgroup H) [S.Normal] [S.FiniteIndex], S ≤ S₀ → avg ρ S x = 0 := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨⟨h, v⟩, rfl⟩ := hy
    haveI := hfin v
    refine ⟨(stab ρ v).normalCore, Subgroup.normalCore_normal _,
      Subgroup.finiteIndex_normalCore _, fun S _ _ hS => ?_⟩
    have hSv : S ≤ stab ρ v := hS.trans (Subgroup.normalCore_le _)
    simp only [map_sub, avg_act hSv, sub_self]
  | zero => exact ⟨⊤, inferInstance, inferInstance, fun S _ _ _ => map_zero _⟩
  | add a b _ _ ha hb =>
    obtain ⟨A, hA1, hA2, hA⟩ := ha
    obtain ⟨B, hB1, hB2, hB⟩ := hb
    refine ⟨A ⊓ B, inferInstance, inferInstance, fun S _ _ hS => ?_⟩
    rw [map_add, hA S (hS.trans inf_le_left), hB S (hS.trans inf_le_right), add_zero]
  | smul c a _ ha =>
    obtain ⟨A, hA1, hA2, hA⟩ := ha
    exact ⟨A, hA1, hA2, fun S _ _ hS => by rw [map_smul, hA S hS, smul_zero]⟩

theorem isCompl_invariants_coK (hfin : ∀ v, (stab ρ v).FiniteIndex) :
    IsCompl (Representation.invariants ρ) (coK ρ) := by
  constructor
  · rw [Submodule.disjoint_def]
    intro x hx hx'
    obtain ⟨S, hS1, hS2, hS⟩ := exists_avg_eq_zero hfin hx'
    have h0 := hS S le_rfl
    rw [avg_of_mem_invariants S hx] at h0
    exact (smul_eq_zero.1 h0).resolve_left (Nat.cast_ne_zero.2 Fintype.card_ne_zero)
  · rw [codisjoint_iff, eq_top_iff]
    intro v _
    haveI := hfin v
    haveI : (stab ρ v).normalCore.FiniteIndex := Subgroup.finiteIndex_normalCore _
    have hSv : (stab ρ v).normalCore ≤ stab ρ v := Subgroup.normalCore_le _
    have hc : (Fintype.card (H ⧸ (stab ρ v).normalCore) : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.2 Fintype.card_ne_zero
    set c : ℂ := (Fintype.card (H ⧸ (stab ρ v).normalCore) : ℂ) with hcdef
    have ha : c⁻¹ • avg ρ (stab ρ v).normalCore v ∈ Representation.invariants ρ := by
      refine Submodule.smul_mem _ _ ((Representation.mem_invariants ρ _).2 fun k => ?_)
      exact act_avg hSv k
    have hb : v - c⁻¹ • avg ρ (stab ρ v).normalCore v ∈ coK ρ := by
      have h : v - c⁻¹ • avg ρ (stab ρ v).normalCore v =
          c⁻¹ • (c • v - avg ρ (stab ρ v).normalCore v) := by
        rw [smul_sub, smul_smul, inv_mul_cancel₀ hc, one_smul]
      rw [h]
      exact Submodule.smul_mem _ _ (card_smul_sub_avg_mem _ v)
    exact Submodule.mem_sup.2 ⟨_, ha, _, hb, add_sub_cancel _ _⟩

end Abstract

section Fixed

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]

theorem mem_fixed_iff {π : Representation ℂ G V} {K : Subgroup G} {v : V} :
    v ∈ fixed π K ↔ ∀ k ∈ K, π k v = v := by
  constructor
  · intro h k hk
    simpa [fixed, eig] using h ⟨k, hk⟩
  · intro h k
    simpa using h k k.2

abbrev resK (π : Representation ℂ G V) (K : Subgroup G) : Representation ℂ K V :=
  π.comp K.subtype

theorem fixed_eq_invariants (π : Representation ℂ G V) (K : Subgroup G) :
    fixed π K = Representation.invariants (resK π K) := by
  ext v
  rw [mem_fixed_iff, Representation.mem_invariants]
  exact ⟨fun h k => h k k.2, fun h k hk => h ⟨k, hk⟩⟩

variable [TopologicalSpace G]

def IsHeckeOn (π : Representation ℂ G V) (K : Subgroup G) (g : G)
    (T : Module.End ℂ (fixed π K)) : Prop :=
  ∀ (v : fixed π K) (l : Module.Dual ℂ V), (∀ x ∈ K, l ∘ₗ π x = l) →
    l (π g (v : V)) = l ((T v : fixed π K) : V)

variable [IsTopologicalGroup G]

theorem finiteIndex_stab {π : Representation ℂ G V} (hπ : IsSmooth π) {K : Subgroup G}
    (hKc : IsCompact (K : Set G)) (v : V) : (stab (resK π K) v).FiniteIndex := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hKc
  have ho : IsOpen (stab (resK π K) v : Set K) :=
    (hπ v).preimage continuous_subtype_val
  haveI := Subgroup.quotient_finite_of_isOpen _ ho
  exact Subgroup.finiteIndex_of_finite_quotient

theorem isCompl_res {π : Representation ℂ G V} (hπ : IsSmooth π) {K : Subgroup G}
    (hKc : IsCompact (K : Set G)) :
    IsCompl (Representation.invariants (resK π K)) (coK (resK π K)) :=
  isCompl_invariants_coK (finiteIndex_stab hπ hKc)

def eK (π : Representation ℂ G V) (hπ : IsSmooth π) {K : Subgroup G}
    (hKc : IsCompact (K : Set G)) : V →ₗ[ℂ] fixed π K :=
  LinearMap.codRestrict (fixed π K)
    ((Representation.invariants (resK π K)).subtype ∘ₗ
      Submodule.projectionOnto _ _ (isCompl_res hπ hKc))
    (fun v => by
      rw [fixed_eq_invariants]
      exact (Submodule.projectionOnto _ _ (isCompl_res hπ hKc) v).2)

variable {π : Representation ℂ G V} (hπ : IsSmooth π) {K : Subgroup G}
  (hKc : IsCompact (K : Set G))

theorem coe_eK (v : V) : (eK π hπ hKc v : V) =
    (Submodule.projectionOnto _ _ (isCompl_res hπ hKc) v : V) := rfl

theorem eK_apply_of_mem {v : V} (hv : v ∈ fixed π K) : (eK π hπ hKc v : V) = v := by
  have hv' : v ∈ Representation.invariants (resK π K) := by rwa [← fixed_eq_invariants]
  rw [coe_eK, Submodule.projectionOnto_apply_of_mem_left _ hv']

theorem eK_apply_of_mem_coK {v : V} (hv : v ∈ coK (resK π K)) : eK π hπ hKc v = 0 := by
  apply Subtype.ext
  rw [coe_eK, (Submodule.projectionOnto_apply_eq_zero_iff _).2 hv]
  rfl

theorem eK_apply_act {k : G} (hk : k ∈ K) (v : V) : eK π hπ hKc (π k v) = eK π hπ hKc v := by
  rw [← sub_eq_zero, ← map_sub]
  exact eK_apply_of_mem_coK hπ hKc (sub_mem_coK (resK π K) ⟨k, hk⟩ v)

theorem form_eK (l : Module.Dual ℂ V) (hl : ∀ x ∈ K, l ∘ₗ π x = l) (v : V) :
    l (eK π hπ hKc v : V) = l v := by
  have hker : coK (resK π K) ≤ LinearMap.ker l := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨⟨k, x⟩, rfl⟩
    have h := LinearMap.congr_fun (hl k k.2) x
    simp only [LinearMap.comp_apply] at h
    simp [h]
  have hs : v - (eK π hπ hKc v : V) ∈ coK (resK π K) := by
    have := Submodule.sub_projection_mem (isCompl_res hπ hKc) v
    rwa [Submodule.projection_apply] at this
  have h0 := hker hs
  rw [LinearMap.mem_ker, map_sub, sub_eq_zero] at h0
  exact h0.symm

def heckeOn (π : Representation ℂ G V) (hπ : IsSmooth π) {K : Subgroup G}
    (hKc : IsCompact (K : Set G)) (g : G) : Module.End ℂ (fixed π K) :=
  eK π hπ hKc ∘ₗ π g ∘ₗ (fixed π K).subtype

theorem heckeOn_apply (g : G) (v : fixed π K) :
    heckeOn π hπ hKc g v = eK π hπ hKc (π g (v : V)) := rfl

theorem isHeckeOn_heckeOn (g : G) : IsHeckeOn π K g (heckeOn π hπ hKc g) :=
  fun v l hl => by rw [heckeOn_apply, form_eK hπ hKc l hl]

include hπ hKc in

theorem IsHeckeOn.unique {g : G} {T T' : Module.End ℂ (fixed π K)}
    (hT : IsHeckeOn π K g T) (hT' : IsHeckeOn π K g T') : T = T' := by
  refine LinearMap.ext fun v => Subtype.ext ?_
  rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
  intro f
  have hinv : ∀ x ∈ K, (f ∘ₗ (fixed π K).subtype ∘ₗ eK π hπ hKc) ∘ₗ π x =
      f ∘ₗ (fixed π K).subtype ∘ₗ eK π hπ hKc := by
    intro x hx
    ext y
    simp only [LinearMap.comp_apply, eK_apply_act hπ hKc hx]
  have h := (hT v _ hinv).symm.trans (hT' v _ hinv)
  simp only [LinearMap.comp_apply, Submodule.subtype_apply,
    eK_apply_of_mem hπ hKc (T v).2, eK_apply_of_mem hπ hKc (T' v).2] at h
  rw [map_sub, h, sub_self]

include hπ hKc in

theorem existsUnique_isHeckeOn (g : G) : ∃! T : Module.End ℂ (fixed π K), IsHeckeOn π K g T :=
  ⟨heckeOn π hπ hKc g, isHeckeOn_heckeOn hπ hKc g,
    fun _ hT => hT.unique hπ hKc (isHeckeOn_heckeOn hπ hKc g)⟩

end Fixed

theorem heckeExistsUnique : PositivityTheory.Lbc.HeckeExistsUnique := by
  intro G _ _ _ K _ hKc V _ _ π hπ g
  exact existsUnique_isHeckeOn hπ hKc g

end GlobalTheory.CompanionTheory.HeckeFixed
