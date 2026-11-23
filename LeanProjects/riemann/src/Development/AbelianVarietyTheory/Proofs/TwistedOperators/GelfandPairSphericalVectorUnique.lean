import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsFactorisationCuspidal
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.FlathTensorProduct
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnitaryIrreducibleAdmissible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubleCosetOperatorsCommOfAntiInvolution
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsIrreducibleIff
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ImportsMore
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqTopOfStable
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField Filter GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace GlobalTheory.AdelicU GlobalTheory.AutMult
open GlobalTheory.PRep (IsAdmissible fixed)

noncomputable section

namespace GlobalTheory.GelfandLine

variable {G : Type} [Group G]

theorem mem_fixed_iff {V : Type} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
    {K : Subgroup G} {v : V} : v ∈ fixed ρ K ↔ ∀ k ∈ K, ρ k v = v :=
  ⟨fun h k hk => by simpa using h ⟨k, hk⟩, fun h k => by simpa using h k k.2⟩

def stabSub (K : Subgroup G) (g : G) : Subgroup G where
  carrier := {h | h ∈ K ∧ g⁻¹ * h * g ∈ K}
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨K.mul_mem ha hb, ?_⟩
    convert K.mul_mem ha' hb' using 1
    group
  one_mem' := ⟨K.one_mem, by simp⟩
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨K.inv_mem ha, ?_⟩
    convert K.inv_mem ha' using 1
    group

theorem mem_stabSub {K : Subgroup G} {g h : G} : h ∈ stabSub K g ↔ h ∈ K ∧ g⁻¹ * h * g ∈ K := Iff.rfl

def heckeOp {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (K : Subgroup G) (g : G)
    [Fintype (K ⧸ (stabSub K g).subgroupOf K)] : Module.End ℂ V :=
  ∑ q : K ⧸ (stabSub K g).subgroupOf K, ρ ((q.out : G) * g)

theorem heckeOp_apply {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (K : Subgroup G)
    (g : G) [Fintype (K ⧸ (stabSub K g).subgroupOf K)] (v : V) :
    heckeOp ρ K g v = ∑ q : K ⧸ (stabSub K g).subgroupOf K, ρ ((q.out : G) * g) v := by
  simp [heckeOp, LinearMap.sum_apply]

def repSet (K : Subgroup G) (g : G) [Fintype (K ⧸ (stabSub K g).subgroupOf K)] : Finset G :=
  Finset.univ.map ⟨fun q : K ⧸ (stabSub K g).subgroupOf K => (q.out : G) * g, fun q q' e => by
    have : (q.out : G) = q'.out := mul_right_cancel e
    exact Quotient.out_inj.1 (Subtype.ext this)⟩

theorem heckeOp_eq_sum {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (K : Subgroup G)
    (g : G) [Fintype (K ⧸ (stabSub K g).subgroupOf K)] (v : V) :
    heckeOp ρ K g v = ∑ γ ∈ repSet K g, ρ γ v := by
  rw [heckeOp_apply, repSet, Finset.sum_map]
  rfl

theorem repSet_spec (K : Subgroup G) (a : G) [Fintype (K ⧸ (stabSub K a).subgroupOf K)] :
    (∀ γ ∈ repSet K a, GelfandTrick.InDoubleCoset K a γ) ∧
    (∀ x : G, GelfandTrick.InDoubleCoset K a x → ∃! γ, γ ∈ repSet K a ∧ γ⁻¹ * x ∈ K) := by
  constructor
  · intro γ hγ
    obtain ⟨q, -, rfl⟩ := Finset.mem_map.1 hγ
    refine ⟨q.out, q.out.2, 1, K.one_mem, ?_⟩
    show (q.out : G) * a = (q.out : G) * a * 1
    simp
  · rintro x ⟨k₁, hk₁, k₂, hk₂, rfl⟩
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul ((stabSub K a).subgroupOf K) (⟨k₁, hk₁⟩ : K)
    have hh' : ((h : K) : G) ∈ stabSub K a := Subgroup.mem_subgroupOf.1 h.2
    set q : K ⧸ (stabSub K a).subgroupOf K := ((⟨k₁, hk₁⟩ : K) : K ⧸ (stabSub K a).subgroupOf K)
    have hq : ((q.out : K) : G) = k₁ * ((h : K) : G) := by
      rw [hh]; rfl
    refine ⟨(q.out : G) * a, ⟨Finset.mem_map.2 ⟨q, Finset.mem_univ _, rfl⟩, ?_⟩, ?_⟩
    · rw [hq]
      have : a⁻¹ * ((h : K) : G)⁻¹ * a ∈ K := (mem_stabSub.1 (inv_mem hh')).2
      convert K.mul_mem this hk₂ using 1
      group
    · rintro y ⟨hy, hyx⟩
      obtain ⟨p, -, rfl⟩ := Finset.mem_map.1 hy
      change (p.out : G) * a = (q.out : G) * a
      congr 1
      have hx1 : ((q.out : G) * a)⁻¹ * (k₁ * a * k₂) ∈ K := by
        rw [hq]
        have : a⁻¹ * ((h : K) : G)⁻¹ * a ∈ K := (mem_stabSub.1 (inv_mem hh')).2
        convert K.mul_mem this hk₂ using 1
        group
      have hx2 : ((p.out : G) * a)⁻¹ * (k₁ * a * k₂) ∈ K := hyx
      have hu : ((p.out : K)⁻¹ * q.out : K) ∈ (stabSub K a).subgroupOf K := by
        rw [Subgroup.mem_subgroupOf]
        refine ⟨(p.out⁻¹ * q.out : K).2, ?_⟩
        convert K.mul_mem hx2 (K.inv_mem hx1) using 1
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        group
      have : (p.out : K ⧸ (stabSub K a).subgroupOf K) = q.out := QuotientGroup.eq.2 hu
      rw [QuotientGroup.out_eq', QuotientGroup.out_eq'] at this
      rw [this]

theorem sum_comm_anti {V : Type} [AddCommGroup V] (K : Subgroup G) (τ : G → G)
    (hmul : ∀ a b, τ (a * b) = τ b * τ a) (hinv : ∀ a, τ (τ a) = a)
    (hdc : ∀ g : G, ∃ k₁ ∈ K, ∃ k₂ ∈ K, τ g = k₁ * g * k₂) (hK : ∀ k ∈ K, τ k ∈ K)
    (α β : G) (R S : Finset G)
    (hR : ∀ γ ∈ R, GelfandTrick.InDoubleCoset K α γ)
    (hR' : ∀ x : G, GelfandTrick.InDoubleCoset K α x → ∃! γ, γ ∈ R ∧ γ⁻¹ * x ∈ K)
    (hS : ∀ γ ∈ S, GelfandTrick.InDoubleCoset K β γ)
    (hS' : ∀ x : G, GelfandTrick.InDoubleCoset K β x → ∃! γ, γ ∈ S ∧ γ⁻¹ * x ∈ K)
    (F : G → V) (hF : ∀ k ∈ K, ∀ g, F (g * k) = F g) :
    ∑ γ ∈ R, ∑ δ ∈ S, F (γ * δ) = ∑ δ ∈ S, ∑ γ ∈ R, F (δ * γ) := by
  classical
  let f : G ⧸ K → V := fun c => F c.out
  have hf : ∀ g : G, f (g : G ⧸ K) = F g := fun g => by
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K g
    simp only [f, hk, hF k k.2]
  have key : ∀ A B : Finset G, ∑ γ ∈ A, ∑ δ ∈ B, F (γ * δ)
      = ∑ p ∈ A ×ˢ B, f ((p.1 * p.2 : G) : G ⧸ K) := fun A B => by
    rw [Finset.sum_product]
    simp only [hf]
  rw [key, key]
  let T : Finset (G ⧸ K) := (R ×ˢ S).image (fun p => ((p.1 * p.2 : G) : G ⧸ K)) ∪
    (S ×ˢ R).image (fun p => ((p.1 * p.2 : G) : G ⧸ K))
  rw [← Finset.sum_fiberwise_of_maps_to' (s := R ×ˢ S) (t := T)
      (g := fun p => ((p.1 * p.2 : G) : G ⧸ K))
      (fun p hp => Finset.mem_union_left _ (Finset.mem_image_of_mem _ hp)) f,
    ← Finset.sum_fiberwise_of_maps_to' (s := S ×ˢ R) (t := T)
      (g := fun p => ((p.1 * p.2 : G) : G ⧸ K))
      (fun p hp => Finset.mem_union_right _ (Finset.mem_image_of_mem _ hp)) f]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_const, Finset.sum_const]
  congr 1
  apply le_antisymm
  · convert GelfandTrick.card_pairs_le K τ hmul hinv hdc hK α β R S hR hR' hS hS' c
  · convert GelfandTrick.card_pairs_le K τ hmul hinv hdc hK β α S R hS hS' hR hR' c

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem heckeOp_comm (ρ : Representation ℂ G V) (K : Subgroup G) (τ : G → G)
    (hmul : ∀ a b, τ (a * b) = τ b * τ a) (hinv : ∀ a, τ (τ a) = a)
    (hdc : ∀ g : G, ∃ k₁ ∈ K, ∃ k₂ ∈ K, τ g = k₁ * g * k₂) (a b : G)
    [Fintype (K ⧸ (stabSub K a).subgroupOf K)] [Fintype (K ⧸ (stabSub K b).subgroupOf K)]
    {v : V} (hv : ∀ k ∈ K, ρ k v = v) :
    heckeOp ρ K a (heckeOp ρ K b v) = heckeOp ρ K b (heckeOp ρ K a v) := by
  have hK : ∀ k ∈ K, τ k ∈ K := fun k hk => by
    obtain ⟨k₁, h₁, k₂, h₂, e⟩ := hdc k
    rw [e]; exact K.mul_mem (K.mul_mem h₁ hk) h₂
  have := sum_comm_anti K τ hmul hinv hdc hK a b _ _ (repSet_spec K a).1 (repSet_spec K a).2
    (repSet_spec K b).1 (repSet_spec K b).2 (fun g => ρ g v)
    (fun k hk g => by simp only [map_mul, Module.End.mul_apply, hv k hk])
  rw [heckeOp_eq_sum ρ K a (heckeOp ρ K b v), heckeOp_eq_sum ρ K b v,
    heckeOp_eq_sum ρ K b (heckeOp ρ K a v), heckeOp_eq_sum ρ K a v]
  simpa only [map_sum, map_mul, Module.End.mul_apply] using this

theorem heckeTerm_eq (ρ : Representation ℂ G V) (K : Subgroup G) (a : G) {v : V}
    (hv : ∀ k ∈ K, ρ k v = v) (y : K) :
    ρ ((((y : K ⧸ (stabSub K a).subgroupOf K)).out : G) * a) v = ρ ((y : G) * a) v := by
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul ((stabSub K a).subgroupOf K) y
  have hh' : ((h : K) : G) ∈ stabSub K a := Subgroup.mem_subgroupOf.1 h.2
  rw [hh]
  have e : ((y * (h : K) : K) : G) * a = (y : G) * a * (a⁻¹ * ((h : K) : G) * a) := by
    simp only [Subgroup.coe_mul]; group
  rw [e, map_mul, Module.End.mul_apply, hv _ hh'.2]

theorem heckeOp_fixed (ρ : Representation ℂ G V) (K : Subgroup G) (a : G)
    [Fintype (K ⧸ (stabSub K a).subgroupOf K)] {v : V} (hv : ∀ k ∈ K, ρ k v = v) :
    ∀ k ∈ K, ρ k (heckeOp ρ K a v) = heckeOp ρ K a v := by
  intro k hk
  rw [heckeOp_apply, map_sum]
  refine Fintype.sum_equiv (MulAction.toPerm (⟨k, hk⟩ : K)) _ _ fun q => ?_
  have hq : (MulAction.toPerm (⟨k, hk⟩ : K) q : K ⧸ (stabSub K a).subgroupOf K) =
      ((⟨k, hk⟩ * q.out : K) : K ⧸ (stabSub K a).subgroupOf K) := by
    show (⟨k, hk⟩ : K) • q = _
    conv_lhs => rw [← QuotientGroup.out_eq' q]
    rfl
  rw [hq, heckeTerm_eq ρ K a hv, ← Module.End.mul_apply, ← map_mul, ← mul_assoc]
  rfl

theorem finsum_quot_le {K W : Type} [Group K] [AddCommGroup W] {H H' : Subgroup K} (hle : H ≤ H')
    [H.FiniteIndex] (F : K → W) (hF : ∀ y, ∀ h ∈ H', F (y * h) = F y) :
    ∑ᶠ q : K ⧸ H, F q.out = Nat.card (H' ⧸ H.subgroupOf H') • ∑ᶠ p : K ⧸ H', F p.out := by
  classical
  haveI : H'.FiniteIndex := Subgroup.finiteIndex_of_le hle
  let e := Subgroup.quotientEquivProdOfLE hle
  haveI : Finite ((K ⧸ H') × (H' ⧸ H.subgroupOf H')) := Finite.of_equiv _ e
  haveI : Finite (H' ⧸ H.subgroupOf H') := Finite.prod_right (K ⧸ H')
  haveI := Fintype.ofFinite (K ⧸ H)
  haveI := Fintype.ofFinite (K ⧸ H')
  haveI := Fintype.ofFinite (H' ⧸ H.subgroupOf H')
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype]
  have h1 : ∀ q : K ⧸ H, F q.out = F (e q).1.out := by
    intro q
    have : (e q).1 = ((q.out : K) : K ⧸ H') := by
      conv_lhs => rw [← QuotientGroup.out_eq' q]
      rfl
    rw [this]
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul H' q.out
    rw [hh, hF _ _ h.2]
  rw [Finset.sum_congr rfl fun q _ => h1 q, Fintype.sum_equiv e _ (fun y => F y.1.out) (fun _ => rfl),
    Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, Nat.card_eq_fintype_card]
  rw [Finset.smul_sum]

end GlobalTheory.GelfandLine

open GlobalTheory.GelfandLine in

theorem GlobalTheory.fixed_eq_span_of_gelfandPair : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (K : Subgroup G), IsOpen (K : Set G) → IsCompact (K : Set G) → ∀ θ : G → G, (∀ x y, θ (x * y) = θ y * θ x) → (∀ x, θ (θ x) = x) → (∀ g, ∃ a ∈ K, ∃ b ∈ K, θ g = a * g * b) → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ G W), ρ.IsIrreducible → IsAdmissible ρ → ∀ x ∈ fixed ρ K, x ≠ 0 → fixed ρ K = ℂ ∙ x := by
  first
  | exact @_root_.GlobalTheory.GroupAverageProjection.main
  | exact _root_.GlobalTheory.GroupAverageProjection.main
  | (apply _root_.GlobalTheory.GroupAverageProjection.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.GroupAverageProjection.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.GroupAverageProjection.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.GroupAverageProjection.main ..)
