import Mathlib
import GroundTheory.LocalFields.AbstractLocalReciprocity.UniqueQuotientSubgroupOfSelf
import GroundTheory.LocalFields.AbstractLocalReciprocity.Frobenius
import GroundTheory.LocalFields.AbstractLocalReciprocity.Unramified

namespace GroundTheory.LocalField.Abstract

open ProfiniteInteger

namespace ClassFieldData

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] {A : Type*} [CommGroup A] [MulDistribMulAction G A]
  (D : ClassFieldData G A)

structure FrobeniusLift (K : OpenSubgroup G) where

  elt : G
  mem : elt ∈ (K : Subgroup G)

  deg : ℕ
  deg_pos : 0 < deg
  deg_eq : D.deg elt = Multiplicative.ofAdd ((deg * inertiaDegree D.deg K : ℕ) : ℤ̂)

variable {D} {K L : OpenSubgroup G}

namespace FrobeniusLift

omit [TotallyDisconnectedSpace G] in
theorem degree_ne_zero (s : D.FrobeniusLift K) : s.deg * inertiaDegree D.deg K ≠ 0 :=
  mul_ne_zero s.deg_pos.ne' (D.inertiaDegree_ne_zero K)

omit [TotallyDisconnectedSpace G] in

theorem mem_normalizer (hLK : L ≤ K) [hN : ((L : Subgroup G).subgroupOf K).Normal] {σ : G}
    (hσ : σ ∈ (K : Subgroup G)) :
    σ ∈ Subgroup.normalizer (((L : Subgroup G) ⊓ D.deg.ker : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  have hconj : ∀ g ∈ (K : Subgroup G), ∀ x ∈ (L : Subgroup G), g * x * g⁻¹ ∈ (L : Subgroup G) := by
    intro g hg x hx
    have := hN.conj_mem ⟨x, hLK hx⟩ (by simpa [Subgroup.mem_subgroupOf] using hx) ⟨g, hg⟩
    simpa [Subgroup.mem_subgroupOf] using this
  simp only [Subgroup.mem_inf, MonoidHom.mem_ker, map_mul, map_inv]
  constructor
  · rintro ⟨hL, hk⟩
    refine ⟨hconj σ hσ h hL, ?_⟩
    rw [hk, mul_one, mul_inv_cancel]
  · rintro ⟨hL, hk⟩
    refine ⟨?_, ?_⟩
    · have := hconj σ⁻¹ (K.inv_mem hσ) _ hL
      simpa [mul_assoc] using this
    · have := hk
      rwa [mul_comm (D.deg σ), mul_assoc, mul_inv_cancel, mul_one] at this

variable (L) in

noncomputable def field (hLK : L ≤ K) [((L : Subgroup G).subgroupOf K).Normal]
    (s : D.FrobeniusLift K) : OpenSubgroup G where
  toSubgroup := frobeniusClosure D.deg L s.elt
  isOpen' := isOpen_frobeniusClosure D.continuous_deg L.isOpen (mem_normalizer hLK s.mem)
    s.degree_ne_zero s.deg_eq

variable (hLK : L ≤ K) [((L : Subgroup G).subgroupOf K).Normal] (s : D.FrobeniusLift K)

theorem coe_field : ((s.field L hLK : OpenSubgroup G) : Subgroup G) =
    frobeniusClosure D.deg L s.elt :=
  rfl

theorem field_le : s.field L hLK ≤ K := by
  intro x hx
  exact frobeniusClosure_le K.isClosed s.mem (inf_le_left.trans hLK) hx

theorem elt_mem_field : s.elt ∈ ((s.field L hLK : OpenSubgroup G) : Subgroup G) :=
  mem_frobeniusClosure_self

theorem field_inf_ker :
    ((s.field L hLK : OpenSubgroup G) : Subgroup G) ⊓ D.deg.ker = (L : Subgroup G) ⊓ D.deg.ker :=
  frobeniusClosure_inf_ker D.continuous_deg L.isOpen (mem_normalizer hLK s.mem) s.degree_ne_zero
    s.deg_eq

theorem inertiaDegree_field :
    inertiaDegree D.deg ((s.field L hLK : OpenSubgroup G) : Subgroup G) =
      s.deg * inertiaDegree D.deg K :=
  inertiaDegree_frobeniusClosure D.continuous_deg (mem_normalizer hLK s.mem) s.degree_ne_zero
    s.deg_eq

theorem relDeg_field :
    D.relDeg (s.field L hLK) ⟨s.elt, s.elt_mem_field hLK⟩ = Multiplicative.ofAdd 1 := by
  refine (ProfiniteInteger.pow_left_inj (D.inertiaDegree_ne_zero (s.field L hLK))).1 ?_
  rw [D.relDeg_pow, inertiaDegree_field, ← ofAdd_nsmul, nsmul_one]
  exact s.deg_eq

theorem inf_ker_le_inf :
    ((s.field L hLK : OpenSubgroup G) : Subgroup G) ⊓ D.deg.ker ≤
      ((L ⊓ s.field L hLK : OpenSubgroup G) : Subgroup G) := by
  intro x hx
  have hx' := hx
  rw [field_inf_ker] at hx'
  exact ⟨hx'.1, hx.1⟩

end FrobeniusLift

omit [TotallyDisconnectedSpace G] in

theorem exists_prime (K : OpenSubgroup G) :
    ∃ π : fixedModule A (K : Subgroup G), D.valuation K π = Multiplicative.ofAdd 1 := by
  have h := D.intCast_mem_range_val 1
  rw [← D.range_valuation K, Int.cast_one] at h
  exact h

section PrimeNorm

variable (K L) in

noncomputable def primeNorm (S : OpenSubgroup G) : tateZero A (K : Subgroup G) (L : Subgroup G) :=
  QuotientGroup.mk (norm A (K : Subgroup G) (S : Subgroup G) (D.exists_prime S).choose)

omit [TotallyDisconnectedSpace G] in

theorem norm_mem_range_of_mem_units (hax : ClassFieldAxiom G A) {S : OpenSubgroup G} (hSK : S ≤ K)
    (hLK : L ≤ K) (hu : (S : Subgroup G) ⊓ D.deg.ker ≤ L) {u : fixedModule A (S : Subgroup G)}
    (hu' : u ∈ D.units S) :
    norm A (K : Subgroup G) (S : Subgroup G) u ∈ (norm A (K : Subgroup G) (L : Subgroup G)).range := by
  set M : OpenSubgroup G := L ⊓ S with hMdef
  have hMS : M ≤ S := inf_le_right
  have hML : M ≤ L := inf_le_left
  have hMu : (S : Subgroup G) ⊓ D.deg.ker ≤ M := fun x hx => ⟨hu hx, hx.1⟩
  rw [D.units_eq_map_norm hax hMS hMu] at hu'
  obtain ⟨w, -, rfl⟩ := hu'
  rw [norm_norm (fun x hx => hMS hx) (fun x hx => hSK hx) w]
  exact ⟨norm A (L : Subgroup G) (M : Subgroup G) w,
    norm_norm (fun x hx => hML hx) (fun x hx => hLK hx) w⟩

omit [TotallyDisconnectedSpace G] in

theorem mk_norm_eq_primeNorm (hax : ClassFieldAxiom G A) {S : OpenSubgroup G} (hSK : S ≤ K)
    (hLK : L ≤ K) (hu : (S : Subgroup G) ⊓ D.deg.ker ≤ L) {π : fixedModule A (S : Subgroup G)}
    (hπ : D.valuation S π = Multiplicative.ofAdd 1) :
    (QuotientGroup.mk (norm A (K : Subgroup G) (S : Subgroup G) π) :
      tateZero A (K : Subgroup G) (L : Subgroup G)) = D.primeNorm K L S := by
  set π0 := (D.exists_prime S).choose with hπ0
  have h0 : D.valuation S π0 = Multiplicative.ofAdd 1 := (D.exists_prime S).choose_spec
  have hu' : π * π0⁻¹ ∈ D.units S := by
    rw [D.mem_units, map_mul, map_inv, hπ, h0, mul_inv_cancel]
  obtain ⟨b, hb⟩ := D.norm_mem_range_of_mem_units hax hSK hLK hu hu'
  rw [primeNorm, ← hπ0, QuotientGroup.eq]
  have : (norm A (K : Subgroup G) (S : Subgroup G) π)⁻¹ * norm A (K : Subgroup G) (S : Subgroup G) π0 =
      (norm A (K : Subgroup G) (S : Subgroup G) (π * π0⁻¹))⁻¹ := by
    rw [map_mul, map_inv, mul_inv_rev, inv_inv, mul_comm]
  rw [this]
  exact Subgroup.inv_mem _ ⟨b, hb⟩

end PrimeNorm

section RecFrob

variable (hLK : L ≤ K) [((L : Subgroup G).subgroupOf K).Normal]

variable (L) in

noncomputable def recFrob (s : D.FrobeniusLift K) : tateZero A (K : Subgroup G) (L : Subgroup G) :=
  D.primeNorm K L (s.field L hLK)

theorem mk_norm_eq_recFrob (hax : ClassFieldAxiom G A) (s : D.FrobeniusLift K)
    {π : fixedModule A ((s.field L hLK : OpenSubgroup G) : Subgroup G)}
    (hπ : D.valuation (s.field L hLK) π = Multiplicative.ofAdd 1) :
    (QuotientGroup.mk (norm A (K : Subgroup G) ((s.field L hLK : OpenSubgroup G) : Subgroup G) π) :
      tateZero A (K : Subgroup G) (L : Subgroup G)) = D.recFrob L hLK s :=
  D.mk_norm_eq_primeNorm hax (s.field_le hLK) hLK (fun x hx => by
    have := (s.field_inf_ker hLK).le hx
    exact this.1) hπ

end RecFrob

end ClassFieldData

end GroundTheory.LocalField.Abstract
