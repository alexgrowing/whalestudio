import Mathlib
import GroundTheory.LocalFields.AbstractLocalReciprocity.Multiplicative

namespace GroundTheory.LocalField.Abstract

open ProfiniteInteger

namespace ClassFieldData

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] {A : Type*} [CommGroup A] [MulDistribMulAction G A]
  {D : ClassFieldData G A} {K L : OpenSubgroup G}

variable (hLK : L ≤ K) [((L : Subgroup G).subgroupOf K).Normal]

include hLK in
omit [TotallyDisconnectedSpace G] [((L : Subgroup G).subgroupOf K).Normal] in

theorem exists_frobeniusLift {τ : G} (hτ : τ ∈ (K : Subgroup G)) :
    ∃ s : D.FrobeniusLift K, τ⁻¹ * s.elt ∈ (L : Subgroup G) := by
  obtain ⟨w, hw⟩ := mem_multiples.1 (toAdd_deg_mem_multiples (D := D) K hτ)
  set f' := relInertiaDegree D.deg K L with hf'def
  have hf' : 0 < f' := Nat.pos_of_ne_zero (D.relInertiaDegree_ne_zero hLK)
  set F : ℕ+ := ⟨f', hf'⟩ with hFdef
  set m : ℕ := (proj F w).val + f' with hmdef
  have hm : 0 < m := by omega
  have hmw : (m : ℤ̂) - w ∈ multiples f' := by
    have := (proj_eq_zero_iff (n := F) (x := (m : ℤ̂) - w)).1 (by
      rw [map_sub, map_natCast, hmdef, Nat.cast_add, ZMod.natCast_zmod_val]
      have : ((f' : ℕ) : ZMod F) = 0 := by
        rw [hFdef]
        exact ZMod.natCast_self f'
      rw [this, add_zero, sub_self])
    simpa [hFdef] using this
  obtain ⟨z, hz⟩ := mem_multiples.1 hmw
  have hfL := inertiaDegree_eq_mul D.surjective_deg (K := (K : Subgroup G)) (L := (L : Subgroup G)) hLK
  obtain ⟨ρ, hρL, hρ⟩ := (D.mem_map_deg_iff L).2 ⟨Multiplicative.ofAdd z, rfl⟩
  refine ⟨⟨τ * ρ, K.mul_mem hτ (hLK hρL), m, hm, ?_⟩, by simpa using hρL⟩
  apply Multiplicative.toAdd.injective
  rw [map_mul, toAdd_mul, hρ, toAdd_pow, toAdd_ofAdd, toAdd_ofAdd, hw, hfL]
  have hz' : (f' : ℤ̂) * z = m - w := by rw [← nsmul_eq_mul, ← hz]
  simp only [nsmul_eq_mul]
  push_cast
  linear_combination (inertiaDegree D.deg K : ℤ̂) * hz'

theorem recFrob_eq_one_of_mem (s : D.FrobeniusLift K) (hs : s.elt ∈ (L : Subgroup G)) :
    D.recFrob L hLK s = 1 := by
  have hle : s.field L hLK ≤ L := fun x hx => frobeniusClosure_le L.isClosed hs inf_le_left hx
  unfold recFrob primeNorm
  rw [QuotientGroup.eq_one_iff]
  exact ⟨norm A (L : Subgroup G) ((s.field L hLK : OpenSubgroup G) : Subgroup G) _,
    norm_norm (fun x hx => hle hx) (fun x hx => hLK hx) _⟩

theorem field_eq_of_mem (s t : D.FrobeniusLift K)
    (h : s.elt⁻¹ * t.elt ∈ (L : Subgroup G) ⊓ D.deg.ker) : s.field L hLK = t.field L hLK := by
  apply OpenSubgroup.toSubgroup_injective
  show frobeniusClosure D.deg L s.elt = frobeniusClosure D.deg L t.elt
  unfold frobeniusClosure
  congr 1
  apply le_antisymm
  · refine sup_le (Subgroup.zpowers_le.2 ?_) le_sup_right
    have : s.elt = t.elt * (s.elt⁻¹ * t.elt)⁻¹ := by group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_zpowers _))
      (Subgroup.mem_sup_right (Subgroup.inv_mem _ h))
  · refine sup_le (Subgroup.zpowers_le.2 ?_) le_sup_right
    have : t.elt = s.elt * (s.elt⁻¹ * t.elt) := by group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_zpowers _))
      (Subgroup.mem_sup_right h)

theorem recFrob_eq_of_mem_of_le (hax : ClassFieldAxiom G A) [IsDiscreteModule G A]
    (s t : D.FrobeniusLift K) (h : s.elt⁻¹ * t.elt ∈ (L : Subgroup G)) (hle : s.deg ≤ t.deg) :
    D.recFrob L hLK s = D.recFrob L hLK t := by
  rcases Nat.eq_or_lt_of_le hle with heq | hlt
  · have hker : s.elt⁻¹ * t.elt ∈ D.deg.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, s.deg_eq, t.deg_eq, heq, inv_mul_cancel]
    unfold recFrob
    rw [field_eq_of_mem hLK s t ⟨h, hker⟩]
  · let ρ : D.FrobeniusLift K :=
      { elt := s.elt⁻¹ * t.elt
        mem := K.mul_mem (K.inv_mem s.mem) t.mem
        deg := t.deg - s.deg
        deg_pos := by omega
        deg_eq := by
          apply Multiplicative.toAdd.injective
          rw [map_mul, map_inv, toAdd_mul, toAdd_inv, s.deg_eq, t.deg_eq, toAdd_ofAdd, toAdd_ofAdd,
            toAdd_ofAdd]
          push_cast [Nat.cast_sub hlt.le]
          ring }
    have hρ : D.recFrob L hLK ρ = 1 := recFrob_eq_one_of_mem hLK ρ h
    rw [recFrob_congr hLK (s := t) (t := s.mul ρ) (by simp [FrobeniusLift.mul, ρ]),
      recFrob_mul hLK hax, hρ, mul_one]

theorem recFrob_eq_of_mem (hax : ClassFieldAxiom G A) [IsDiscreteModule G A]
    (s t : D.FrobeniusLift K) (h : s.elt⁻¹ * t.elt ∈ (L : Subgroup G)) :
    D.recFrob L hLK s = D.recFrob L hLK t := by
  rcases le_total s.deg t.deg with hle | hle
  · exact recFrob_eq_of_mem_of_le hLK hax s t h hle
  · refine (recFrob_eq_of_mem_of_le hLK hax t s ?_ hle).symm
    have := L.inv_mem h
    simpa using this

section Map

noncomputable def liftOf (τ : (K : Subgroup G)) : D.FrobeniusLift K :=
  (exists_frobeniusLift hLK τ.2).choose

omit [TotallyDisconnectedSpace G] [((L : Subgroup G).subgroupOf K).Normal] in
theorem liftOf_spec (τ : (K : Subgroup G)) : (τ : G)⁻¹ * (liftOf (D := D) hLK τ).elt ∈ (L : Subgroup G) :=
  (exists_frobeniusLift hLK τ.2).choose_spec

omit [TotallyDisconnectedSpace G] [((L : Subgroup G).subgroupOf K).Normal] in

theorem mk_liftOf (τ : (K : Subgroup G)) :
    ((⟨(liftOf (D := D) hLK τ).elt, (liftOf (D := D) hLK τ).mem⟩ : (K : Subgroup G)) :
      (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) = (τ : (K : Subgroup G) ⧸ _) := by
  rw [eq_comm, QuotientGroup.eq, Subgroup.mem_subgroupOf]
  simpa using liftOf_spec hLK τ

variable (hax : ClassFieldAxiom G A) [IsDiscreteModule G A]

noncomputable def recHom : (K : Subgroup G) →* tateZero A (K : Subgroup G) (L : Subgroup G) where
  toFun τ := D.recFrob L hLK (liftOf hLK τ)
  map_one' := recFrob_eq_one_of_mem hLK _ (by simpa using liftOf_spec (D := D) hLK 1)
  map_mul' τ1 τ2 := by
    rw [← recFrob_mul hLK hax]
    apply recFrob_eq_of_mem hLK hax
    have h12 := mk_liftOf (D := D) hLK (τ1 * τ2)
    have h1 := mk_liftOf (D := D) hLK τ1
    have h2 := mk_liftOf (D := D) hLK τ2
    have key : ((⟨(liftOf (D := D) hLK (τ1 * τ2)).elt, (liftOf (D := D) hLK (τ1 * τ2)).mem⟩ :
        (K : Subgroup G)) : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) =
        ((⟨(liftOf (D := D) hLK τ1).elt * (liftOf (D := D) hLK τ2).elt,
          K.mul_mem (liftOf (D := D) hLK τ1).mem (liftOf (D := D) hLK τ2).mem⟩ : (K : Subgroup G)) :
            (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) := by
      rw [h12, QuotientGroup.mk_mul, ← h1, ← h2, ← QuotientGroup.mk_mul]
      rfl
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at key
    simpa [FrobeniusLift.mul] using key

theorem recHom_apply (τ : (K : Subgroup G)) :
    D.recHom hLK hax τ = D.recFrob L hLK (liftOf hLK τ) :=
  rfl

noncomputable def reciprocity :
    (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K →* tateZero A (K : Subgroup G) (L : Subgroup G) :=
  QuotientGroup.lift _ (D.recHom hLK hax) fun τ hτ => by
    rw [MonoidHom.mem_ker, recHom_apply]
    apply recFrob_eq_one_of_mem hLK
    have := L.mul_mem (Subgroup.mem_subgroupOf.1 hτ) (liftOf_spec (D := D) hLK τ)
    simpa using this

theorem reciprocity_mk (s : D.FrobeniusLift K) :
    D.reciprocity hLK hax ((⟨s.elt, s.mem⟩ : (K : Subgroup G)) :
      (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) = D.recFrob L hLK s := by
  show D.recHom hLK hax ⟨s.elt, s.mem⟩ = _
  rw [recHom_apply]
  apply recFrob_eq_of_mem hLK hax
  have := L.inv_mem (liftOf_spec (D := D) hLK ⟨s.elt, s.mem⟩)
  simpa using this

theorem reciprocity_mk_eq_norm (s : D.FrobeniusLift K)
    {π : fixedModule A ((s.field L hLK : OpenSubgroup G) : Subgroup G)}
    (hπ : D.valuation (s.field L hLK) π = Multiplicative.ofAdd 1) :
    D.reciprocity hLK hax ((⟨s.elt, s.mem⟩ : (K : Subgroup G)) :
      (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) =
      (QuotientGroup.mk (norm A (K : Subgroup G)
        ((s.field L hLK : OpenSubgroup G) : Subgroup G) π) :
          tateZero A (K : Subgroup G) (L : Subgroup G)) := by
  rw [reciprocity_mk, D.mk_norm_eq_recFrob hLK hax s hπ]

include hLK in
omit [IsDiscreteModule G A] [TotallyDisconnectedSpace G] [((L : Subgroup G).subgroupOf K).Normal] in

theorem exists_frobeniusLift_mk (q : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) :
    ∃ s : D.FrobeniusLift K,
      ((⟨s.elt, s.mem⟩ : (K : Subgroup G)) : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) = q := by
  induction q using QuotientGroup.induction_on with
  | H τ => exact ⟨liftOf hLK τ, mk_liftOf hLK τ⟩

end Map

end ClassFieldData

end GroundTheory.LocalField.Abstract
