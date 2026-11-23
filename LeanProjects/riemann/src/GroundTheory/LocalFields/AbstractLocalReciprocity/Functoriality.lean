import Mathlib
import GroundTheory.LocalFields.AbstractLocalReciprocity.ReciprocityMap
import GroundTheory.LocalFields.AbstractLocalReciprocity.NormFormula

namespace GroundTheory.LocalField.Abstract

open ProfiniteInteger

section Conj

variable {G : Type*} [Group G]

theorem map_conj_apply {M : Type*} [CommGroup M] (f : G →* M) (σ x : G) :
    f (σ * x * σ⁻¹) = f x := by
  rw [map_mul, map_mul, map_inv, mul_right_comm, mul_inv_cancel, one_mul]

theorem mem_map_conj {H : Subgroup G} {σ x : G} :
    x ∈ H.map (MulAut.conj σ).toMonoidHom ↔ σ⁻¹ * x * σ ∈ H := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [mul_assoc] using hy
  · intro h
    exact ⟨σ⁻¹ * x * σ, h, by simp [mul_assoc]⟩

theorem coe_map_conj (H : Subgroup G) (σ : G) :
    (H.map (MulAut.conj σ).toMonoidHom : Set G) = (fun x => σ⁻¹ * x * σ) ⁻¹' (H : Set G) := by
  ext x
  exact mem_map_conj

theorem inertiaDegree_map_conj (d : G →* Multiplicative ℤ̂) (K : Subgroup G) (σ : G) :
    inertiaDegree d (K.map (MulAut.conj σ).toMonoidHom) = inertiaDegree d K := by
  have h : d.comp (MulAut.conj σ).toMonoidHom = d := MonoidHom.ext fun x => map_conj_apply d σ x
  rw [inertiaDegree, inertiaDegree, Subgroup.map_map, h]

variable [TopologicalSpace G] [IsTopologicalGroup G]

theorem isClosed_map_conj {H : Subgroup G} (hH : IsClosed (H : Set G)) (σ : G) :
    IsClosed (H.map (MulAut.conj σ).toMonoidHom : Set G) := by
  rw [coe_map_conj]
  exact hH.preimage ((continuous_const.mul continuous_id).mul continuous_const)

theorem map_conj_frobeniusClosure (d : G →* Multiplicative ℤ̂) (L : Subgroup G) (x ρ : G) :
    (frobeniusClosure d L x).map (MulAut.conj ρ).toMonoidHom =
      frobeniusClosure d (L.map (MulAut.conj ρ).toMonoidHom) (ρ * x * ρ⁻¹) := by
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    refine frobeniusClosure_le ?_ ?_ ?_
    · exact isClosed_frobeniusClosure.preimage
        ((continuous_const.mul continuous_id).mul continuous_const)
    · exact mem_frobeniusClosure_self
    · intro y hy
      obtain ⟨hyL, hyk⟩ := Subgroup.mem_inf.1 hy
      rw [Subgroup.mem_comap]
      refine le_frobeniusClosure (Subgroup.mem_inf.2 ⟨⟨y, hyL, rfl⟩, ?_⟩)
      rw [MonoidHom.mem_ker] at hyk ⊢
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [map_conj_apply, hyk]
  · refine frobeniusClosure_le (isClosed_map_conj isClosed_frobeniusClosure ρ)
      ⟨x, mem_frobeniusClosure_self, rfl⟩ ?_
    intro y hy
    obtain ⟨hyL, hyk⟩ := Subgroup.mem_inf.1 hy
    rw [mem_map_conj] at hyL ⊢
    refine le_frobeniusClosure (Subgroup.mem_inf.2 ⟨hyL, ?_⟩)
    rw [MonoidHom.mem_ker] at hyk ⊢
    have h : ρ⁻¹ * y * ρ = ρ⁻¹ * y * ρ⁻¹⁻¹ := by rw [inv_inv]
    rw [h, map_conj_apply, hyk]

theorem frobeniusClosure_mono {d : G →* Multiplicative ℤ̂} {L L' : Subgroup G} (h : L' ≤ L) (x : G) :
    frobeniusClosure d L' x ≤ frobeniusClosure d L x :=
  frobeniusClosure_le isClosed_frobeniusClosure mem_frobeniusClosure_self
    ((inf_le_inf_right _ h).trans le_frobeniusClosure)

def conjOpen (σ : G) (K : OpenSubgroup G) : OpenSubgroup G where
  toSubgroup := (K : Subgroup G).map (MulAut.conj σ).toMonoidHom
  isOpen' := by
    show IsOpen (((K : Subgroup G).map (MulAut.conj σ).toMonoidHom : Subgroup G) : Set G)
    rw [coe_map_conj]
    exact K.isOpen.preimage ((continuous_const.mul continuous_id).mul continuous_const)

theorem coe_conjOpen (σ : G) (K : OpenSubgroup G) :
    ((conjOpen σ K : OpenSubgroup G) : Subgroup G) = (K : Subgroup G).map (MulAut.conj σ).toMonoidHom :=
  rfl

theorem mem_conjOpen {σ x : G} {K : OpenSubgroup G} :
    x ∈ ((conjOpen σ K : OpenSubgroup G) : Subgroup G) ↔ σ⁻¹ * x * σ ∈ (K : Subgroup G) :=
  mem_map_conj

theorem conjOpen_mono (σ : G) {K L : OpenSubgroup G} (h : L ≤ K) : conjOpen σ L ≤ conjOpen σ K :=
  fun _ hx => Subgroup.map_mono (f := (MulAut.conj σ).toMonoidHom) h hx

instance normal_conjOpen (σ : G) (K L : OpenSubgroup G) [hN : ((L : Subgroup G).subgroupOf K).Normal] :
    (((conjOpen σ L : OpenSubgroup G) : Subgroup G).subgroupOf (conjOpen σ K)).Normal := by
  constructor
  intro n hn g
  rw [Subgroup.mem_subgroupOf, mem_conjOpen] at hn ⊢
  have hnK : σ⁻¹ * (n : G) * σ ∈ (K : Subgroup G) := mem_conjOpen.1 n.2
  have hgK : σ⁻¹ * (g : G) * σ ∈ (K : Subgroup G) := mem_conjOpen.1 g.2
  have := hN.conj_mem ⟨_, hnK⟩ (Subgroup.mem_subgroupOf.2 hn) ⟨_, hgK⟩
  rw [Subgroup.mem_subgroupOf] at this
  convert this using 1
  simp only [Subgroup.coe_mul, InvMemClass.coe_inv]
  group

end Conj

section Maps

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  {A : Type*} [CommGroup A] [MulDistribMulAction G A]

def galRestrict {K L K' L' : OpenSubgroup G} [((L : Subgroup G).subgroupOf K).Normal]
    [((L' : Subgroup G).subgroupOf K').Normal] (hK : K' ≤ K) (hL : L' ≤ L) :
    (K' : Subgroup G) ⧸ (L' : Subgroup G).subgroupOf K' →* (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K :=
  QuotientGroup.map _ _ (Subgroup.inclusion hK) fun x hx => by
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
    exact hL (Subgroup.mem_subgroupOf.1 hx)

omit [IsTopologicalGroup G] [CompactSpace G] in
theorem galRestrict_mk {K L K' L' : OpenSubgroup G} [((L : Subgroup G).subgroupOf K).Normal]
    [((L' : Subgroup G).subgroupOf K').Normal] (hK : K' ≤ K) (hL : L' ≤ L) (τ : (K' : Subgroup G)) :
    galRestrict hK hL (τ : (K' : Subgroup G) ⧸ (L' : Subgroup G).subgroupOf K') =
      ((⟨τ, hK τ.2⟩ : (K : Subgroup G)) : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) :=
  rfl

noncomputable def normTateZero {K L K' L' : OpenSubgroup G} (hK : K' ≤ K) (hL : L' ≤ L)
    (hL'K' : L' ≤ K') (hLK : L ≤ K) :
    tateZero A (K' : Subgroup G) (L' : Subgroup G) →* tateZero A (K : Subgroup G) (L : Subgroup G) :=
  QuotientGroup.map _ _ (norm A (K : Subgroup G) (K' : Subgroup G)) (by
    rintro _ ⟨b, rfl⟩
    rw [Subgroup.mem_comap, norm_norm (M := (L' : Subgroup G)) hL'K' hK,
      ← norm_norm (M := (L' : Subgroup G)) hL hLK]
    exact ⟨_, rfl⟩)

theorem normTateZero_mk {K L K' L' : OpenSubgroup G} (hK : K' ≤ K) (hL : L' ≤ L)
    (hL'K' : L' ≤ K') (hLK : L ≤ K) (a : fixedModule A (K' : Subgroup G)) :
    normTateZero hK hL hL'K' hLK (QuotientGroup.mk a : tateZero A (K' : Subgroup G) (L' : Subgroup G)) =
      (QuotientGroup.mk (norm A (K : Subgroup G) (K' : Subgroup G) a) :
        tateZero A (K : Subgroup G) (L : Subgroup G)) :=
  rfl

noncomputable def galConj (σ : G) (K L : OpenSubgroup G) [((L : Subgroup G).subgroupOf K).Normal] :
    (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K →*
      ((conjOpen σ K : OpenSubgroup G) : Subgroup G) ⧸
        ((conjOpen σ L : OpenSubgroup G) : Subgroup G).subgroupOf (conjOpen σ K) :=
  QuotientGroup.map _ _
    ((K : Subgroup G).equivMapOfInjective _ (MulAut.conj σ).injective).toMonoidHom fun x hx => by
      rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
      exact ⟨x, Subgroup.mem_subgroupOf.1 hx, rfl⟩

omit [CompactSpace G] in
theorem galConj_mk (σ : G) (K L : OpenSubgroup G) [((L : Subgroup G).subgroupOf K).Normal]
    (τ : (K : Subgroup G)) :
    galConj σ K L (τ : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) =
      ((⟨σ * τ * σ⁻¹, τ, τ.2, rfl⟩ : ((conjOpen σ K : OpenSubgroup G) : Subgroup G)) : _ ⧸ _) :=
  rfl

def conjFixed (σ : G) (K : OpenSubgroup G) :
    fixedModule A (K : Subgroup G) →* fixedModule A ((conjOpen σ K : OpenSubgroup G) : Subgroup G) where
  toFun a := ⟨σ • (a : A), smul_mem_fixedModule a.2 σ⟩
  map_one' := Subtype.ext (smul_one σ)
  map_mul' a b := Subtype.ext (smul_mul' σ (a : A) b)

theorem smul_norm_conjOpen (σ : G) (K L : OpenSubgroup G) (a : fixedModule A (L : Subgroup G)) :
    σ • (norm A (K : Subgroup G) (L : Subgroup G) a : A) =
      norm A ((conjOpen σ K : OpenSubgroup G) : Subgroup G) ((conjOpen σ L : OpenSubgroup G) : Subgroup G)
        (conjFixed σ L a) := by
  have : (((L : Subgroup G).map (MulAut.conj σ).toMonoidHom).subgroupOf
      ((K : Subgroup G).map (MulAut.conj σ).toMonoidHom)).FiniteIndex :=
    (inferInstance : (((conjOpen σ L : OpenSubgroup G) : Subgroup G).subgroupOf
      (conjOpen σ K)).FiniteIndex)
  exact smul_norm σ a

noncomputable def tateZeroConj (σ : G) (K L : OpenSubgroup G) :
    tateZero A (K : Subgroup G) (L : Subgroup G) →*
      tateZero A ((conjOpen σ K : OpenSubgroup G) : Subgroup G) ((conjOpen σ L : OpenSubgroup G) : Subgroup G) :=
  QuotientGroup.map _ _ (conjFixed σ K) (by
    rintro _ ⟨b, rfl⟩
    exact ⟨conjFixed σ L b, Subtype.ext (smul_norm_conjOpen σ K L b).symm⟩)

theorem tateZeroConj_mk (σ : G) (K L : OpenSubgroup G) (a : fixedModule A (K : Subgroup G)) :
    tateZeroConj σ K L (QuotientGroup.mk a : tateZero A (K : Subgroup G) (L : Subgroup G)) =
      (QuotientGroup.mk (conjFixed σ K a) : tateZero A _ _) :=
  rfl

end Maps

namespace ClassFieldData

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  {A : Type*} [CommGroup A] [MulDistribMulAction G A] {D : ClassFieldData G A}

theorem valuation_conj (σ : G) {K K' : OpenSubgroup G}
    (hK' : (K' : Subgroup G) = (K : Subgroup G).map (MulAut.conj σ).toMonoidHom)
    (a : fixedModule A (K : Subgroup G)) (b : fixedModule A (K' : Subgroup G))
    (hb : (b : A) = σ • (a : A)) : D.valuation K' b = D.valuation K a := by
  have hf : inertiaDegree D.deg (K' : Subgroup G) = inertiaDegree D.deg (K : Subgroup G) := by
    rw [hK', inertiaDegree_map_conj]
  rw [valuation_eq_iff, hf, valuation_pow D K a]
  congr 1
  apply Subtype.ext
  have htop : (⊤ : Subgroup G).map (MulAut.conj σ).toMonoidHom = ⊤ :=
    Subgroup.map_top_of_surjective _ (MulAut.conj σ).surjective
  have : (((K : Subgroup G).map (MulAut.conj σ).toMonoidHom).subgroupOf
      ((⊤ : Subgroup G).map (MulAut.conj σ).toMonoidHom)).FiniteIndex := by
    rw [← hK', htop]
    infer_instance
  have h1 := smul_norm σ (K := ⊤) a
  rw [(norm A ⊤ (K : Subgroup G) a).2 σ (Subgroup.mem_top σ), coe_norm_congr htop hK'.symm] at h1
  rw [h1]
  exact congrArg (fun x => (norm A ⊤ (K' : Subgroup G) x : A)) (Subtype.ext hb)

variable [TotallyDisconnectedSpace G]

section Restriction

noncomputable def FrobeniusLift.toBase {K K' : OpenSubgroup G} (hK : K' ≤ K) (s : D.FrobeniusLift K') :
    D.FrobeniusLift K where
  elt := s.elt
  mem := hK s.mem
  deg := s.deg * relInertiaDegree D.deg K K'
  deg_pos := Nat.mul_pos s.deg_pos (Nat.pos_of_ne_zero (D.relInertiaDegree_ne_zero hK))
  deg_eq := by
    rw [s.deg_eq, inertiaDegree_eq_mul D.surjective_deg (K := (K : Subgroup G))
      (L := (K' : Subgroup G)) hK, Nat.mul_assoc]

theorem reciprocity_galRestrict (hax : ClassFieldAxiom G A) [IsDiscreteModule G A]
    {K L K' L' : OpenSubgroup G} (hLK : L ≤ K) [((L : Subgroup G).subgroupOf K).Normal]
    (hL'K' : L' ≤ K') [((L' : Subgroup G).subgroupOf K').Normal] (hK : K' ≤ K) (hL : L' ≤ L)
    (q : (K' : Subgroup G) ⧸ (L' : Subgroup G).subgroupOf K') :
    D.reciprocity hLK hax (galRestrict hK hL q) =
      normTateZero hK hL hL'K' hLK (D.reciprocity hL'K' hax q) := by
  obtain ⟨s, rfl⟩ := exists_frobeniusLift_mk (D := D) hL'K' q
  set t := s.toBase hK with htdef
  have ht : t.deg = s.deg * relInertiaDegree D.deg K K' := rfl
  have hle : s.field L' hL'K' ≤ t.field L hLK := fun x hx => frobeniusClosure_mono hL s.elt hx
  obtain ⟨π, hπ⟩ := D.exists_prime (s.field L' hL'K')
  have hrel : relInertiaDegree D.deg (t.field L hLK) (s.field L' hL'K') = 1 := by
    have h1 := inertiaDegree_eq_mul D.surjective_deg
      (K := ((t.field L hLK : OpenSubgroup G) : Subgroup G))
      (L := ((s.field L' hL'K' : OpenSubgroup G) : Subgroup G)) hle
    rw [s.inertiaDegree_field hL'K', t.inertiaDegree_field hLK, ht,
      inertiaDegree_eq_mul D.surjective_deg (K := (K : Subgroup G)) (L := (K' : Subgroup G)) hK] at h1
    have hpos : 0 < s.deg * relInertiaDegree D.deg K K' * inertiaDegree D.deg K :=
      Nat.mul_pos (Nat.mul_pos s.deg_pos (Nat.pos_of_ne_zero (D.relInertiaDegree_ne_zero hK)))
        (Nat.pos_of_ne_zero (D.inertiaDegree_ne_zero K))
    refine Nat.eq_of_mul_eq_mul_right hpos ?_
    rw [one_mul]
    exact h1.symm.trans (Nat.mul_assoc _ _ _).symm
  set π0 := norm A ((t.field L hLK : OpenSubgroup G) : Subgroup G)
    ((s.field L' hL'K' : OpenSubgroup G) : Subgroup G) π with hπ0def
  have hπ0 : D.valuation (t.field L hLK) π0 = Multiplicative.ofAdd 1 := by
    rw [hπ0def, D.valuation_norm hle, hrel, pow_one, hπ]
  have e1 : galRestrict hK hL ((⟨s.elt, s.mem⟩ : (K' : Subgroup G)) :
      (K' : Subgroup G) ⧸ (L' : Subgroup G).subgroupOf K') =
      ((⟨t.elt, t.mem⟩ : (K : Subgroup G)) : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) := rfl
  rw [e1, D.reciprocity_mk_eq_norm hLK hax t hπ0, D.reciprocity_mk_eq_norm hL'K' hax s hπ,
    normTateZero_mk, hπ0def,
    norm_norm (M := ((s.field L' hL'K' : OpenSubgroup G) : Subgroup G)) (s.field_le hL'K') hK,
    norm_norm (M := ((s.field L' hL'K' : OpenSubgroup G) : Subgroup G)) hle (t.field_le hLK)]

end Restriction

section Conjugation

def FrobeniusLift.conj (ρ : G) {K : OpenSubgroup G} (s : D.FrobeniusLift K) :
    D.FrobeniusLift (conjOpen ρ K) where
  elt := ρ * s.elt * ρ⁻¹
  mem := ⟨s.elt, s.mem, rfl⟩
  deg := s.deg
  deg_pos := s.deg_pos
  deg_eq := by
    rw [map_conj_apply, s.deg_eq, coe_conjOpen, inertiaDegree_map_conj]

theorem FrobeniusLift.coe_field_conj (ρ : G) {K L : OpenSubgroup G} (hLK : L ≤ K)
    [((L : Subgroup G).subgroupOf K).Normal] (s : D.FrobeniusLift K) :
    (((s.conj ρ).field (conjOpen ρ L) (conjOpen_mono ρ hLK) : OpenSubgroup G) : Subgroup G) =
      ((s.field L hLK : OpenSubgroup G) : Subgroup G).map (MulAut.conj ρ).toMonoidHom :=
  (map_conj_frobeniusClosure D.deg (L : Subgroup G) s.elt ρ).symm

theorem reciprocity_galConj (hax : ClassFieldAxiom G A) [IsDiscreteModule G A] (σ : G)
    {K L : OpenSubgroup G} (hLK : L ≤ K) [((L : Subgroup G).subgroupOf K).Normal]
    (q : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) :
    D.reciprocity (conjOpen_mono σ hLK) hax (galConj σ K L q) =
      tateZeroConj σ K L (D.reciprocity hLK hax q) := by
  obtain ⟨s, rfl⟩ := exists_frobeniusLift_mk (D := D) hLK q
  set t := s.conj σ with htdef
  have hfield := s.coe_field_conj σ hLK
  obtain ⟨π, hπ⟩ := D.exists_prime (s.field L hLK)
  let π' : fixedModule A (((t.field (conjOpen σ L) (conjOpen_mono σ hLK)) : OpenSubgroup G) :
      Subgroup G) := ⟨σ • (π : A), hfield ▸ smul_mem_fixedModule π.2 σ⟩
  have hπ' : D.valuation (t.field (conjOpen σ L) (conjOpen_mono σ hLK)) π' = Multiplicative.ofAdd 1 := by
    rw [valuation_conj σ hfield π π' rfl, hπ]
  have e1 : galConj σ K L ((⟨s.elt, s.mem⟩ : (K : Subgroup G)) :
      (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) =
      ((⟨t.elt, t.mem⟩ : ((conjOpen σ K : OpenSubgroup G) : Subgroup G)) : _ ⧸ _) := rfl
  rw [e1, D.reciprocity_mk_eq_norm (conjOpen_mono σ hLK) hax t hπ',
    D.reciprocity_mk_eq_norm hLK hax s hπ, tateZeroConj_mk]
  congr 1
  apply Subtype.ext
  show _ = σ • (norm A (K : Subgroup G) ((s.field L hLK : OpenSubgroup G) : Subgroup G) π : A)
  rw [smul_norm_conjOpen σ K (s.field L hLK) π]
  have : ((((s.field L hLK : OpenSubgroup G) : Subgroup G).map (MulAut.conj σ).toMonoidHom).subgroupOf
      ((conjOpen σ K : OpenSubgroup G) : Subgroup G)).FiniteIndex := by
    rw [← hfield]
    infer_instance
  exact coe_norm_congr rfl hfield _

end Conjugation

end ClassFieldData

end GroundTheory.LocalField.Abstract
