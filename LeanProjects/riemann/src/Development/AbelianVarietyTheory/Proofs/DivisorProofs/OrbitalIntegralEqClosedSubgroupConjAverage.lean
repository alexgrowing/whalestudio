import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ParP
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralTwistedConjInvariant
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.IwRed

open GlobalTheory.LeviDesc GlobalTheory.TwOrbConj

theorem avg_const {H : Type} [Group H] (c : ℂ) : avg (fun _ : H => c) = c := by
  have hR : rStab (fun _ : H => c) = ⊤ := by
    ext k; simp [mem_rStab]
  unfold avg
  simp only
  rw [hR, Subgroup.index_top]
  haveI : Unique (H ⧸ (⊤ : Subgroup H)) :=
    ⟨⟨QuotientGroup.mk 1⟩, fun a => QuotientGroup.induction_on a fun x => QuotientGroup.eq.2 (Subgroup.mem_top _)⟩
  rw [finsum_unique]
  simp

variable {G : Type} [Group G]

theorem avg_cavg (K P : Subgroup G) (δ : G) (hδ : δ ∈ P) (f : G → ℂ) (p : P) :
    avg (fun k : K.subgroupOf P => cavg K f (((p * k)⁻¹ * ⟨δ, hδ⟩ * (p * k) : P) : G)) =
      avg (fun k : K => f (((p : G) * k)⁻¹ * δ * ((p : G) * k))) := by
  have h : ∀ k : K.subgroupOf P, cavg K f (((p * k)⁻¹ * ⟨δ, hδ⟩ * (p * k) : P) : G) =
      avg (fun k : K => f (((p : G) * k)⁻¹ * δ * ((p : G) * k))) := by
    intro k
    have hk : ((k : P) : G) ∈ K := k.2
    unfold cavg
    rw [← avg_left (fun k' : K => f (((p : G) * k')⁻¹ * δ * ((p : G) * k'))) ⟨_, hk⟩]
    congr 1
    funext k'
    congr 1
    simp only [Subgroup.coe_mul, InvMemClass.coe_inv, _root_.mul_inv_rev]
    group
  simp_rw [h]
  exact avg_const _

theorem mem_twCent_sub (P : Subgroup G) (δ : G) (hδ : δ ∈ P) (x : P) :
    x ∈ twCent (MonoidHom.id P) ⟨δ, hδ⟩ ↔ (x : G) ∈ twCent (MonoidHom.id G) δ := by
  rw [mem_twCent, mem_twCent, Subtype.ext_iff]
  simp

theorem inf_eq_comap (K P : Subgroup G) (δ : G) (hδ : δ ∈ P) (p : P) :
    twCent (MonoidHom.id P) ⟨δ, hδ⟩ ⊓ (K.subgroupOf P).map (MulAut.conj p).toMonoidHom =
      (twCent (MonoidHom.id G) δ ⊓ K.map (MulAut.conj (p : G)).toMonoidHom).comap P.subtype := by
  ext x
  simp only [Subgroup.mem_inf, Subgroup.mem_comap, Subgroup.mem_map_equiv, mem_twCent_sub, MulAut.conj_symm_apply,
    Subgroup.mem_subgroupOf, Subgroup.coe_subtype, Subgroup.coe_mul, InvMemClass.coe_inv]

variable [TopologicalSpace G] [IsTopologicalGroup G]

theorem cptPart_map_sub (P : Subgroup G) (hP : IsClosed (P : Set G)) (δ : G) (hδ : δ ∈ P)
    (hT : twCent (MonoidHom.id G) δ ≤ P) :
    (cptPart (twCent (MonoidHom.id P) ⟨δ, hδ⟩)).map P.subtype = cptPart (twCent (MonoidHom.id G) δ) := by
  unfold cptPart
  rw [MonoidHom.map_closure]
  congr 1
  have hc : ∀ x : P, IsCompact (closure (Subgroup.zpowers x : Set P)) ↔
      IsCompact (closure (Subgroup.zpowers (x : G) : Set G)) := by
    intro x
    rw [(hP.isClosedEmbedding_subtypeVal).isInducing.isCompact_iff,
      ← (hP.isClosedEmbedding_subtypeVal).closure_image_eq]
    have : (Subtype.val '' (Subgroup.zpowers x : Set P)) = (Subgroup.zpowers (x : G) : Set G) := by
      rw [← Subgroup.coe_subtype, ← Subgroup.coe_map, MonoidHom.map_zpowers]
    first
      | (convert Iff.rfl using 3; exact this.symm)
      | (convert Iff.rfl using 3; exact this)
      | exact this ▸ Iff.rfl
  ext y
  constructor
  · rintro ⟨x, ⟨hx, hx'⟩, rfl⟩
    exact ⟨(mem_twCent_sub P δ hδ x).1 hx, (hc x).1 hx'⟩
  · rintro ⟨hy, hy'⟩
    exact ⟨⟨y, hT hy⟩, ⟨(mem_twCent_sub P δ hδ _).2 hy, (hc _).2 hy'⟩, rfl⟩

end GlobalTheory.IwRed

namespace GlobalTheory.IwRed

open GlobalTheory.LeviDesc GlobalTheory.TwOrbConj

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

theorem relIndex_sub (K P : Subgroup G) (hP : IsClosed (P : Set G)) (δ : G) (hδ : δ ∈ P)
    (hT : twCent (MonoidHom.id G) δ ≤ P) (p : P) :
    (twCent (MonoidHom.id P) ⟨δ, hδ⟩ ⊓ (K.subgroupOf P).map (MulAut.conj p).toMonoidHom).relIndex
        (cptPart (twCent (MonoidHom.id P) ⟨δ, hδ⟩)) =
      (twCent (MonoidHom.id G) δ ⊓ K.map (MulAut.conj (p : G)).toMonoidHom).relIndex
        (cptPart (twCent (MonoidHom.id G) δ)) := by
  rw [inf_eq_comap, Subgroup.relIndex_comap, cptPart_map_sub P hP δ hδ hT]

theorem summand_sub (K P : Subgroup G) (hP : IsClosed (P : Set G)) (δ : G) (hδ : δ ∈ P)
    (hT : twCent (MonoidHom.id G) δ ≤ P) (f : G → ℂ) (p : P) :
    summand (MonoidHom.id P) (K.subgroupOf P) ⟨δ, hδ⟩ (fun x : P => cavg K f (x : G)) p =
      summand (MonoidHom.id G) K δ f p := by
  unfold summand
  rw [relIndex_sub K P hP δ hδ hT p]
  congr 1
  simpa using avg_cavg K P δ hδ f p

def dcMap (K P : Subgroup G) (δ : G) (hδ : δ ∈ P) :
    DoubleCoset.Quotient (twCent (MonoidHom.id P) ⟨δ, hδ⟩ : Set P) (K.subgroupOf P : Set P) →
      DoubleCoset.Quotient (twCent (MonoidHom.id G) δ : Set G) (K : Set G) :=
  fun q => DoubleCoset.mk _ K ((Quotient.out q : P) : G)

theorem dcMap_bij (K P : Subgroup G) (δ : G) (hδ : δ ∈ P) (hT : twCent (MonoidHom.id G) δ ≤ P)
    (hPK : ∀ g : G, ∃ p ∈ P, ∃ k ∈ K, g = p * k) : Function.Bijective (dcMap K P δ hδ) := by
  constructor
  · intro q₁ q₂ h
    obtain ⟨t, ht, k, hk, he⟩ := (DoubleCoset.eq _ _ _ _).1 h
    have htP : t ∈ P := hT ht
    have hkP : k ∈ P := by
      have : k = ((Quotient.out q₁ : P) : G)⁻¹ * t⁻¹ * ((Quotient.out q₂ : P) : G) := by rw [he]; group
      rw [this]
      exact P.mul_mem (P.mul_mem (P.inv_mem (Quotient.out q₁).2) (P.inv_mem htP)) (Quotient.out q₂).2
    rw [← DoubleCoset.out_eq' _ _ q₁, ← DoubleCoset.out_eq' _ _ q₂, DoubleCoset.eq]
    refine ⟨⟨t, htP⟩, (mem_twCent_sub P δ hδ _).2 ht, ⟨k, hkP⟩, (Subgroup.mem_subgroupOf).2 hk, ?_⟩
    exact Subtype.ext (by simpa using he)
  · intro q
    obtain ⟨p, hp, k, hk, hg⟩ := hPK (Quotient.out q)
    refine ⟨DoubleCoset.mk _ _ (⟨p, hp⟩ : P), ?_⟩
    obtain ⟨t, ht, k', hk', he⟩ := (DoubleCoset.eq _ _ _ _).1
      (DoubleCoset.out_eq' (twCent (MonoidHom.id P) ⟨δ, hδ⟩) (K.subgroupOf P) (DoubleCoset.mk _ _ (⟨p, hp⟩ : P))).symm
    rw [← DoubleCoset.out_eq' _ _ q]
    show DoubleCoset.mk _ K _ = _
    rw [DoubleCoset.eq]
    refine ⟨(t : G)⁻¹, (twCent (MonoidHom.id G) δ).inv_mem ((mem_twCent_sub P δ hδ t).1 ht), ((k' : P) : G)⁻¹ * k,
      K.mul_mem (K.inv_mem ((Subgroup.mem_subgroupOf).1 hk')) hk, ?_⟩
    rw [hg]
    have he' := congrArg (fun x : P => (x : G)) he
    simp only [Subgroup.coe_mul] at he'
    rw [he']
    group

theorem twOrb_sub : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (K P : Subgroup G),
    IsOpen (K : Set G) → IsCompact (K : Set G) → IsClosed (P : Set G) → (∀ g : G, ∃ p ∈ P, ∃ k ∈ K, g = p * k) →
    ∀ (δ : G) (hδ : δ ∈ P), twCent (MonoidHom.id G) δ ≤ P → ∀ f : G → ℂ,
    (∃ K' : Subgroup G, IsOpen (K' : Set G) ∧ IsHecke K' f) →
    twOrb (MonoidHom.id G) K δ f = twOrb (MonoidHom.id P) (K.subgroupOf P) ⟨δ, hδ⟩ (fun p => GlobalTheory.LeviDesc.cavg K f (p : G)) := by
  intro G _ _ _ K P _ _ hP hPK δ hδ hT f _
  rw [twOrb_eq, twOrb_eq]
  rw [← finsum_comp_equiv (Equiv.ofBijective _ (dcMap_bij K P δ hδ hT hPK))]
  refine finsum_congr fun q => ?_
  rw [summand_sub K P hP δ hδ hT f]
  show summand _ K δ f (Quotient.out (DoubleCoset.mk _ K ((Quotient.out q : P) : G))) = _
  obtain ⟨t, ht, k, hk, he⟩ := (DoubleCoset.eq _ _ _ _).1
    (DoubleCoset.out_eq' (twCent (MonoidHom.id G) δ) K (DoubleCoset.mk _ K ((Quotient.out q : P) : G))).symm
  rw [he, summand_rep _ K δ f _ ht hk]

end GlobalTheory.IwRed
