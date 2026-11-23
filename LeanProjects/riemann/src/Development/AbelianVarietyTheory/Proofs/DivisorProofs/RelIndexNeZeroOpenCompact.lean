import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PointSide
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VolConjEqOneOfMassCNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MassMulVolumeCommensurable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VolEqIdxRatio
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumDoubleCosetFoldIntermediateSubgroupStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedCentralizerMassNeZeroOfMemSupportStatement

open GlobalTheory.LKCount

noncomputable section
open scoped Classical

namespace GlobalTheory.LKCountPoint

section Gen
variable {G : Type} [Group G]

theorem mem_map_conj {K : Subgroup G} {a z : G} :
    z ∈ K.map (MulAut.conj a).toMonoidHom ↔ a⁻¹ * z * a ∈ K := by
  rw [Subgroup.mem_map_equiv]
  simp [MulAut.conj_symm_apply]

theorem map_conj_map_conj (K : Subgroup G) (a b : G) :
    (K.map (MulAut.conj a).toMonoidHom).map (MulAut.conj b).toMonoidHom =
      K.map (MulAut.conj (b * a)).toMonoidHom := by
  ext z
  simp only [mem_map_conj, mul_inv_rev, mul_assoc]

theorem map_conj_inf_of_mem {T : Subgroup G} {t : G} (ht : t ∈ T) (K : Subgroup G) :
    (T ⊓ K).map (MulAut.conj t).toMonoidHom = T ⊓ K.map (MulAut.conj t).toMonoidHom := by
  ext z
  simp only [mem_map_conj, Subgroup.mem_inf]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    have := T.mul_mem (T.mul_mem ht h1) (T.inv_mem ht)
    simpa [mul_assoc] using this
  · rintro ⟨h1, h2⟩
    exact ⟨T.mul_mem (T.mul_mem (T.inv_mem ht) h1) ht, h2⟩

theorem relIndex_inf_inf_ne_zero (H : Subgroup G) {U K : Subgroup G} (h : U.relIndex K ≠ 0) :
    (H ⊓ U).relIndex (H ⊓ K) ≠ 0 := by
  have := Subgroup.relIndex_inter_ne_zero h H
  rwa [inf_comm U H, inf_comm K H] at this

end Gen

section Prod
variable {G₁ G₂ : Type} [Group G₁] [Group G₂]

theorem prod_map_conj (A : Subgroup G₁) (B : Subgroup G₂) (x : G₁ × G₂) :
    (A.prod B).map (MulAut.conj x).toMonoidHom =
      (A.map (MulAut.conj x.1).toMonoidHom).prod (B.map (MulAut.conj x.2).toMonoidHom) := by
  ext z
  simp only [mem_map_conj, Subgroup.mem_prod, Prod.fst_mul, Prod.snd_mul, Prod.fst_inv, Prod.snd_inv]

theorem twCent_prod (θ₁ : G₁ →* G₁) (θ₂ : G₂ →* G₂) (a : G₁) (b : G₂) :
    GlobalTheory.BCT.twCent (θ₁.prodMap θ₂) (a, b) = (GlobalTheory.BCT.twCent θ₁ a).prod (GlobalTheory.BCT.twCent θ₂ b) := by
  ext z
  rw [Subgroup.mem_prod]
  show z * (a, b) = (a, b) * (θ₁.prodMap θ₂) z ↔ z.1 * a = a * θ₁ z.1 ∧ z.2 * b = b * θ₂ z.2
  rw [Prod.ext_iff]
  exact Iff.rfl

theorem relIndex_prod (A C : Subgroup G₁) (B D : Subgroup G₂) :
    (A.prod B).relIndex (C.prod D) = A.relIndex C * B.relIndex D := by
  have e : (A.prod B).subgroupOf (C.prod D) =
      ((A.subgroupOf C).prod (B.subgroupOf D)).comap (Subgroup.prodEquiv C D).toMonoidHom := by
    ext z
    exact Iff.rfl
  rw [Subgroup.relIndex, e, Subgroup.index_comap_of_surjective _ (Subgroup.prodEquiv C D).surjective,
    Subgroup.index_prod]
  rfl

theorem vol_prod (C₁ H₁ : Subgroup G₁) (C₂ H₂ : Subgroup G₂) :
    vol (C₁.prod C₂) (H₁.prod H₂) = vol C₁ H₁ * vol C₂ H₂ := by
  unfold vol
  rw [relIndex_prod, relIndex_prod]
  push_cast
  rw [div_mul_div_comm]

theorem stab_eq {Γ : Type} [Group Γ] (ι₁ : Γ →* G₁) (ι₂ : Γ →* G₂) (K₁ : Subgroup G₁) (K₂ : Subgroup G₂)
    (x : G₁ × G₂) :
    stab ι₁ ι₂ K₁ K₂ x = ((K₁.prod K₂).map (MulAut.conj x).toMonoidHom).comap (ι₁.prod ι₂) := by
  rw [prod_map_conj]
  ext g
  exact Iff.rfl

theorem card_stab {Γ : Type} [Group Γ] (ι₁ : Γ →* G₁) (ι₂ : Γ →* G₂) (K₁ : Subgroup G₁) (K₂ : Subgroup G₂)
    (hι : Function.Injective (ι₁.prod ι₂)) (x : G₁ × G₂) :
    Nat.card (stab ι₁ ι₂ K₁ K₂ x) =
      Nat.card ((ι₁.prod ι₂).range ⊓ (K₁.prod K₂).map (MulAut.conj x).toMonoidHom : Subgroup (G₁ × G₂)) := by
  rw [stab_eq, ← Subgroup.map_comap_eq]
  exact Nat.card_congr (Subgroup.equivMapOfInjective _ _ hι).toEquiv

theorem finite_inter {Γ : Type} [Group Γ] (ι₁ : Γ →* G₁) (ι₂ : Γ →* G₂) (K₁ : Subgroup G₁) (K₂ : Subgroup G₂)
    (x : G₁ × G₂) (h : Finite (stab ι₁ ι₂ K₁ K₂ x)) :
    (((ι₁.prod ι₂).range ⊓ (K₁.prod K₂).map (MulAut.conj x).toMonoidHom : Subgroup (G₁ × G₂)) :
      Set (G₁ × G₂)).Finite := by
  rw [← Subgroup.map_comap_eq, ← stab_eq, Subgroup.coe_map]
  exact Set.Finite.image _ (Set.toFinite _)

end Prod

section Core
variable {G : Type} [Group G]

theorem map_conj_one (A : Subgroup G) : A.map (MulAut.conj (1 : G)).toMonoidHom = A := by
  ext z
  simp [mem_map_conj]

theorem vol_self (A : Subgroup G) : vol A A = 1 := by
  simp [vol, Subgroup.relIndex_self]

theorem fold_sum (Γ' T K : Subgroup G) (F : G → ℂ) (hΓT : Γ' ≤ T)
    (hF : ∀ t ∈ T, ∀ x, ∀ k ∈ K, F (t * x * k) = F x)
    (hfin : ∀ x : G, ((Γ' ⊓ K.map (MulAut.conj x).toMonoidHom : Subgroup G) : Set G).Finite)
    (hsupp : {q : DoubleCoset.Quotient (Γ' : Set G) (K : Set G) | F (Quotient.out q) ≠ 0}.Finite) :
    ∑ᶠ q : DoubleCoset.Quotient (Γ' : Set G) (K : Set G),
        ((Nat.card (Γ' ⊓ K.map (MulAut.conj (Quotient.out q)).toMonoidHom : Subgroup G) : ℕ) : ℂ)⁻¹ *
          F (Quotient.out q) =
      ∑ᶠ y : DoubleCoset.Quotient (T : Set G) (K : Set G),
        ((massC Γ' T (T ⊓ K.map (MulAut.conj (Quotient.out y)).toMonoidHom) : ℚ) : ℂ) * F (Quotient.out y) :=
  GlobalTheory.T.finsum_doubleCoset_fold_intermediate_subgroup Γ' T K F hΓT hF hfin hsupp

theorem massC_ne_zero_of_ne (Γ' T K : Subgroup G) (F : G → ℂ) (hΓT : Γ' ≤ T)
    (hF : ∀ t ∈ T, ∀ x, ∀ k ∈ K, F (t * x * k) = F x)
    (hfin : ∀ x : G, ((Γ' ⊓ K.map (MulAut.conj x).toMonoidHom : Subgroup G) : Set G).Finite)
    (hsupp : {q : DoubleCoset.Quotient (Γ' : Set G) (K : Set G) | F (Quotient.out q) ≠ 0}.Finite)
    (y : G) (hy : F y ≠ 0) :
    massC Γ' T (T ⊓ K.map (MulAut.conj y).toMonoidHom) ≠ 0 :=
  GlobalTheory.T.twistedCentralizerMass_ne_zero_of_mem_support Γ' T K F hΓT hF hfin hsupp y hy

variable [TopologicalSpace G] [IsTopologicalGroup G]

end Core

end GlobalTheory.LKCountPoint
