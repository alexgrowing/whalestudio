import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.Ord2

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime]

def MemE (c : Coef l) (x : Qbar l) : Prop := ∃ k : ℕ, (l : Qbar l) ^ k * x ∈ c.O

def VecE (c : Coef l) (y : Fin 2 → Qbar l) : Prop := ∃ k : ℕ, ∀ i, (l : Qbar l) ^ k * y i ∈ c.O

theorem natPow_mem (c : Coef l) (k : ℕ) : (l : Qbar l) ^ k ∈ c.O :=
  c.O.pow_mem (c.O.natCast_mem l) k

theorem pow_mul_mem_add (c : Coef l) {x : Qbar l} {k : ℕ} (h : (l : Qbar l) ^ k * x ∈ c.O) (j : ℕ) :
    (l : Qbar l) ^ (k + j) * x ∈ c.O := by
  rw [pow_add, mul_comm ((l : Qbar l) ^ k), mul_assoc]
  exact c.O.mul_mem (natPow_mem c j) h

theorem memE_add {c : Coef l} {x y : Qbar l} (hx : MemE c x) (hy : MemE c y) : MemE c (x + y) := by
  obtain ⟨k, hk⟩ := hx
  obtain ⟨j, hj⟩ := hy
  refine ⟨k + j, ?_⟩
  have h2 := pow_mul_mem_add c hj k
  rw [add_comm j k] at h2
  rw [mul_add]
  exact c.O.add_mem (pow_mul_mem_add c hk j) h2

theorem memE_neg {c : Coef l} {x : Qbar l} (hx : MemE c x) : MemE c (-x) := by
  obtain ⟨k, hk⟩ := hx
  exact ⟨k, by rw [mul_neg]; exact c.O.neg_mem hk⟩

theorem vecE_add {c : Coef l} {x y : Fin 2 → Qbar l} (hx : VecE c x) (hy : VecE c y) : VecE c (x + y) := by
  obtain ⟨k, hk⟩ := hx
  obtain ⟨j, hj⟩ := hy
  refine ⟨k + j, fun i => ?_⟩
  have h2 := pow_mul_mem_add c (hj i) k
  rw [add_comm j k] at h2
  rw [Pi.add_apply, mul_add]
  exact c.O.add_mem (pow_mul_mem_add c (hk i) j) h2

theorem vecE_neg {c : Coef l} {x : Fin 2 → Qbar l} (hx : VecE c x) : VecE c (-x) := by
  obtain ⟨k, hk⟩ := hx
  exact ⟨k, fun i => by rw [Pi.neg_apply, mul_neg]; exact c.O.neg_mem (hk i)⟩

def divSelCoc (c : Coef l) (W : R2 Ω l) (S : Finset Pl) (A : ValuationSubring Ω) :
    AddSubgroup (G ℚ Ω → Fin 2 → Qbar l) where
  carrier := {z | (∃ k : ℕ, ∀ s i, (l : Qbar l) ^ k * z s i ∈ c.O) ∧
    (∀ s t i, z (s * t) i - z s i - (mat W s *ᵥ z t) i ∈ c.O) ∧
    (∀ s, ∀ᶠ t in nhds s, ∀ i, z t i - z s i ∈ c.O) ∧
    (∀ a ∈ (toGS Ω (S : Set Pl)).ker, ∀ i, z a i ∈ c.O) ∧
    (∀ q ∈ S, ((l : ℕ) : 𝓞 ℚ) ∉ q.asIdeal → ∀ B : ValuationSubring Ω, IsPlaceOver B q →
      ∃ y : Fin 2 → Qbar l, VecE c y ∧ ∀ s ∈ Ine (F := ℚ) B, ∀ i, z s i - (mat W s *ᵥ y - y) i ∈ c.O) ∧
    (∃ y : Qbar l, MemE c y ∧ ∀ s ∈ Dec (F := ℚ) A, z s 1 - (mat W s 1 1 * y - y) ∈ c.O)}
  add_mem' := by
    rintro z w ⟨⟨k, hk⟩, h2, h3, h4, h5, ⟨y, hy, h6⟩⟩ ⟨⟨k', hk'⟩, h2', h3', h4', h5', ⟨y', hy', h6'⟩⟩
    refine ⟨⟨k + k', fun s i => ?_⟩, fun s t i => ?_, fun s => ?_, fun a ha i => ?_, fun q hq hl B hB => ?_,
      ⟨y + y', memE_add hy hy', fun s hs => ?_⟩⟩
    · have h := pow_mul_mem_add c (hk' s i) k
      rw [add_comm k' k] at h
      rw [Pi.add_apply, Pi.add_apply, mul_add]
      exact c.O.add_mem (pow_mul_mem_add c (hk s i) k') h
    · have e : (z + w) (s * t) i - (z + w) s i - (mat W s *ᵥ (z + w) t) i =
          (z (s * t) i - z s i - (mat W s *ᵥ z t) i) + (w (s * t) i - w s i - (mat W s *ᵥ w t) i) := by
        simp only [Pi.add_apply, Matrix.mulVec_add]; ring
      rw [e]; exact c.O.add_mem (h2 s t i) (h2' s t i)
    · filter_upwards [h3 s, h3' s] with t ht ht' i
      have e : (z + w) t i - (z + w) s i = (z t i - z s i) + (w t i - w s i) := by
        simp only [Pi.add_apply]; ring
      rw [e]; exact c.O.add_mem (ht i) (ht' i)
    · rw [Pi.add_apply, Pi.add_apply]; exact c.O.add_mem (h4 a ha i) (h4' a ha i)
    · obtain ⟨u, hu, hu'⟩ := h5 q hq hl B hB
      obtain ⟨u', hv, hv'⟩ := h5' q hq hl B hB
      refine ⟨u + u', vecE_add hu hv, fun s hs i => ?_⟩
      have e : (z + w) s i - (mat W s *ᵥ (u + u') - (u + u')) i =
          (z s i - (mat W s *ᵥ u - u) i) + (w s i - (mat W s *ᵥ u' - u') i) := by
        simp only [Pi.add_apply, Pi.sub_apply, Matrix.mulVec_add]; ring
      rw [e]; exact c.O.add_mem (hu' s hs i) (hv' s hs i)
    · have e : (z + w) s 1 - (mat W s 1 1 * (y + y') - (y + y')) =
          (z s 1 - (mat W s 1 1 * y - y)) + (w s 1 - (mat W s 1 1 * y' - y')) := by
        simp only [Pi.add_apply]; ring
      rw [e]; exact c.O.add_mem (h6 s hs) (h6' s hs)
  zero_mem' := by
    refine ⟨⟨0, fun s i => by simp⟩, fun s t i => by simp, fun s => Filter.Eventually.of_forall fun t i => by simp,
      fun a _ i => by simp, fun q _ _ B _ => ⟨0, ⟨0, fun i => by simp⟩, fun s _ i => by simp⟩, ⟨0, ⟨0, by simp⟩, fun s _ => by simp⟩⟩
  neg_mem' := by
    rintro z ⟨⟨k, hk⟩, h2, h3, h4, h5, ⟨y, hy, h6⟩⟩
    refine ⟨⟨k, fun s i => ?_⟩, fun s t i => ?_, fun s => ?_, fun a ha i => ?_, fun q hq hl B hB => ?_,
      ⟨-y, memE_neg hy, fun s hs => ?_⟩⟩
    · rw [Pi.neg_apply, Pi.neg_apply, mul_neg]; exact c.O.neg_mem (hk s i)
    · have e : (-z) (s * t) i - (-z) s i - (mat W s *ᵥ (-z) t) i = -(z (s * t) i - z s i - (mat W s *ᵥ z t) i) := by
        simp only [Pi.neg_apply, Matrix.mulVec_neg]; ring
      rw [e]; exact c.O.neg_mem (h2 s t i)
    · filter_upwards [h3 s] with t ht i
      have e : (-z) t i - (-z) s i = -(z t i - z s i) := by simp only [Pi.neg_apply]; ring
      rw [e]; exact c.O.neg_mem (ht i)
    · rw [Pi.neg_apply, Pi.neg_apply]; exact c.O.neg_mem (h4 a ha i)
    · obtain ⟨u, hu, hu'⟩ := h5 q hq hl B hB
      refine ⟨-u, vecE_neg hu, fun s hs i => ?_⟩
      have e : (-z) s i - (mat W s *ᵥ (-u) - (-u)) i = -(z s i - (mat W s *ᵥ u - u) i) := by
        simp only [Pi.neg_apply, Pi.sub_apply, Matrix.mulVec_neg]; ring
      rw [e]; exact c.O.neg_mem (hu' s hs i)
    · have e : (-z) s 1 - (mat W s 1 1 * (-y) - (-y)) = -(z s 1 - (mat W s 1 1 * y - y)) := by
        simp only [Pi.neg_apply]; ring
      rw [e]; exact c.O.neg_mem (h6 s hs)

def divCob (c : Coef l) (W : R2 Ω l) : AddSubgroup (G ℚ Ω → Fin 2 → Qbar l) where
  carrier := {z | ∃ y : Fin 2 → Qbar l, VecE c y ∧ ∀ s i, z s i - (mat W s *ᵥ y - y) i ∈ c.O}
  add_mem' := by
    rintro z w ⟨u, hu, hu'⟩ ⟨u', hv, hv'⟩
    refine ⟨u + u', vecE_add hu hv, fun s i => ?_⟩
    have e : (z + w) s i - (mat W s *ᵥ (u + u') - (u + u')) i =
        (z s i - (mat W s *ᵥ u - u) i) + (w s i - (mat W s *ᵥ u' - u') i) := by
      simp only [Pi.add_apply, Pi.sub_apply, Matrix.mulVec_add]; ring
    rw [e]; exact c.O.add_mem (hu' s i) (hv' s i)
  zero_mem' := ⟨0, ⟨0, fun i => by simp⟩, fun s i => by simp⟩
  neg_mem' := by
    rintro z ⟨u, hu, hu'⟩
    refine ⟨-u, vecE_neg hu, fun s i => ?_⟩
    have e : (-z) s i - (mat W s *ᵥ (-u) - (-u)) i = -(z s i - (mat W s *ᵥ u - u) i) := by
      simp only [Pi.neg_apply, Pi.sub_apply, Matrix.mulVec_neg]; ring
    rw [e]; exact c.O.neg_mem (hu' s i)

abbrev DivSel (c : Coef l) (W : R2 Ω l) (S : Finset Pl) (A : ValuationSubring Ω) : Type :=
  ↥(divSelCoc c W S A) ⧸ (divCob c W).addSubgroupOf (divSelCoc c W S A)

theorem divSel_torsion (c : Coef l) (W : R2 Ω l) (S : Finset Pl) (A : ValuationSubring Ω) :
    ∀ x : DivSel c W S A, ∃ n : ℕ, l ^ n • x = 0 := by
  intro x
  induction x using QuotientAddGroup.induction_on with
  | H z =>
    obtain ⟨k, hk⟩ := z.2.1
    refine ⟨k, ?_⟩
    rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
    refine ⟨0, ⟨0, fun i => by simp⟩, fun s i => ?_⟩
    simp only [AddSubgroup.coe_nsmul, Pi.smul_apply, nsmul_eq_mul, Matrix.mulVec_zero, sub_zero, Pi.zero_apply]
    push_cast
    exact hk s i

end GlobalTheory.Ord2

end
