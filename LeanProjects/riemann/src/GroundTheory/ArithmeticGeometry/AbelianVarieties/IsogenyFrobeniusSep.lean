import Mathlib
import GroundTheory.ArithmeticGeometry.AbelianVarieties.IsogenyFrobenius

namespace GroundTheory.Arith.Abelian

open Polynomial WeierstrassCurve WeierstrassCurve.Affine IntermediateField

variable {F : Type*} [Field F] (E : WeierstrassCurve F) (p : ℕ) [hp : Fact p.Prime] [CharP F p]

noncomputable def powAdjoin (M : IntermediateField F E.toAffine.FunctionField) (a : ℕ) :
    IntermediateField M E.toAffine.FunctionField :=
  M⟮genX E ^ p ^ a, genY E ^ p ^ a⟯

theorem powAdjoin_succ_eq_top (M : IntermediateField F E.toAffine.FunctionField)
    (h1 : powAdjoin E p M 1 = ⊤) {a : ℕ} (ha : powAdjoin E p M a = ⊤) :
    powAdjoin E p M (a + 1) = ⊤ := by
  set T := powAdjoin E p M (a + 1) with hT
  let Q : IntermediateField M E.toAffine.FunctionField :=
    (T.toSubfield.comap (frobenius E.toAffine.FunctionField p)).toIntermediateField fun m => by
      show (algebraMap M E.toAffine.FunctionField m) ^ p ∈ T
      rw [← map_pow]
      exact IntermediateField.algebraMap_mem T _
  have hQ : powAdjoin E p M a ≤ Q := by
    rw [powAdjoin, adjoin_le_iff]
    rintro w (rfl | rfl)
    · show (genX E ^ p ^ a) ^ p ∈ T
      rw [← pow_mul, ← pow_succ]
      exact subset_adjoin _ _ (by simp)
    · show (genY E ^ p ^ a) ^ p ∈ T
      rw [← pow_mul, ← pow_succ]
      exact subset_adjoin _ _ (by simp)
  have hall : ∀ z : E.toAffine.FunctionField, z ^ p ∈ T := fun z =>
    hQ (show z ∈ powAdjoin E p M a by rw [ha]; trivial)
  have h1le : powAdjoin E p M 1 ≤ T := by
    rw [powAdjoin, adjoin_le_iff]
    rintro w (rfl | rfl)
    · rw [pow_one]; exact hall _
    · rw [pow_one]; exact hall _
  rw [h1] at h1le
  exact top_le_iff.mp h1le

variable [PerfectRing F p]

theorem le_powField_of_finSepDegree_lt (M : IntermediateField F E.toAffine.FunctionField)
    [FiniteDimensional M E.toAffine.FunctionField]
    (h : Field.finSepDegree M E.toAffine.FunctionField <
      Module.finrank M E.toAffine.FunctionField) : M ≤ powField E p := by
  by_contra hM
  set N := M ⊔ powField E p
  have t := relfinrank_mul_relfinrank (le_sup_right : powField E p ≤ N) (le_top : N ≤ ⊤)
  have hp' : relfinrank (powField E p) ⊤ = p := by rw [relfinrank_top_right, finrank_powField]
  rw [hp'] at t
  rcases (Nat.prime_mul_iff.mp (t ▸ hp.out)) with ⟨-, h1⟩ | ⟨-, h1⟩
  · have hN : N = ⊤ := top_le_iff.mp ((relfinrank_eq_one_iff).mp h1)
    have hT1 : powAdjoin E p M 1 = ⊤ := by
      rw [← IntermediateField.restrictScalars_eq_top_iff (K := F)]
      refine top_le_iff.mp ?_
      rw [← hN]
      refine sup_le ?_ ?_
      · intro m hm
        exact (powAdjoin E p M 1).algebraMap_mem ⟨m, hm⟩
      · rw [powField, adjoin_le_iff]
        rintro w (rfl | rfl)
        · exact (subset_adjoin _ _ (by simp) : genX E ^ p ∈ powAdjoin E p M 1)
        · exact (subset_adjoin _ _ (by simp) : genY E ^ p ∈ powAdjoin E p M 1)
    have hall : ∀ a, 1 ≤ a → powAdjoin E p M a = ⊤ := fun a ha =>
      Nat.le_induction hT1 (fun n _ ih => powAdjoin_succ_eq_top E p M hT1 ih) a ha
    set S := separableClosure M E.toAffine.FunctionField
    haveI : CharP S p := charP_of_injective_algebraMap (algebraMap F S).injective p
    haveI : ExpChar S p := ExpChar.prime hp.out
    obtain ⟨nx, hnx⟩ := IsPurelyInseparable.pow_mem S p (genX E)
    obtain ⟨ny, hny⟩ := IsPurelyInseparable.pow_mem S p (genY E)
    have hmem : ∀ (z : E.toAffine.FunctionField) (n a : ℕ),
        z ^ p ^ n ∈ (algebraMap S E.toAffine.FunctionField).range → n ≤ a → z ^ p ^ a ∈ S := by
      intro z n a hz hn
      obtain ⟨s, hs⟩ := hz
      have e : z ^ p ^ a = (z ^ p ^ n) ^ p ^ (a - n) := by
        rw [← pow_mul, ← pow_add, Nat.add_sub_cancel' hn]
      rw [e, ← hs]
      exact pow_mem s.2 _
    have hle : powAdjoin E p M (nx + ny + 1) ≤ S := by
      rw [powAdjoin, adjoin_le_iff]
      rintro w (rfl | rfl)
      · exact hmem _ nx _ hnx (by omega)
      · exact hmem _ ny _ hny (by omega)
    rw [hall _ (by omega), top_le_iff, separableClosure.eq_top_iff] at hle
    rw [Field.finSepDegree_eq_finrank_of_isSeparable] at h
    exact lt_irrefl _ h
  · exact hM (le_sup_left.trans ((relfinrank_eq_one_iff).mp h1))

end GroundTheory.Arith.Abelian
