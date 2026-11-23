import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexUpLatEqProd

open Formalism.UG Matrix GlobalTheory.InertZeta GlobalTheory.BorelUMod.UpLatIndex

noncomputable section

namespace GlobalTheory.CompanionTheory.InertIndex

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ}

def boxLat (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ} (c : Fin n → ℤ) :
    AddSubgroup (Fin n → L) :=
  AddSubgroup.pi Set.univ fun i => ordBall L (c i)

theorem mem_boxLat {c : Fin n → ℤ} {x : Fin n → L} : x ∈ boxLat L c ↔ ∀ i, x i ∈ ordBall L (c i) := by
  simp [boxLat, AddSubgroup.mem_pi]

theorem relIndex_boxLat (c C : Fin n → ℤ) :
    (boxLat L C).relIndex (boxLat L c) = ∏ i, (ordBall L (C i)).relIndex (ordBall L (c i)) := by
  let f : boxLat L c →+ (∀ i, ordBall L (c i) ⧸ (ordBall L (C i)).addSubgroupOf (ordBall L (c i))) :=
    { toFun := fun x i => QuotientAddGroup.mk ⟨x.1 i, mem_boxLat.1 x.2 i⟩
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hf : Function.Surjective f := fun y => by
    refine ⟨⟨fun i => ((y i).out : L), mem_boxLat.2 fun i => (y i).out.2⟩, funext fun i => ?_⟩
    exact (y i).out_eq
  have hc : (boxLat L C).addSubgroupOf (boxLat L c) = f.ker := by
    ext x
    rw [AddMonoidHom.mem_ker, funext_iff, AddSubgroup.mem_addSubgroupOf, mem_boxLat]
    constructor
    · intro h i
      exact (QuotientAddGroup.eq_zero_iff _).2 (h i)
    · intro h i
      exact AddSubgroup.mem_addSubgroupOf.1
        ((QuotientAddGroup.eq_zero_iff (⟨x.1 i, mem_boxLat.1 x.2 i⟩ : ordBall L (c i))).1 (h i))
  rw [AddSubgroup.relIndex, hc, AddSubgroup.index_ker, AddMonoidHom.range_eq_top.2 hf,
    AddSubgroup.card_top, Nat.card_pi]
  rfl

theorem mem_intL_iff {x : L} : x ∈ intL L ↔ Valued.v x ≤ 1 := Iff.rfl

theorem vecMul_mem_intV {M : Matrix (Fin n) (Fin n) L} (hM : IsInt M) {r : Fin n → L} (hr : r ∈ intV L n) :
    r ᵥ* M ∈ intV L n := by
  rw [mem_intV] at hr ⊢
  intro j
  change ∑ i, r i * M i j ∈ intL L
  exact Subring.sum_mem _ fun i _ => mul_mem (hr i) (hM i j)

theorem v_zpow {ϖ : L} (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) (m : ℤ) :
    Valued.v (ϖ ^ m) = WithZero.exp (-m) := by
  rw [map_zpow₀, hϖ, ← WithZero.exp_zsmul]; simp

theorem mem_preLat_iff {ϖ : L} (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) {d : Fin n → ℤ}
    {a b b' : Matrix (Fin n) (Fin n) L} (hb : IsInt b) (hb' : IsInt b') (eb : b * b' = 1) (r : Fin n → L) :
    r ∈ preLat (a * Matrix.diagonal (fun i => ϖ ^ d i) * b) ↔ r ᵥ* a ∈ boxLat L (fun i => -d i) := by
  have h0 : ϖ ≠ 0 := fun e => by
    rw [e, map_zero] at hϖ; exact WithZero.exp_ne_zero hϖ.symm
  have key : ∀ s : Fin n → L, s ᵥ* Matrix.diagonal (fun i => ϖ ^ d i) ∈ intV L n ↔
      s ∈ boxLat L (fun i => -d i) := fun s => by
    rw [mem_intV, mem_boxLat]
    refine forall_congr' fun i => ?_
    rw [Matrix.vecMul_diagonal, mem_intL_iff, mem_ordBall, map_mul, v_zpow hϖ, neg_neg]
    have e : WithZero.exp (d i) = 1 * (WithZero.exp (-d i))⁻¹ := by rw [WithZero.exp_neg, inv_inv, one_mul]
    rw [e, le_mul_inv_iff₀ (zero_lt_iff.2 WithZero.exp_ne_zero)]
  have hr : r ∈ preLat (a * Matrix.diagonal (fun i => ϖ ^ d i) * b) ↔
      r ᵥ* (a * Matrix.diagonal (fun i => ϖ ^ d i) * b) ∈ intV L n := by
    rw [mem_preLat, mem_intV]
  rw [hr, ← key, ← Matrix.vecMul_vecMul, ← Matrix.vecMul_vecMul]
  refine ⟨fun h => ?_, fun h => vecMul_mem_intV hb h⟩
  have := vecMul_mem_intV hb' h
  rwa [Matrix.vecMul_vecMul, eb, Matrix.vecMul_one] at this

theorem latIndex (hS : Smith) : LatIndex := by
  intro L _ _ ϖ σ q n hU A k hA hk
  have hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ) := hU.2.2.2.1
  have hdet : A.det ≠ 0 := fun h => by
    rw [h, map_zero] at hk; exact WithZero.exp_ne_zero hk.symm
  obtain ⟨d, a, a', b, b', ha, ha', hb, hb', ea, eb, hAe⟩ := hS L ϖ n hϖ A hdet
  have ea' : a * a' = 1 := mul_eq_one_comm.1 ea
  have eb' : b' * b = 1 := mul_eq_one_comm.1 eb
  have hDe : Matrix.diagonal (fun i => ϖ ^ d i) = a' * A * b' := by
    rw [hAe]
    calc _ = (a' * a) * Matrix.diagonal (fun i => ϖ ^ d i) * (b * b') := by rw [ea, eb]; simp
      _ = _ := by simp only [Matrix.mul_assoc]
  have hD : IsInt (Matrix.diagonal (fun i => ϖ ^ d i)) := hDe ▸ (ha'.mul hA).mul hb'
  have hd : ∀ i, 0 ≤ d i := fun i => by
    have h := hD i i
    rw [Matrix.diagonal_apply_eq, mem_intL_iff, v_zpow hϖ, ← WithZero.exp_zero, WithZero.exp_le_exp] at h
    omega
  have hprod : ∀ s : Finset (Fin n), ∏ i ∈ s, WithZero.exp (-(d i)) =
      (WithZero.exp (-∑ i ∈ s, d i) : WithZero (Multiplicative ℤ)) := fun s => by
    induction s using Finset.induction_on with
    | empty => simp
    | insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.sum_insert hi, ih, ← WithZero.exp_add, neg_add]
  have hsum : ∑ i, d i = k := by
    have h := hk
    rw [hAe, Matrix.det_mul, Matrix.det_mul, map_mul, map_mul, v_det_eq_one ha ha' ea', v_det_eq_one hb hb' eb,
      Matrix.det_diagonal, map_prod, one_mul, mul_one, Finset.prod_congr rfl fun i _ => v_zpow hϖ (d i), hprod,
      WithZero.exp_inj] at h
    omega
  let f : (Fin n → L) →+ (Fin n → L) := a.vecMulLinear.toAddMonoidHom
  have hfa : ∀ r, f r = r ᵥ* a := fun _ => rfl
  have hf : Function.Surjective f := fun s => ⟨s ᵥ* a', by
    rw [hfa, Matrix.vecMul_vecMul, ea, Matrix.vecMul_one]⟩
  have h1 : intV L n = (boxLat L fun _ => 0).comap f := by
    ext r
    have e : ∀ x : Fin n → L, x ∈ boxLat L (fun _ => 0) ↔ x ∈ intV L n := fun x => by
      rw [mem_boxLat, mem_intV]
      refine forall_congr' fun i => ?_
      rw [mem_ordBall, mem_intL_iff, neg_zero, WithZero.exp_zero]
    rw [AddSubgroup.mem_comap, e, hfa]
    refine ⟨fun h => vecMul_mem_intV ha h, fun h => ?_⟩
    have := vecMul_mem_intV ha' h
    rwa [Matrix.vecMul_vecMul, ea', Matrix.vecMul_one] at this
  have h2 : preLat A = (boxLat L fun i => -d i).comap f := by
    ext r
    rw [AddSubgroup.mem_comap, hfa, hAe]
    exact mem_preLat_iff hϖ hb hb' eb r
  rw [h1, h2, AddSubgroup.relIndex_comap, AddSubgroup.map_comap_eq_self_of_surjective hf, relIndex_boxLat,
    Finset.prod_congr rfl fun i _ => relIndex_ordBall hU (k := -d i) (K := 0) (by linarith [hd i]),
    Finset.prod_pow_eq_pow_sum, ← pow_mul]
  congr 2
  have : ((∑ i, (0 - -d i).toNat : ℕ) : ℤ) = k := by
    rw [Nat.cast_sum, ← hsum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Int.toNat_of_nonneg (by linarith [hd i])]
    ring
  exact_mod_cast this

end GlobalTheory.CompanionTheory.InertIndex

end
