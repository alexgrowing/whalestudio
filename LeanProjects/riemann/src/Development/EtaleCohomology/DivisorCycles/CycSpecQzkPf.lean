import Development.EtaleCohomology.DivisorCycles.CycleCountPf

open Matrix
namespace LateralTheory.DivDb.CycSpec_qzkPf
open LateralTheory.DivDb

variable {C : Type} [Field C] {N n : ℕ}

lemma iter {p : Fin n → Mat C N} {y : Mat C N} {π : Equiv.Perm (Fin n)}
    (h : ∀ j, y * p j = p (π j) * y) (m : ℕ) (r : Fin n) : y ^ m * p r = p ((π ^ m) r) * y ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    have e1 : (π ^ (m + 1)) r = π ((π ^ m) r) := by rw [pow_succ', Equiv.Perm.mul_apply]
    rw [e1, pow_succ' y, mul_assoc, ih, ← mul_assoc, h, mul_assoc]

lemma eig [IsAlgClosed C] (A P : Mat C N) (hP : P * P = P) (hP0 : P ≠ 0) (hA : A * P = P * A) :
    ∃ (β : C) (v : Fin N → C), v ≠ 0 ∧ P *ᵥ v = v ∧ A *ᵥ v = β • v := by
  let W := LinearMap.range (Matrix.toLin' P)
  have hW : ∀ x ∈ W, Matrix.toLin' A x ∈ W := by
    rintro _ ⟨u, rfl⟩
    exact ⟨A *ᵥ u, by simp [Matrix.toLin'_apply, Matrix.mulVec_mulVec, hA]⟩
  haveI : Nontrivial W := by
    rw [Submodule.nontrivial_iff_ne_bot]
    intro h
    apply hP0
    have h2 := LinearMap.range_eq_bot.mp h
    exact Matrix.toLin'.injective (by rw [h2, map_zero])
  obtain ⟨β, hβ⟩ := Module.End.exists_eigenvalue ((Matrix.toLin' A).restrict hW)
  obtain ⟨x, hx⟩ := hβ.exists_hasEigenvector
  refine ⟨β, x.1, ?_, ?_, ?_⟩
  · intro h; exact hx.2 (Subtype.ext h)
  · obtain ⟨u, hu⟩ := x.2
    rw [← hu]; simp [Matrix.toLin'_apply, Matrix.mulVec_mulVec, hP]
  · have h3 := congrArg Subtype.val (Module.End.mem_eigenspace_iff.mp hx.1)
    simpa [LinearMap.restrict_apply, Matrix.toLin'_apply] using h3

lemma comp {p : Fin n → Mat C N} {y : Mat C N} {π : Equiv.Perm (Fin n)} (hp : Sys p)
    (h : ∀ j, y * p j = p (π j) * y) (r : Fin n) (v : Fin N → C) (hv : p r *ᵥ v = v) (m : ℕ) (q : Fin n) :
    p q *ᵥ (y ^ m *ᵥ v) = if q = (π ^ m) r then y ^ m *ᵥ v else 0 := by
  have hu : y ^ m *ᵥ v = p ((π ^ m) r) *ᵥ (y ^ m *ᵥ v) := by
    conv_lhs => rw [← hv]
    rw [Matrix.mulVec_mulVec, iter h, ← Matrix.mulVec_mulVec]
  rw [hu, Matrix.mulVec_mulVec]
  split_ifs with hq
  · subst hq; rw [(hp.1.idem _).eq]
  · rw [hp.1.ortho hq, Matrix.zero_mulVec]

lemma key {p : Fin n → Mat C N} {y : Mat C N} {π : Equiv.Perm (Fin n)} (hp : Sys p)
    (h : ∀ j, y * p j = p (π j) * y) (r : Fin n) (v : Fin N → C) (β l : C) (hv : p r *ᵥ v = v) (hv0 : v ≠ 0)
    (hβ : y ^ Function.minimalPeriod π r *ᵥ v = β • v) (hl : l ^ Function.minimalPeriod π r = β) (hl0 : l ≠ 0) :
    ∃ w : Fin N → C, w ≠ 0 ∧ y *ᵥ w = l • w ∧ ∀ q, (∀ m : ℕ, q ≠ (π ^ m) r) → p q *ᵥ w = 0 := by
  set k := Function.minimalPeriod π r with hk
  have kpos : 0 < k := by
    apply Function.IsPeriodicPt.minimalPeriod_pos (orderOf_pos π)
    show (⇑π)^[orderOf π] r = r
    rw [← Equiv.Perm.coe_pow, pow_orderOf_eq_one]; rfl
  let S : ℕ → Fin N → C := fun m => (l ^ m)⁻¹ • (y ^ m *ᵥ v)
  refine ⟨∑ m ∈ Finset.range k, S m, ?_, ?_, ?_⟩
  · intro h0
    apply hv0
    have e : p r *ᵥ (∑ m ∈ Finset.range k, S m) = v := by
      rw [Matrix.mulVec_sum, Finset.sum_eq_single 0]
      · simp [S, hv]
      · intro m hm hm0
        simp only [S, Matrix.mulVec_smul, comp hp h r v hv]
        rw [if_neg, smul_zero]
        intro hr
        have hper : Function.IsPeriodicPt π m r := by
          show (⇑π)^[m] r = r
          rw [← Equiv.Perm.coe_pow]; exact hr.symm
        have := hper.minimalPeriod_le (Nat.pos_of_ne_zero hm0)
        have := Finset.mem_range.mp hm
        omega
      · intro h0; exact absurd (Finset.mem_range.mpr kpos) h0
    rw [← e, h0, Matrix.mulVec_zero]
  · have shift : ∑ m ∈ Finset.range k, S (m + 1) = ∑ m ∈ Finset.range k, S m := by
      have a1 := Finset.sum_range_succ' S k
      have a2 := Finset.sum_range_succ S k
      have s0 : S 0 = v := by simp [S]
      have sk : S k = v := by
        simp only [S, hβ, hl, smul_smul]
        rw [inv_mul_cancel₀ (by rw [← hl]; exact pow_ne_zero _ hl0), one_smul]
      rw [s0] at a1; rw [sk] at a2
      exact add_right_cancel (a1.symm.trans a2)
    rw [Matrix.mulVec_sum, ← shift, Finset.smul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    simp only [S, Matrix.mulVec_smul, Matrix.mulVec_mulVec, ← pow_succ', smul_smul]
    congr 1
    rw [pow_succ, mul_inv, ← mul_assoc, mul_comm l, mul_assoc, mul_inv_cancel₀ hl0, mul_one]
  · intro q hq
    rw [Matrix.mulVec_sum]
    refine Finset.sum_eq_zero fun m _ => ?_
    simp only [S, Matrix.mulVec_smul, comp hp h r v hv, if_neg (hq m), smul_zero]

theorem CycSpec_of : LateralTheory.DivDb.CycleCountPf.CycSpec := by
  intro C _ _ _ N n p y π hp hy hyp hd
  classical
  let s := Equiv.Perm.SameCycle.setoid π
  let R : Fin n → Fin n := fun j => (Quotient.mk s j).out
  have hR : ∀ j, π.SameCycle (R j) j := fun j => Quotient.mk_out (s := s) j
  have hR2 : ∀ i j, π.SameCycle i j → R i = R j := fun i j h => by
    show (Quotient.mk s i).out = (Quotient.mk s j).out
    rw [Quotient.sound (s := s) h]
  let k : Fin n → ℕ := fun r => Function.minimalPeriod π r
  have kpos : ∀ r, 0 < k r := fun r => by
    apply Function.IsPeriodicPt.minimalPeriod_pos (orderOf_pos π)
    show (⇑π)^[orderOf π] r = r
    rw [← Equiv.Perm.coe_pow, pow_orderOf_eq_one]; rfl
  have hE : ∀ r, ∃ (β : C) (v : Fin N → C), v ≠ 0 ∧ p r *ᵥ v = v ∧ y ^ k r *ᵥ v = β • v := fun r => by
    refine eig _ _ (hp.1.idem r).eq (hp.2 r) ?_
    rw [iter hyp]
    congr 2
    show (⇑(π ^ k r)) r = r
    rw [Equiv.Perm.coe_pow]; exact Function.iterate_minimalPeriod
  choose β v hv0 hvp hvb using hE
  have β0 : ∀ r, β r ≠ 0 := fun r h0 => by
    obtain ⟨u, hu⟩ := hy.pow (k r)
    apply hv0 r
    have e : ((u⁻¹ : (Mat C N)ˣ) : Mat C N) *ᵥ (y ^ k r *ᵥ v r) = v r := by
      rw [Matrix.mulVec_mulVec, ← hu, Units.inv_mul, Matrix.one_mulVec]
    rw [← e, hvb, h0, zero_smul, Matrix.mulVec_zero]
  have hZ : ∀ r, ∃ z : C, z ^ k r = β r := fun r => IsAlgClosed.exists_pow_nat_eq _ (kpos r)
  choose ζ hζ using hZ
  have hO : ∀ r, ∃ ω : C, IsPrimitiveRoot ω (k r) := fun r => by
    haveI : NeZero ((k r : ℕ) : C) := ⟨Nat.cast_ne_zero.mpr (kpos r).ne'⟩
    exact HasEnoughRootsOfUnity.exists_primitiveRoot C (k r)
  choose ω hω using hO
  have hM : ∀ j, ∃ m, m < k (R j) ∧ (π ^ m) (R j) = j := fun j => by
    obtain ⟨i, -, hi⟩ := (hR j).exists_pow_eq'
    refine ⟨i % k (R j), Nat.mod_lt _ (kpos _), ?_⟩
    rw [Equiv.Perm.coe_pow, Function.iterate_mod_minimalPeriod_eq, ← Equiv.Perm.coe_pow, hi]
  choose m hmk hm using hM
  let l : Fin n → C := fun j => ζ (R j) * ω (R j) ^ m j
  have hlk : ∀ j, l j ^ k (R j) = β (R j) := fun j => by
    simp only [l, mul_pow, hζ]
    rw [← pow_mul, mul_comm (m j), pow_mul, (hω _).pow_eq_one, one_pow, mul_one]
  have hl0 : ∀ j, l j ≠ 0 := fun j => by
    refine mul_ne_zero ?_ (pow_ne_zero _ ((hω _).ne_zero (kpos _).ne'))
    intro h0; apply β0 (R j); rw [← hζ, h0, zero_pow (kpos _).ne']
  have hW : ∀ j, ∃ w : Fin N → C, w ≠ 0 ∧ y *ᵥ w = l j • w ∧ ∀ q, ¬ π.SameCycle j q → p q *ᵥ w = 0 := fun j => by
    obtain ⟨w, hw0, hwy, hwq⟩ := key hp hyp (R j) (v (R j)) (β (R j)) (l j) (hvp _) (hv0 _) (hvb _) (hlk j) (hl0 j)
    refine ⟨w, hw0, hwy, fun q hq => hwq q fun i hi => hq ?_⟩
    rw [hi]
    exact ((hR j).symm.trans (Equiv.Perm.SameCycle.refl π (R j))).trans
      (Equiv.Perm.sameCycle_pow_right.mpr (Equiv.Perm.SameCycle.refl π (R j)))
  refine ⟨l, ?_, fun j => ⟨?_, hW j⟩⟩
  · intro i j hij
    by_cases hs : π.SameCycle i j
    · have e := hR2 i j hs
      have h1 : ω (R j) ^ m i = ω (R j) ^ m j := by
        have h2 : ζ (R i) * ω (R i) ^ m i = ζ (R j) * ω (R j) ^ m j := hij
        rw [e] at h2
        exact mul_left_cancel₀ (fun h0 => by
          apply β0 (R j); rw [← hζ, h0, zero_pow (kpos _).ne']) h2
      have h3 : m i = m j := (hω (R j)).pow_inj (e ▸ hmk i) (hmk j) h1
      rw [← hm i, ← hm j, h3, e]
    · exfalso
      obtain ⟨wi, hi0, hiy, hiq⟩ := hW i
      obtain ⟨wj, hj0, hjy, hjq⟩ := hW j
      exact hd i j hs (l i) wi wj hi0 hj0 hiy (by rw [hij]; exact hjy) hiq hjq
  · obtain ⟨w, hw0, hwy, -⟩ := hW j
    rw [← Matrix.charpoly_toLin', ← Module.End.hasEigenvalue_iff_isRoot_charpoly]
    exact Module.End.hasEigenvalue_of_hasEigenvector
      ⟨Module.End.mem_eigenspace_iff.mpr (by rw [Matrix.toLin'_apply]; exact hwy), hw0⟩

end LateralTheory.DivDb.CycSpec_qzkPf
