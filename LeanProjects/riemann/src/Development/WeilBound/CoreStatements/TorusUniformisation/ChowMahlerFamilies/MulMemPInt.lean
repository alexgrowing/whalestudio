import Mathlib
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.IsDerAt0
import Development.WeilBound.CoreStatements.HodgeTatePoints.CntCoord
import Development.WeilBound.CoreStatements.HodgeTatePoints.RaChar
import Development.WeilBound.CoreStatements.HodgeTatePoints.DetUpdateRowDiagonal
import ReciprocityTheory.DualLattices.HasLenCokerDet

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR PositivityTheory.HtPt.Ra
open scoped Matrix

noncomputable section

namespace PositivityTheory.Xgn.TestGroupPoint

variable {p : ℕ} [Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C] {v : Valuation C NNReal}
  {R : Type} [CommRing R] [Algebra R C] {I : Type} [Fintype I] [DecidableEq I]

theorem mono_basis (hv : v.Integers R) (hp1 : v (p : C) < 1) (AA : HopfOrder (C := C) R (I → ZMod p))
    {cA cN : NNReal} (hA : HasLen v R (AFQuot p AA.carrier) cA) (hN : HasColen R v AA.carrier cN)
    (heq : cA ^ (Fintype.card (I → ZMod p) * (p - 1)) = cN ^ 2) :
    ∃ (ε : I → R) (u : I → (I → ZMod p) → C),
      (∀ j, (fun x => algebraMap R C (ε j) * u j x) ∈ afFun p AA.carrier) ∧
      (∀ j, v (p : C) ≤ v (algebraMap R C (ε j)) ^ (p - 1)) ∧ (∀ j x, v (u j x) ≤ 1) ∧
      v (Matrix.of fun (x α : I → ZMod p) => ∏ j, u j x ^ (α j).val).det = 1 ∧
      AA.carrier = Submodule.span R (Set.range fun (α : I → ZMod p) (y : I → ZMod p) =>
        ∏ j, (algebraMap R C (ε j) * u j y) ^ (α j).val) := by
  obtain ⟨Λ, ε, hΛ, hspan, hε, hlen⟩ := smith p C v R hv hp1 I AA
  have hcA : cA = ∏ j, v (algebraMap R C (ε j)) := hasLen_unique hv hA hlen
  have hl := fun j => lifts p C v R hv hp1 I AA (Λ j) (ε j)
    (by rw [hspan]; exact Submodule.subset_span ⟨j, rfl⟩) (hε j)
  choose u hu_mem hu_int hu_cong using hl
  refine ⟨ε, u, hu_mem, hε, hu_int, (u5 p C v R hv hp1 I Λ u hΛ hu_int hu_cong).1, ?_⟩
  let B' : Matrix (I → ZMod p) (I → ZMod p) C := Matrix.of fun (x α : I → ZMod p) =>
    ∏ j, (algebraMap R C (ε j) * u j x) ^ (α j).val
  have hB'v : v B'.det = ∏ j, v (algebraMap R C (ε j)) ^
      (p ^ (Fintype.card I - 1) * (p * (p - 1) / 2)) :=
    (u5 p C v R hv hp1 I Λ u hΛ hu_int hu_cong).2 fun j => algebraMap R C (ε j)
  have hsq : cA ^ (Fintype.card (I → ZMod p) * (p - 1)) = v B'.det ^ 2 := by
    rw [hcA, hB'v]
    exact monomialCount_exponent p _
  have hp0 : v (p : C) ≠ 0 :=
    (Valuation.ne_zero_iff v).2 (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero)
  have hε0 : ∀ j, v (algebraMap R C (ε j)) ≠ 0 := by
    intro j h0
    have hpp : p - 1 ≠ 0 := by have := (Fact.out : p.Prime).two_le; omega
    have := hε j
    rw [h0, zero_pow hpp] at this
    exact hp0 (le_antisymm this zero_le)
  have hB'0 : v B'.det ≠ 0 := by
    rw [hB'v]
    exact Finset.prod_ne_zero_iff.2 fun j _ => pow_ne_zero _ (hε0 j)
  have hmem : ∀ α : I → ZMod p, (fun x => B' x α) ∈ AA.carrier := by
    intro α
    exact monomialCount_prod_pow_mem AA (fun j y => algebraMap R C (ε j) * u j y)
      (fun j => (Submodule.mem_inf.1 (hu_mem j)).1) (fun j => (α j).val)
  obtain ⟨B, hAA, hBc⟩ := hN
  obtain ⟨W, hW⟩ := monomialCount_exists_factor (R := R) B B' (fun α => hAA ▸ hmem α)
  have hdet : v B'.det = cN * v (algebraMap R C W.det) := by
    rw [hW, Matrix.det_mul, map_mul, RingHom.map_det, hBc]; rfl
  have hBeq : v B'.det = cN := by
    rw [hsq] at heq
    exact (pow_left_inj₀ zero_le zero_le two_ne_zero).1 heq
  have hcN0 : cN ≠ 0 := hBeq ▸ hB'0
  have hw : v (algebraMap R C W.det) = 1 := by
    have h : cN * v (algebraMap R C W.det) = cN * 1 := by rw [← hdet, hBeq, mul_one]
    exact mul_left_cancel₀ hcN0 h
  have hWu : IsUnit W.det :=
    hv.isUnit_of_one (isUnit_iff_ne_zero.2 fun h0 => by simp [h0] at hw) hw
  have hBeq' : B' * (W⁻¹).map (algebraMap R C) = B := by
    rw [hW, Matrix.mul_assoc, ← Matrix.map_mul, Matrix.mul_nonsing_inv _ hWu,
      Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one]
  have hspan' : Submodule.span R (Set.range fun (α : I → ZMod p) (y : I → ZMod p) =>
      ∏ j, (algebraMap R C (ε j) * u j y) ^ (α j).val) =
      Submodule.span R (Set.range fun α x => B' x α) := rfl
  rw [hspan']
  refine le_antisymm ?_ (Submodule.span_le.2 ?_)
  · rw [hAA]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨j, rfl⟩
    have := monomialCount_col_mem_span (R := R) B' (W⁻¹) j
    rwa [hBeq'] at this
  · rintro _ ⟨α, rfl⟩
    exact hmem α

section Der

variable {W : Type} [AddCommGroup W] [Module R W] {N : Type} [AddCommGroup N] [Fintype N] [DecidableEq N]
  {AA : HopfOrder (C := C) R N} {Dv : AA.carrier →ₗ[R] W}

omit [Fact p.Prime] [IsAlgClosed C] [CharZero C] in
theorem der_one (hD : IsDerAt0 _ Dv) : Dv ⟨1, AA.one_mem⟩ = 0 := by
  have h := hD ⟨1, AA.one_mem⟩ ⟨1, AA.one_mem⟩ ⟨1, AA.one_mem⟩ 1 1 (by simp) (by simp) (by simp)
  rw [one_smul] at h
  exact (left_eq_add.1 h)

omit [Fact p.Prime] [IsAlgClosed C] [CharZero C] in
theorem der_mul (hD : IsDerAt0 _ Dv) (hW : ∀ w : W, (p : R) • w = 0) (f g h : AA.carrier)
    (e : (h : N → C) = (f : N → C) * (g : N → C)) (hf : f.1 0 ∈ pInt (C := C) R p) (hg : g.1 0 ∈ pInt (C := C) R p) :
    Dv h = 0 := by
  obtain ⟨a, ha⟩ := PositivityTheory.HtPt.Rh.mem_pInt.1 hf
  obtain ⟨b, hb⟩ := PositivityTheory.HtPt.Rh.mem_pInt.1 hg
  rw [hD f g h (a * p) (b * p) e (by rw [ha, map_mul, map_natCast]) (by rw [hb, map_mul, map_natCast]),
    mul_smul, mul_smul, hW, hW, smul_zero, smul_zero, add_zero]

omit [Fact p.Prime] [IsAlgClosed C] [CharZero C] in
theorem mul_mem_pInt {f g : N → C} (hg : g ∈ AA.carrier) (hf : f 0 ∈ pInt (C := C) R p) :
    (f * g) 0 ∈ pInt (C := C) R p := by
  obtain ⟨r, hr⟩ := AA.le_int hg 0
  have := Submodule.smul_mem _ r hf
  rw [Algebra.smul_def, hr, mul_comm] at this
  exact this

omit [IsAlgClosed C] in
theorem der_tl (hv : v.Integers R) (hp : v (p : C) < 1) (hD : IsDerAt0 _ Dv) (hW : ∀ w : W, (p : R) • w = 0)
    (f : AA.carrier) (h1 : f.1 0 = 1) :
    Dv ⟨fun x => tl p (f.1 x), tl_mem_order hv p hp AA f.2⟩ = Dv f := by
  have hm : f.1 - 1 ∈ AA.carrier := AA.carrier.sub_mem f.2 AA.one_mem
  have h0 : (f.1 - 1) 0 ∈ pInt (C := C) R p := by
    rw [Pi.sub_apply, h1, Pi.one_apply, sub_self]; exact Submodule.zero_mem _
  have hr : ∀ k : ℕ, ∃ r : R, k ∈ Finset.Ico 1 p → algebraMap R C r = (-1) ^ (k - 1) / (k : C) := by
    intro k
    by_cases hk : k ∈ Finset.Ico 1 p
    · obtain ⟨h1, h2⟩ := Finset.mem_Ico.1 hk
      obtain ⟨r, hr⟩ := hv.exists_of_le_one (r := (-1) ^ (k - 1) / (k : C)) (by
        rw [map_div₀, val_nat_eq v p hp k h1 h2, map_pow, Valuation.map_neg, map_one, one_pow, div_one])
      exact ⟨r, fun _ => hr⟩
    · exact ⟨0, fun h => absurd h hk⟩
  choose r hr using hr
  have e : (⟨fun x => tl p (f.1 x), tl_mem_order hv p hp AA f.2⟩ : AA.carrier) =
      ∑ k ∈ Finset.Ico 1 p, r k • (⟨(f.1 - 1) ^ k, pow_mem_order AA hm k⟩ : AA.carrier) := by
    refine Subtype.ext (funext fun x => ?_)
    rw [Submodule.coe_sum, Finset.sum_apply]
    change tl p (f.1 x) = _
    rw [tl]
    refine Finset.sum_congr rfl fun k hk => ?_
    simp only [Submodule.coe_smul, Pi.smul_apply, Algebra.smul_def, hr k hk, Pi.pow_apply, Pi.sub_apply, Pi.one_apply]
    ring
  have h1m : 1 ∈ Finset.Ico 1 p := Finset.mem_Ico.2 ⟨le_rfl, (Fact.out : p.Prime).one_lt⟩
  rw [e, map_sum, Finset.sum_eq_single_of_mem 1 h1m]
  · have : r 1 = 1 := hv.hom_inj (by rw [hr 1 h1m]; simp)
    rw [this, one_smul]
    have e2 : (⟨(f.1 - 1) ^ 1, pow_mem_order AA hm 1⟩ : AA.carrier) = f - ⟨1, AA.one_mem⟩ :=
      Subtype.ext (pow_one _)
    rw [e2, map_sub, der_one hD, sub_zero]
  · intro k hk hk1
    obtain ⟨k, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by have := (Finset.mem_Ico.1 hk).1; omega⟩
    rw [map_smul, der_mul hD hW ⟨_, hm⟩ ⟨(f.1 - 1) * (f.1 - 1) ^ k, AA.mul_mem _ _ hm (pow_mem_order AA hm k)⟩ _
      (by change (f.1 - 1) ^ (k + 2) = (f.1 - 1) * ((f.1 - 1) * (f.1 - 1) ^ k); ring) h0
      (mul_mem_pInt (pow_mem_order AA hm k) h0), smul_zero]

omit [Fact p.Prime] [IsAlgClosed C] [CharZero C] in
theorem der_mon (hD : IsDerAt0 _ Dv) (hW : ∀ w : W, (p : R) • w = 0) (X : I → N → C) (hX : ∀ j, X j ∈ AA.carrier)
    (h0 : ∀ j, X j 0 ∈ pInt (C := C) R p) (n : I → ℕ) :
    Dv ⟨_, monomialCount_prod_pow_mem AA X hX n⟩ = 0 ∨ ∃ j, n = Pi.single j 1 := by
  have split : ∀ (n : I → ℕ) j, n j ≠ 0 → (fun y => ∏ i, X i y ^ n i) =
      X j * fun y => ∏ i, X i y ^ (n - Pi.single j 1 : I → ℕ) i := by
    intro n j hj
    funext y
    have e : n = Pi.single j 1 + (n - Pi.single j 1) := by
      funext i
      by_cases h : i = j
      · subst h; simp; omega
      · simp [h]
    conv_lhs => rw [e]
    simp only [Pi.add_apply, pow_add, Finset.prod_mul_distrib, Pi.mul_apply]
    congr 1
    rw [Finset.prod_eq_single j (fun i _ hi => by simp [hi]) (by simp)]
    simp
  by_cases hn : n = 0
  · left
    subst hn
    have : (⟨_, monomialCount_prod_pow_mem AA X hX 0⟩ : AA.carrier) = ⟨1, AA.one_mem⟩ :=
      Subtype.ext (funext fun y => by simp)
    rw [this, der_one hD]
  · obtain ⟨j, hj⟩ := Function.ne_iff.1 hn
    by_cases hn' : n - Pi.single j 1 = 0
    · right
      refine ⟨j, funext fun i => ?_⟩
      have := congrFun hn' i
      by_cases h : i = j
      · subst h; simp at this hj ⊢; omega
      · simpa [h] using this
    · left
      obtain ⟨i, hi⟩ := Function.ne_iff.1 hn'
      refine der_mul hD hW ⟨_, hX j⟩ ⟨_, monomialCount_prod_pow_mem AA X hX (n - Pi.single j 1)⟩ _
        (split n j hj) (h0 j) ?_
      change (fun y => ∏ i, X i y ^ (n - Pi.single j 1 : I → ℕ) i) 0 ∈ _
      rw [split _ i hi]
      exact mul_mem_pInt (monomialCount_prod_pow_mem AA X hX _) (h0 i)

end Der

theorem small_gen (hv : v.Integers R) (hp1 : v (p : C) < 1) (AA : HopfOrder (C := C) R (I → ZMod p))
    {cA cN : NNReal} (hA : HasLen v R (AFQuot p AA.carrier) cA) (hN : HasColen R v AA.carrier cN)
    (heq : cA ^ (Fintype.card (I → ZMod p) * (p - 1)) = cN ^ 2)
    {W : Type} [AddCommGroup W] [Module R W] {Dv : AA.carrier →ₗ[R] W}
    (hD : IsDerAt0 _ Dv) (hW : ∀ w : W, (p : R) • w = 0) {t : NNReal} (ht : t ^ (p - 1) = v (p : C)) :
    ∃ X : I → AA.carrier, (∀ j, (X j).1 ∈ afFun p AA.carrier) ∧
      (∀ g, Dv g ∈ Submodule.span R (Set.range fun j => Dv (X j))) ∧
      ∀ g : AA.carrier, (∀ y, v (g.1 y) ≤ t * v (p : C)) → Dv g = 0 := by
  obtain ⟨ε, u, hu, hε, hu1, hdet, hsp⟩ := mono_basis hv hp1 AA hA hN heq
  have hp2 := (Fact.out : p.Prime).two_le
  let X : I → (I → ZMod p) → C := fun j y => algebraMap R C (ε j) * u j y
  have hX : ∀ j, X j ∈ AA.carrier := fun j => (hu j).1
  have h0 : ∀ j, X j 0 ∈ pInt (C := C) R p := fun j => by
    have := Submodule.neg_mem _ ((hu j).2 0 0)
    simpa using this
  let mon : (I → ZMod p) → AA.carrier := fun α => ⟨_, monomialCount_prod_pow_mem AA X hX fun j => (α j).val⟩
  have hexp : ∀ g : AA.carrier, ∃ c : (I → ZMod p) → R, g = ∑ α, c α • mon α := by
    intro g
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 (hsp.le g.2)
    refine ⟨c, Subtype.ext ?_⟩
    rw [← hc, Submodule.coe_sum]
    rfl
  have hsingle : ∀ α j, (fun j => (α j).val) = Pi.single j 1 → mon α = ⟨X j, hX j⟩ := by
    intro α j h
    refine Subtype.ext (funext fun y => ?_)
    change ∏ i, X i y ^ (fun j => (α j).val) i = X j y
    rw [h, Finset.prod_eq_single j (fun i _ hi => by simp [hi]) (by simp)]
    simp
  refine ⟨fun j => ⟨X j, hX j⟩, hu, fun g => ?_, fun g hg => ?_⟩
  · obtain ⟨c, rfl⟩ := hexp g
    rw [map_sum]
    refine Submodule.sum_mem _ fun α _ => ?_
    rw [map_smul]
    refine Submodule.smul_mem _ _ ?_
    rcases der_mon hD hW X hX h0 fun j => (α j).val with h | ⟨j, h⟩
    · rw [show Dv (mon α) = 0 from h]; exact Submodule.zero_mem _
    · rw [hsingle α j h]; exact Submodule.subset_span ⟨j, rfl⟩
  · obtain ⟨c, rfl⟩ := hexp g
    have hU : ∀ x α : I → ZMod p, v (∏ j, u j x ^ (α j).val) ≤ 1 := fun x α => by
      rw [map_prod]
      exact Finset.prod_le_one' fun j _ => by rw [map_pow]; exact pow_le_one₀ zero_le (hu1 j x)
    choose U hU using fun x α => hv.exists_of_le_one (hU x α)
    have hUm : (Matrix.of U).map (algebraMap R C) = Matrix.of fun (x α : I → ZMod p) => ∏ j, u j x ^ (α j).val := by
      ext x α; exact hU x α
    have hUu : IsUnit (Matrix.of U).det := by
      refine hv.isUnit_of_one' ?_
      rw [RingHom.map_det, RingHom.mapMatrix_apply, hUm, hdet]
    let d : (I → ZMod p) → C := fun α => algebraMap R C (c α) * ∏ j, algebraMap R C (ε j) ^ (α j).val
    have hgd : (∑ α, c α • mon α).1 = (Matrix.of U).map (algebraMap R C) *ᵥ d := by
      funext y
      rw [hUm, Submodule.coe_sum, Finset.sum_apply, Matrix.mulVec, dotProduct]
      refine Finset.sum_congr rfl fun α _ => ?_
      change c α • ∏ j, (algebraMap R C (ε j) * u j y) ^ (α j).val = _
      simp only [Algebra.smul_def, mul_pow, Finset.prod_mul_distrib, Matrix.of_apply, d]
      ring
    have hd : d = ((Matrix.of U)⁻¹).map (algebraMap R C) *ᵥ (∑ α, c α • mon α).1 := by
      rw [hgd, Matrix.mulVec_mulVec, ← Matrix.map_mul, Matrix.nonsing_inv_mul _ hUu,
        Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec]
    have hdv : ∀ α, v (d α) ≤ t * v (p : C) := fun α => by
      rw [hd, Matrix.mulVec, dotProduct]
      refine v.map_sum_le fun y _ => ?_
      rw [map_mul]
      exact (mul_le_of_le_one_left zero_le (hv.map_le_one _)).trans (hg y)
    rw [map_sum]
    refine Finset.sum_eq_zero fun α _ => ?_
    rw [map_smul]
    rcases der_mon hD hW X hX h0 fun j => (α j).val with h | ⟨j, h⟩
    · rw [show Dv (mon α) = 0 from h, smul_zero]
    · have h1 := hdv α
      have h2 : ∏ i, algebraMap R C (ε i) ^ (α i).val = algebraMap R C (ε j) := by
        change ∏ i, algebraMap R C (ε i) ^ (fun j => (α j).val) i = _
        rw [h, Finset.prod_eq_single j (fun i _ hi => by simp [hi]) (by simp)]
        simp
      simp only [d, h2, map_mul] at h1
      have hp0 : v (p : C) ≠ 0 :=
        (Valuation.ne_zero_iff v).2 (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero)
      have ht0 : t ≠ 0 := fun h => hp0 (by rw [← ht, h, zero_pow (by omega)])
      have h3 : t ≤ v (algebraMap R C (ε j)) := le_of_pow_le_pow_left₀ (n := p - 1) (by omega) zero_le (ht ▸ hε j)
      have h4 : v (algebraMap R C (c α)) ≤ v (algebraMap R C (p : R)) := by
        rw [map_natCast]
        refine le_of_mul_le_mul_left (a := t) ?_ (pos_iff_ne_zero.2 ht0)
        rw [mul_comm]
        exact (mul_le_mul_right h3 _).trans h1
      obtain ⟨s, hs⟩ := hv.dvd_of_le h4
      rw [hs, mul_comm, mul_smul, hW, smul_zero]

end PositivityTheory.Xgn.TestGroupPoint
