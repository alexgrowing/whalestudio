import Formalism.LocalToGlobal.ProjectiveLattices.CurveOpen
import Formalism.LocalToGlobal.ProjectiveLattices.CurveInstSt
import Formalism.LocalToGlobal.ProjectiveLattices.CompHt

noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps ReciprocityTheory.ChartRestriction.G.Geo.Tor

section Alg

variable {K L : Type*} [Field K] [Field L] [Algebra K L] {N : ℕ}

variable (K) in

def HomQ (x : Fin N → L) (f : L) : Prop :=
  ∃ (e : ℕ) (A B : MvPolynomial (Fin N) K), A.IsHomogeneous e ∧ B.IsHomogeneous e ∧
    MvPolynomial.aeval x B ≠ 0 ∧ f = MvPolynomial.aeval x A / MvPolynomial.aeval x B

theorem homQ_mul {x : Fin N → L} {f g : L} (hf : HomQ K x f) (hg : HomQ K x g) : HomQ K x (f * g) := by
  obtain ⟨e, A, B, hA, hB, hBx, rfl⟩ := hf
  obtain ⟨e', A', B', hA', hB', hBx', rfl⟩ := hg
  exact ⟨e + e', A * A', B * B', hA.mul hA', hB.mul hB', by rw [map_mul]; exact mul_ne_zero hBx hBx',
    by rw [map_mul, map_mul, div_mul_div_comm]⟩

theorem homQ_add {x : Fin N → L} {f g : L} (hf : HomQ K x f) (hg : HomQ K x g) : HomQ K x (f + g) := by
  obtain ⟨e, A, B, hA, hB, hBx, rfl⟩ := hf
  obtain ⟨e', A', B', hA', hB', hBx', rfl⟩ := hg
  exact ⟨e + e', A * B' + B * A', B * B', (hA.mul hB').add (hB.mul hA'), hB.mul hB',
    by rw [map_mul]; exact mul_ne_zero hBx hBx',
    by rw [map_add, map_mul, map_mul, map_mul, div_add_div _ _ hBx hBx']⟩

theorem homQ_inv {x : Fin N → L} {f : L} (hf : HomQ K x f) : HomQ K x f⁻¹ := by
  obtain ⟨e, A, B, hA, hB, hBx, rfl⟩ := hf
  by_cases hAx : MvPolynomial.aeval x A = 0
  · rw [hAx, zero_div, inv_zero]
    exact ⟨0, 0, 1, MvPolynomial.isHomogeneous_zero _ _ _, MvPolynomial.isHomogeneous_one _ _, by simp, by simp⟩
  · exact ⟨e, B, A, hB, hA, hAx, by rw [inv_div]⟩

theorem homQ_algebraMap (x : Fin N → L) (c : K) : HomQ K x (algebraMap K L c) :=
  ⟨0, MvPolynomial.C c, 1, MvPolynomial.isHomogeneous_C _ _, MvPolynomial.isHomogeneous_one _ _, by simp, by simp⟩

theorem homQ_ratio (x : Fin N → L) (m k₀ : Fin N) (hx : x k₀ ≠ 0) : HomQ K x (x m / x k₀) :=
  ⟨1, MvPolynomial.X m, MvPolynomial.X k₀, MvPolynomial.isHomogeneous_X _ _, MvPolynomial.isHomogeneous_X _ _,
    by simpa using hx, by simp⟩

variable (K) in

def homQField (x : Fin N → L) : IntermediateField K L where
  carrier := {f | HomQ K x f}
  mul_mem' := fun ha hb => homQ_mul ha hb
  add_mem' := fun ha hb => homQ_add ha hb
  algebraMap_mem' := homQ_algebraMap x
  inv_mem' := fun _ hf => homQ_inv hf

theorem homQ_of_mem_adjoin (x : Fin N → L) (k₀ : Fin N) (hx : x k₀ ≠ 0) {f : L}
    (hf : f ∈ IntermediateField.adjoin K (Set.range fun m => x m / x k₀)) : HomQ K x f := by
  have hle : IntermediateField.adjoin K (Set.range fun m => x m / x k₀) ≤ homQField K x := by
    rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨m, rfl⟩
    exact homQ_ratio x m k₀ hx
  exact hle hf

theorem isAlgebraic_of_trdeg_eq (F : IntermediateField K L) (d : ℕ) (hF : Algebra.trdeg K F = d)
    (hL : Algebra.trdeg K L = d) : Algebra.IsAlgebraic F L := by
  have hs := trdeg_add_eq K F (A := L)
  rw [hF, hL] at hs
  have h0 : Algebra.trdeg F L = 0 := by
    rcases Cardinal.add_eq_left_iff.1 hs with h | h
    · exact absurd ((le_max_left _ _).trans h) (not_le.2 ((Cardinal.natCast_lt_aleph0 (n := d))))
    · exact h
  exact trdeg_eq_zero_iff.1 h0

theorem exists_homInt (x : Fin N → L) (k₀ : Fin N) (hx : x k₀ ≠ 0)
    (halg : Algebra.IsAlgebraic (IntermediateField.adjoin K (Set.range fun m => x m / x k₀)) L) (a : L) :
    ∃ (k n : ℕ) (P : MvPolynomial (Fin N) K) (cf : ℕ → MvPolynomial (Fin N) K), 0 < k ∧ P.IsHomogeneous k ∧
      MvPolynomial.aeval x P ≠ 0 ∧ (∀ i < n, (cf i).IsHomogeneous ((n - i) * k)) ∧
      (MvPolynomial.aeval x P * a) ^ n + ∑ i ∈ Finset.range n,
        MvPolynomial.aeval x (cf i) * (MvPolynomial.aeval x P * a) ^ i = 0 := by
  set F := IntermediateField.adjoin K (Set.range fun m => x m / x k₀) with hFdef
  obtain ⟨p, hpm, hp⟩ := ((halg.isAlgebraic a).isIntegral : IsIntegral F a)
  have hq : ∀ i, HomQ K x ((p.coeff i : F) : L) := fun i => homQ_of_mem_adjoin x k₀ hx (p.coeff i).2
  choose e A B hA hB hBx hf using hq
  obtain ⟨n, hn⟩ : ∃ n, p.natDegree = n := ⟨_, rfl⟩
  set P : MvPolynomial (Fin N) K := MvPolynomial.X k₀ * ∏ i ∈ Finset.range n, B i with hPdef
  have hPh : P.IsHomogeneous (1 + ∑ i ∈ Finset.range n, e i) :=
    (MvPolynomial.isHomogeneous_X K k₀).mul (MvPolynomial.IsHomogeneous.prod _ _ _ fun i _ => hB i)
  have hPx : MvPolynomial.aeval x P = x k₀ * ∏ i ∈ Finset.range n, MvPolynomial.aeval x (B i) := by
    rw [hPdef, map_mul, MvPolynomial.aeval_X, map_prod]
  have hPx0 : MvPolynomial.aeval x P ≠ 0 := by
    rw [hPx]; exact mul_ne_zero hx (Finset.prod_ne_zero_iff.2 fun i _ => hBx i)
  refine ⟨1 + ∑ i ∈ Finset.range n, e i, n, P,
    fun i => P ^ (n - i - 1) * (MvPolynomial.X k₀ * ∏ j ∈ (Finset.range n).erase i, B j) * A i,
    by omega, hPh, hPx0, ?_, ?_⟩
  · intro i hi
    have hS : ∑ j ∈ Finset.range n, e j = e i + ∑ j ∈ (Finset.range n).erase i, e j :=
      (Finset.add_sum_erase _ _ (Finset.mem_range.2 hi)).symm
    have h1 := ((hPh.pow (n - i - 1)).mul ((MvPolynomial.isHomogeneous_X K k₀).mul
      (MvPolynomial.IsHomogeneous.prod ((Finset.range n).erase i) B e fun j _ => hB j))).mul (hA i)
    convert h1 using 1
    obtain ⟨t, ht⟩ : ∃ t, n - i = t + 1 := ⟨n - i - 1, by omega⟩
    rw [ht, Nat.add_sub_cancel, hS]
    ring
  · beta_reduce
    have hp' : Polynomial.aeval a p = 0 := by rw [Polynomial.aeval_def]; exact hp
    rw [Polynomial.aeval_eq_sum_range, Finset.sum_range_succ, hpm.coeff_natDegree, one_smul, hn] at hp'
    have key : ∀ i ∈ Finset.range n,
        MvPolynomial.aeval x (P ^ (n - i - 1) * (MvPolynomial.X k₀ * ∏ j ∈ (Finset.range n).erase i, B j) * A i) *
          (MvPolynomial.aeval x P * a) ^ i = MvPolynomial.aeval x P ^ n * (p.coeff i • a ^ i) := by
      intro i hi
      have hi' := Finset.mem_range.1 hi
      have hPi : MvPolynomial.aeval x P = x k₀ * (MvPolynomial.aeval x (B i) *
          ∏ j ∈ (Finset.range n).erase i, MvPolynomial.aeval x (B j)) := by
        rw [hPx, ← Finset.mul_prod_erase _ _ hi]
      have hsm : p.coeff i • a ^ i = MvPolynomial.aeval x (A i) / MvPolynomial.aeval x (B i) * a ^ i := by
        rw [Algebra.smul_def, IntermediateField.algebraMap_apply, hf i]
      obtain ⟨t, ht⟩ : ∃ t, n - i = t + 1 := ⟨n - i - 1, by omega⟩
      have hpow : MvPolynomial.aeval x P ^ n =
          MvPolynomial.aeval x P ^ t * MvPolynomial.aeval x P * MvPolynomial.aeval x P ^ i := by
        rw [← pow_succ, ← pow_add]; congr 1; omega
      rw [hsm, hpow]
      simp only [map_mul, map_pow, MvPolynomial.aeval_X, map_prod]
      rw [ht, Nat.add_sub_cancel, hPi]
      field_simp [hBx i]
      ring
    rw [Finset.sum_congr rfl key, ← Finset.mul_sum, mul_pow, ← mul_add, add_comm, hp', mul_zero]

end Alg

variable {D : D7} {T : Top D} (h : LawsP T) (j : ℕ) (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c)

def IntFormSt {wL : WeightFamilies.Wt D j} {N : ℕ} (w : Fin N → (recB h.toLawsCore).Cusp j wL) : Prop :=
  ∀ (Z : Comp (T.Q.Xo j) T.Q.c) (k n : ℕ) (cf : ℕ → MvPolynomial (Fin N) T.Q.c.F) (b : Om Z), 0 < k →
    (∀ i < n, (cf i).IsHomogeneous ((n - i) * k)) →
    b ^ n + ∑ i ∈ Finset.range n,
        MvPolynomial.aeval (fun m => evC hG Z ((w m : (recB h.toLawsCore).Cusp j wL) : T.R j)) (cf i) * b ^ i = 0 →
    ∃ g : (recB h.toLawsCore).Cusp j (wsmul k wL),
      evC hG Z ((g : (recB h.toLawsCore).Cusp j (wsmul k wL)) : T.R j) = b

theorem birSt_of (htr : FnTrdeg (T.Q.Xo j) T.Q.c (WeightFamilies.dimY D j)) {ka wL wF : WeightFamilies.Wt D j}
    (G : GlobalFamilyData (recPlus h j hj) ka wL wF)
    (hB2 : ∀ Z : Comp (T.Q.Xo j) T.Q.c, ∃ k₀, evC hG Z ((G.w k₀ : (recB h.toLawsCore).Cusp j wL) : T.R j) ≠ 0 ∧
      Algebra.trdeg T.Q.c.F (IntermediateField.adjoin T.Q.c.F (Set.range fun k =>
        evC hG Z ((G.w k : (recB h.toLawsCore).Cusp j wL) : T.R j) /
          evC hG Z ((G.w k₀ : (recB h.toLawsCore).Cusp j wL) : T.R j))) = WeightFamilies.dimY D j)
    (hint : IntFormSt h j hG G.w) : BIRSt h j hj hG G := by
  intro Z a
  obtain ⟨k₀, hx0, htrF⟩ := hB2 Z
  have halg := isAlgebraic_of_trdeg_eq _ _ htrF (htr Z)
  obtain ⟨k, n, P, cf, hk, hP, hP0, hcf, heq⟩ := exists_homInt (K := T.Q.c.F) _ k₀ hx0 halg a
  obtain ⟨g, hg⟩ := hint Z k n cf _ hk hcf heq
  exact ⟨k, g, P, hP, hP0, by rw [hg, mul_comm]⟩

theorem birSt_of_big (htr : FnTrdeg (T.Q.Xo j) T.Q.c (WeightFamilies.dimY D j)) {ka wL wF : WeightFamilies.Wt D j}
    (G : GlobalFamilyData (recPlus h j hj) ka wL wF) (hBig : BigAt h j hj hG G) (hint : IntFormSt h j hG G.w) :
    BIRSt h j hj hG G :=
  birSt_of h j hj hG htr G hBig.2 hint

end Formalism.L2.Pj
