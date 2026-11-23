import Formalism.HermitianCurvature.HermitianCurvatureProofs.ChartEqsOfParts
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HermSumRight
import Formalism.HermitianCurvature.HermitianCurvatureProofs.StabilizerFixesTailCoords

open Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ComplexOrder

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity.CmpZeroPf

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

theorem herm_nondeg (x : Fin (2 * r + k + 1) → ℂ) (h : ∀ u, herm (Hpk k r) x u = 0) : x = 0 := by
  have hH : Hpk k r *ᵥ x = 0 := by
    funext i
    rw [← JfS.Sym.herm_bvec]
    exact h _
  have h2 := (hpkFacts k r).2.1
  calc x = (Hpk k r * Hpk k r) *ᵥ x := by rw [h2, one_mulVec]
    _ = 0 := by rw [← mulVec_mulVec, hH, mulVec_zero]

theorem lie_fix {X : B.Mat k r} {v : Fin (2 * r + k + 1) → ℂ}
    (h : ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • X) *ᵥ v = v) : X *ᵥ v = 0 := by
  funext i
  have := LieSplitPf.clm_zero (k := k) (r := r) X
    (((ContinuousLinearMap.proj i).comp (LieSplitPf.mvL v)).restrictScalars ℝ) (v i)
    (fun t => by
      simp only [ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.coe_comp', Function.comp_apply,
        ContinuousLinearMap.proj_apply, LieSplitPf.mvL_apply]
      rw [h t])
  simpa only [ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.coe_comp', Function.comp_apply,
    ContinuousLinearMap.proj_apply, LieSplitPf.mvL_apply, Pi.zero_apply] using this

theorem lieW_facts {z : Fin (2 * r + k + 1) → ℂ} {X : B.Mat k r} (hX : X ∈ JfS.lieOf (UWset k r z)) :
    B.inLie k r X ∧ (∀ a : Fin r, X *ᵥ bvec (eI k r a) = 0 ∧ X *ᵥ bvec (esI k r a) = 0) ∧ X *ᵥ z = 0 := by
  refine ⟨?_, fun a => ⟨?_, ?_⟩, ?_⟩
  · have := LieSplitPf.lieHpk_of (k := k) (r := r) (X := X) (fun t => (hX t).1)
    exact this
  · exact lie_fix (fun t => ((hX t).2.1 a).1)
  · exact lie_fix (fun t => ((hX t).2.1 a).2)
  · exact lie_fix (fun t => (hX t).2.2)

def psiW (k r : ℕ) : (Fin (2 * r + k + 1) → ℂ) →ₗ[ℂ] (Fin (k + 1) → ℂ) where
  toFun v i := v ⟨r + i.val, by omega⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem psiW_inj {w : Fin (2 * r + k + 1) → ℂ} (hw : inWb k r w) (h : psiW k r w = 0) : w = 0 := by
  funext i
  by_cases hi : i.val < r ∨ r + k < i.val
  · exact hw i hi
  · have e : psiW k r w ⟨i.val - r, by omega⟩ = w i := by
      show w _ = w i
      congr 1
      apply Fin.ext
      show r + (i.val - r) = i.val
      omega
    rw [← e, h]
    rfl

theorem inWb_sum {ι : Type*} (s : Finset ι) (f : ι → Fin (2 * r + k + 1) → ℂ) (h : ∀ i ∈ s, inWb k r (f i)) :
    inWb k r (∑ i ∈ s, f i) := by
  intro p hp
  rw [Finset.sum_apply]
  exact Finset.sum_eq_zero (fun i hi => h i hi p hp)

theorem perp_zero {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hT : 0 < Tz k r z)
    {Bs : Fin k → Fin (2 * r + k + 1) → ℂ} (hB : Q.IsFrameOf k r [z] Bs)
    (y : Fin (2 * r + k + 1) → ℂ) (hy : inWb k r y) (hyz : herm (Hpk k r) y z = 0)
    (hyB : ∀ b, herm (Hpk k r) y (Bs b) = 0) : y = 0 := by
  by_contra hy0
  have hyy : herm (Hpk k r) y y ≠ 0 := by
    intro h
    exact hy0 (JfS.Sym.wb_definite hz hT hy hyz (by rw [h]; simp))
  have hzz := JfS.Sym.herm_self_ne_zero hT
  have hBz : ∀ b, herm (Hpk k r) (Bs b) z = 0 := fun b => hB.2.2 b z (List.mem_singleton_self z)
  let f : Option (Option (Fin k)) → Fin (2 * r + k + 1) → ℂ := fun o =>
    match o with
    | none => z
    | some none => y
    | some (some b) => Bs b
  have hfW : ∀ o, inWb k r (f o) := by
    intro o
    rcases o with _ | _ | b
    · exact hz
    · exact hy
    · exact hB.1 b
  have hfo : ∀ o o', o ≠ o' → herm (Hpk k r) (f o) (f o') = 0 := by
    intro o o' hne
    rcases o with _ | _ | b <;> rcases o' with _ | _ | b'
    · exact absurd rfl hne
    · show herm _ z y = 0
      rw [JfS.Sym.herm_swap, hyz, star_zero]
    · show herm _ z (Bs b') = 0
      rw [JfS.Sym.herm_swap, hBz, star_zero]
    · exact hyz
    · exact absurd rfl hne
    · exact hyB b'
    · exact hBz b
    · show herm _ (Bs b) y = 0
      rw [JfS.Sym.herm_swap, hyB, star_zero]
    · show herm _ (Bs b) (Bs b') = 0
      rw [hB.2.1 b b', if_neg (fun e => hne (by rw [e]))]
  have hfs : ∀ o, herm (Hpk k r) (f o) (f o) ≠ 0 := by
    intro o
    rcases o with _ | _ | b
    · exact hzz
    · exact hyy
    · show herm _ (Bs b) (Bs b) ≠ 0
      rw [hB.2.1 b b, if_pos rfl]
      exact one_ne_zero
  have hli : LinearIndependent ℂ (fun o => psiW k r (f o)) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg o
    have hsum : (∑ o', g o' • f o') = 0 := by
      apply psiW_inj (inWb_sum _ _ (fun o' _ => JfS.Sym.inWb_smul _ (hfW o')))
      rw [map_sum]
      simpa only [map_smul] using hg
    have := congrArg (fun x => herm (Hpk k r) x (f o)) hsum
    simp only [JfS.Sym.herm_sum_left, JfS.Sym.herm_smul_left, JfS.Sym.herm_zero_left] at this
    rw [Finset.sum_eq_single o (fun o' _ hne => by rw [hfo o' o hne, mul_zero])
      (fun h => absurd (Finset.mem_univ o) h)] at this
    exact (mul_eq_zero.1 this).resolve_right (hfs o)
  have hc := hli.fintype_card_le_finrank
  simp only [Fintype.card_option, Fintype.card_fin, Module.finrank_fin_fun] at hc
  omega

section lieW

variable {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hT : 0 < Tz k r z)
  {Bs : Fin k → Fin (2 * r + k + 1) → ℂ} (hB : Q.IsFrameOf k r [z] Bs)
  {X : B.Mat k r} (hX : X ∈ JfS.lieOf (UWset k r z))
include hz hT hB hX

theorem col_in (w : Fin (2 * r + k + 1) → ℂ) :
    X *ᵥ w = ∑ a, herm (Hpk k r) (X *ᵥ w) (Bs a) • Bs a := by
  obtain ⟨hL, hE, hXz⟩ := lieW_facts hX
  have hBz : ∀ b, herm (Hpk k r) (Bs b) z = 0 := fun b => hB.2.2 b z (List.mem_singleton_self z)
  have hXw : inWb k r (X *ᵥ w) := by
    intro i hi
    rcases hi with hi | hi
    · have e : i = eI k r ⟨i.val, hi⟩ := Fin.ext rfl
      rw [e, ← JfS.Sym.herm_es (X *ᵥ w) ⟨i.val, hi⟩, JfS.Sym.herm_skew hL, (hE _).2, JfS.Sym.herm_zero_right, neg_zero]
    · have e : i = esI k r ⟨2 * r + k - i.val, by omega⟩ := by
        apply Fin.ext
        simp only [esI]
        omega
      rw [e, ← JfS.Sym.herm_e (X *ᵥ w) ⟨2 * r + k - i.val, by omega⟩, JfS.Sym.herm_skew hL, (hE _).1, JfS.Sym.herm_zero_right, neg_zero]
  set q := X *ᵥ w - ∑ a, herm (Hpk k r) (X *ᵥ w) (Bs a) • Bs a with hq
  have hqW : inWb k r q :=
    JfS.Sym.inWb_sub hXw (inWb_sum _ _ (fun a _ => JfS.Sym.inWb_smul _ (hB.1 a)))
  have h1 : herm (Hpk k r) (X *ᵥ w) z = 0 := by
    rw [JfS.Sym.herm_skew hL, hXz, JfS.Sym.herm_zero_right, neg_zero]
  have hqz : herm (Hpk k r) q z = 0 := by
    rw [hq, JfS.Sym.herm_sub_left, h1, JfS.Sym.herm_sum_left]
    simp [JfS.Sym.herm_smul_left, hBz]
  have hqB : ∀ b, herm (Hpk k r) q (Bs b) = 0 := by
    intro b
    rw [hq, JfS.Sym.herm_sub_left, JfS.Sym.herm_sum_left]
    simp [JfS.Sym.herm_smul_left, hB.2.1]
  exact sub_eq_zero.1 (perp_zero hz hT hB q hqW hqz hqB)

theorem row_in (v : Fin (2 * r + k + 1) → ℂ) :
    X *ᵥ v = ∑ b, herm (Hpk k r) v (Bs b) • (X *ᵥ Bs b) := by
  obtain ⟨hL, -, -⟩ := lieW_facts hX
  set y := v - ∑ b, herm (Hpk k r) v (Bs b) • Bs b with hy
  have hyB : ∀ a, herm (Hpk k r) y (Bs a) = 0 := by
    intro a
    rw [hy, JfS.Sym.herm_sub_left, JfS.Sym.herm_sum_left]
    simp [JfS.Sym.herm_smul_left, hB.2.1]
  have hXy : X *ᵥ y = 0 := by
    apply herm_nondeg
    intro u
    rw [JfS.Sym.herm_skew hL, col_in hz hT hB hX u, JfS.Sym.herm_sum_right]
    simp [JfS.Sym.herm_smul_right, hyB]
  have e : X *ᵥ v = X *ᵥ y + X *ᵥ (∑ b, herm (Hpk k r) v (Bs b) • Bs b) := by
    rw [← mulVec_add, hy, sub_add_cancel]
  rw [e, hXy, zero_add, JfS.Sym.mulVec_sum']
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [mulVec_smul]

end lieW

theorem sum_mulVec' {ι : Type*} (s : Finset ι) (M : ι → B.Mat k r) (v : Fin (2 * r + k + 1) → ℂ) :
    (∑ i ∈ s, M i) *ᵥ v = ∑ i ∈ s, M i *ᵥ v := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih => rw [Finset.sum_cons, Finset.sum_cons, add_mulVec, ih]

theorem smul_mulVec'' (c : ℂ) (M : B.Mat k r) (v : Fin (2 * r + k + 1) → ℂ) :
    (c • M) *ᵥ v = c • (M *ᵥ v) := by
  funext i
  simp only [mulVec, dotProduct, Matrix.smul_apply, smul_eq_mul, Pi.smul_apply, Finset.mul_sum, mul_assoc]

theorem trace_vmv (ξ : B.Mat k r) (a b : Fin (2 * r + k + 1) → ℂ) :
    Matrix.trace (ξ * vecMulVec a (star (Hpk k r *ᵥ b))) = herm (Hpk k r) (ξ *ᵥ a) b := by
  have hb : star (Hpk k r *ᵥ b) = star b ᵥ* Hpk k r := by
    rw [star_mulVec, JfS.Sym.hpk_conjT]
  rw [hb, herm, dotProduct_mulVec]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, vecMulVec_apply, dotProduct, mulVec]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  ring

theorem unitB_eq (Bs : Fin k → Fin (2 * r + k + 1) → ℂ) (a b : Fin k) :
    Q.unitB (Hpk k r) Bs a b = vecMulVec (Bs a) (star (Hpk k r *ᵥ Bs b)) := by
  ext p q
  simp only [Q.unitB, Matrix.of_apply, vecMulVec_apply]
  congr 1
  rw [JfS.Sym.herm_bvec_left]
  simp only [Pi.star_apply, mulVec, dotProduct, star_sum, star_mul', JfS.Sym.hpk_star]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [JfS.Sym.hpk_symm]
  ring

theorem cmp_eq (Ξ : B.Mat k r) (Bs : Fin k → Fin (2 * r + k + 1) → ℂ) (a b : Fin k) :
    cmp Ξ Bs a b = herm (Hpk k r) (Ξ *ᵥ Bs a) (Bs b) := by
  show Matrix.trace (Ξ * Q.unitB (Hpk k r) Bs a b) = _
  rw [unitB_eq, trace_vmv]

theorem le_two_pow (n : ℕ) : n ≤ 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : 0 < 2 ^ n := by positivity
    rw [pow_succ]
    omega

theorem skew_nil_zero {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) (hs : Mᴴ = -M) (N : ℕ) (hN : M ^ N = 0) :
    M = 0 := by
  have key : ∀ j : ℕ, M ^ (2 ^ j) = 0 → M = 0 := by
    intro j
    induction j with
    | zero => intro h; simpa using h
    | succ j ih =>
      intro h
      apply ih
      have hc : (M ^ 2 ^ j)ᴴ * M ^ 2 ^ j = 0 := by
        rw [Matrix.conjTranspose_pow, hs, neg_pow, mul_assoc, ← pow_add, ← two_mul, ← pow_succ', h, mul_zero]
      exact Matrix.conjTranspose_mul_self_eq_zero.1 hc
  exact key N (pow_eq_zero_of_le (le_two_pow N) hN)

theorem cp_pow {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ)
    (h : ∀ j, 1 ≤ j → j ≤ m → M.charpoly.coeff (m - j) = 0) : M ^ m = 0 := by
  have hdeg : M.charpoly.natDegree = m := by
    rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  have hcp : M.charpoly = Polynomial.X ^ m := by
    ext n
    rw [Polynomial.coeff_X_pow]
    rcases lt_trichotomy n m with hn | hn | hn
    · rw [if_neg hn.ne]
      have := h (m - n) (by omega) (by omega)
      rwa [show m - (m - n) = n by omega] at this
    · rw [if_pos hn, hn]
      have := M.charpoly_monic.leadingCoeff
      rwa [Polynomial.leadingCoeff, hdeg] at this
    · rw [if_neg hn.ne']
      apply Polynomial.coeff_eq_zero_of_natDegree_lt
      rw [hdeg]
      exact hn
  have := Matrix.aeval_self_charpoly M
  rwa [hcp, map_pow, Polynomial.aeval_X] at this

theorem compact_zero_holds : CmpZero := by
  intro k r z Bs hz hT hB Ξ hΞ hcp X hX
  have hnil := cp_pow (cmp Ξ Bs) hcp
  have hskew : (cmp Ξ Bs)ᴴ = -(cmp Ξ Bs) := by
    ext a b
    rw [Matrix.conjTranspose_apply, Matrix.neg_apply, cmp_eq, cmp_eq, JfS.Sym.herm_skew hΞ (Bs a) (Bs b),
      JfS.Sym.herm_swap (Bs a), neg_neg]
  have hzero := skew_nil_zero _ hskew k hnil
  have hc : ∀ a b, herm (Hpk k r) (Ξ *ᵥ Bs a) (Bs b) = 0 := by
    intro a b
    rw [← cmp_eq, hzero]
    rfl
  set Y : B.Mat k r := ∑ a, ∑ b, herm (Hpk k r) (X *ᵥ Bs b) (Bs a) • vecMulVec (Bs a) (star (Hpk k r *ᵥ Bs b))
    with hY
  have hv : ∀ v, X *ᵥ v = Y *ᵥ v := by
    intro v
    rw [row_in hz hT hB hX v, hY]
    simp only [sum_mulVec', smul_mulVec'', JfS.Sym.vmv_mulVec, JfS.Sym.star_hpk_dot]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    conv_lhs => rw [col_in hz hT hB hX (Bs b)]
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [smul_smul, smul_smul, mul_comm (herm (Hpk k r) v (Bs b))]
  have hXY : X = Y := by
    ext i j
    rw [JfS.Sym.mat_eq_mulVec_bvec X i j, JfS.Sym.mat_eq_mulVec_bvec Y i j, hv]
  have htr : Matrix.trace (Ξ * X) = 0 := by
    rw [hXY, hY]
    simp only [Finset.mul_sum, Matrix.trace_sum, Matrix.mul_smul, Matrix.trace_smul, trace_vmv, hc, smul_zero,
      Finset.sum_const_zero]
  rw [htr, Complex.zero_re]

end

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity.CmpZeroPf

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

theorem compact_zero_holds : CmpZero := CmpZeroPf.compact_zero_holds

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
