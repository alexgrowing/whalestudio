import Formalism.LocalToGlobal.ProjectiveLattices.CurveOpen

noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {D : D7} {T : Top D} (h : LawsP T) {j : ℕ} (hj : InR D j)

include h hj

theorem esec_mem_C {w : WeightFamilies.Wt D j} {f : T.R j} : f ∈ cutR T.C j w ↔ f ∈ T.C j w := by
  rw [cutR_eq T.C hj]

theorem esec_mul_mem {w w' : WeightFamilies.Wt D j} {f g : T.R j} (hf : f ∈ cutR T.C j w) (hg : g ∈ cutR T.C j w') :
    f * g ∈ cutR T.C j (wadd w w') := by
  rw [esec_mem_C h hj] at hf hg ⊢
  exact h.toLawsCore.mul j hj w w' f hf g hg

def esecMul {w w' : WeightFamilies.Wt D j} (F : (recB h.toLawsCore).Cusp j w) (F' : (recB h.toLawsCore).Cusp j w') :
    (recB h.toLawsCore).Cusp j (wadd w w') :=
  ⟨(F : T.R j) * (F' : T.R j), esec_mul_mem h hj F.2 F'.2⟩

theorem esecMul_coe {w w' : WeightFamilies.Wt D j} (F : (recB h.toLawsCore).Cusp j w)
    (F' : (recB h.toLawsCore).Cusp j w') :
    ((esecMul h hj F F' : (recB h.toLawsCore).Cusp j (wadd w w')) : T.R j) = (F : T.R j) * (F' : T.R j) := rfl

theorem esec_inc_apply {w : WeightFamilies.Wt D j} (F : (recB h.toLawsCore).Cusp j w) :
    (recPJ h j hj).inc w F = AddMonoidAlgebra.single (deg w) (F : T.R j) := rfl

theorem esec_inc_mul {w w' : WeightFamilies.Wt D j} (F : (recB h.toLawsCore).Cusp j w)
    (F' : (recB h.toLawsCore).Cusp j w') :
    (recPJ h j hj).inc (wadd w w') (esecMul h hj F F') = (recPJ h j hj).inc w F * (recPJ h j hj).inc w' F' :=
  (incG_mul deg (cutR T.C j) (deg_wadd w w') F F' (esec_mul_mem h hj F.2 F'.2)).symm

def esecW (wL : WeightFamilies.Wt D j) : ℕ → WeightFamilies.Wt D j
  | 0 => wL
  | n + 1 => wadd wL (esecW wL n)

omit h hj in
theorem esecW_eq (wL : WeightFamilies.Wt D j) (n : ℕ) : esecW wL n = addL (wt0 D j) wL (n + 1) := by
  induction n with
  | zero => exact (add_zero_weight_one_eq wL).symm
  | succ n ih => rw [esecW, ih, wadd_addL]

def esecPow {wL : WeightFamilies.Wt D j} (F : (recB h.toLawsCore).Cusp j wL) :
    (n : ℕ) → (recB h.toLawsCore).Cusp j (esecW wL n)
  | 0 => F
  | n + 1 => esecMul h hj F (esecPow F n)

theorem esec_inc_pow {wL : WeightFamilies.Wt D j} (F : (recB h.toLawsCore).Cusp j wL) (n : ℕ) :
    (recPJ h j hj).inc (esecW wL n) (esecPow h hj F n) = (recPJ h j hj).inc wL F ^ (n + 1) := by
  induction n with
  | zero => rw [zero_add, pow_one]; rfl
  | succ n ih =>
    show (recPJ h j hj).inc (wadd wL (esecW wL n)) (esecMul h hj F (esecPow h hj F n)) = _
    rw [esec_inc_mul, ih, pow_succ' _ (n + 1)]

theorem esec_mem_mulL {wL : WeightFamilies.Wt D j} {a b : ℕ} {f g : T.R j}
    (hf : f ∈ cutR T.C j (addL (wt0 D j) wL a)) (hg : g ∈ cutR T.C j (addL (wt0 D j) wL b)) :
    f * g ∈ cutR T.C j (addL (wt0 D j) wL (a + b)) := by
  have := esec_mul_mem h hj hf hg
  rwa [wadd_addL_addL, zero_weight_add] at this

theorem esec_pow_mem {wL : WeightFamilies.Wt D j} {f : T.R j} (hf : f ∈ cutR T.C j wL) (n : ℕ) :
    f ^ (n + 1) ∈ cutR T.C j (addL (wt0 D j) wL (n + 1)) := by
  induction n with
  | zero => rw [zero_add, pow_one, add_zero_weight_one_eq]; exact hf
  | succ n ih =>
    rw [pow_succ]
    have hf' : f ∈ cutR T.C j (addL (wt0 D j) wL 1) := by rw [add_zero_weight_one_eq]; exact hf
    exact esec_mem_mulL h hj ih hf'

theorem esec_monomial_mem {N : ℕ} {wL : WeightFamilies.Wt D j} (x : Fin N → T.R j) (hx : ∀ i, x i ∈ cutR T.C j wL)
    (α : Fin N →₀ ℕ) :
    α = 0 ∨ (α.prod fun i k => x i ^ k) ∈ cutR T.C j (addL (wt0 D j) wL (α.sum fun _ k => k)) := by
  classical
  induction α using Finsupp.induction with
  | zero => exact Or.inl rfl
  | single_add a b f ha hb ih =>
    right
    obtain ⟨b, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hb
    rw [Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _),
      Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl), Finsupp.prod_single_index (h := fun i k => x i ^ k) (pow_zero _),
      Finsupp.sum_single_index rfl]
    rcases ih with h0 | hmem
    · subst h0
      simp only [Finsupp.prod_zero_index, Finsupp.sum_zero_index, mul_one, add_zero]
      exact esec_pow_mem h hj (hx a) b
    · exact esec_mem_mulL h hj (esec_pow_mem h hj (hx a) b) hmem

theorem esec_hom_mem {N : ℕ} {wL : WeightFamilies.Wt D j} (x : Fin N → T.R j) (hx : ∀ i, x i ∈ cutR T.C j wL)
    (P : MvPolynomial (Fin N) T.Q.c.F) {k : ℕ} (hP : P.IsHomogeneous (k + 1)) :
    MvPolynomial.aeval x P ∈ cutR T.C j (addL (wt0 D j) wL (k + 1)) := by
  classical
  rw [P.as_sum, map_sum]
  refine Submodule.sum_mem _ fun α hα => ?_
  rw [MvPolynomial.aeval_monomial, ← Algebra.smul_def]
  refine Submodule.smul_mem _ _ ?_
  have hdeg : (α.sum fun _ k => k) = k + 1 := by
    have := hP (MvPolynomial.mem_support_iff.mp hα)
    rw [Finsupp.weight_apply] at this
    simpa using this
  rcases esec_monomial_mem h hj x hx α with h0 | hmem
  · subst h0
    simp at hdeg
  · rwa [hdeg] at hmem

theorem esec_evC_aeval (hG : GenFrEx (T.Q.Xo j) T.Q.c) (hT : GenFromTest (T.Q.Xo j) T.Q.c hG)
    (Z : Comp (T.Q.Xo j) T.Q.c) {N : ℕ} (x : Fin N → T.R j) (P : MvPolynomial (Fin N) T.Q.c.F) :
    evC hG Z (MvPolynomial.aeval x P) = MvPolynomial.aeval (fun i => evC hG Z (x i)) P := by
  rw [← evCAlg_apply hG hT Z]
  exact DFunLike.congr_fun (MvPolynomial.comp_aeval x (evCAlg hG hT Z)) P

end Formalism.L2.Pj
