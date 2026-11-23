import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ColLieApply
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsEqMulProdMinors

noncomputable section

open MvPolynomial GlobalTheory.Capelli GlobalTheory.Harm GlobalTheory.Harm.HighestUnique

namespace GlobalTheory.DefLift.Joint

theorem X_mul_pderiv_mem {σ : Type} (u v : σ) (N : ℕ) (Q : MvPolynomial σ ℂ)
    (hQ : Q ∈ restrictTotalDegree σ ℂ N) : X u * pderiv v Q ∈ restrictTotalDegree σ ℂ N := by
  classical
  rw [Q.as_sum, map_sum, Finset.mul_sum]
  refine Submodule.sum_mem _ fun m hm => ?_
  rw [mem_restrictTotalDegree] at hQ ⊢
  have hd : (m.sum fun _ e => e) ≤ N := (le_totalDegree hm).trans hQ
  rw [pderiv_monomial]
  by_cases h : m v = 0
  · simp [h]
  · rw [X, monomial_mul]
    refine (totalDegree_monomial_le _ _).trans (le_trans (le_of_eq ?_) hd)
    have h1 : Finsupp.single v 1 ≤ m := by
      rw [Finsupp.single_le_iff]; omega
    have h2 : m = Finsupp.single v 1 + (m - Finsupp.single v 1) := (add_tsub_cancel_of_le h1).symm
    conv_rhs => rw [h2]
    rw [Finsupp.sum_add_index' (by simp) (by simp), Finsupp.sum_add_index' (by simp) (by simp)]
    simp
    rfl

theorem antitone_rowOp {σ J : Type} [Fintype σ] [Fintype J] {p : ℕ} (z : Fin p × J → σ)
    (hz : Function.Injective z) {P : MvPolynomial σ ℂ} (hP : P ≠ 0) (μ : Fin p → ℤ)
    (hup : ∀ a b, a < b → ∑ k, X (z (a, k)) * pderiv (z (b, k)) P = 0)
    (hwt : ∀ a, ∑ k, X (z (a, k)) * pderiv (z (a, k)) P = (μ a : ℂ) • P) : Antitone μ :=
  highest_weight_antitone (rowOp ℂ z) (rowOp_lie z hz) (restrictTotalDegree σ ℂ P.totalDegree)
    (fun i j w hw => by
      rw [rowOp_apply]
      exact Submodule.sum_mem _ fun _ _ => X_mul_pderiv_mem _ _ _ _ hw)
    P ((mem_restrictTotalDegree _ _ _).2 le_rfl) hP μ
    (fun a b h => (rowOp_apply _ _ _ _).trans (hup a b h))
    (fun a => (rowOp_apply _ _ _ _).trans (hwt a))

theorem degree_of_mem_support {σ J : Type} [Fintype J] (z : J → σ) {P : MvPolynomial σ ℂ} {w : ℤ}
    (h : ∑ k, X (z k) * pderiv (z k) P = (w : ℂ) • P) {m : σ →₀ ℕ} (hm : m ∈ P.support) :
    ((∑ k, m (z k) : ℕ) : ℤ) = w := by
  have := congrArg (coeff m) h
  rw [coeff_sum, coeff_smul] at this
  simp only [coeff_X_mul_pderiv, ← Finset.sum_mul, smul_eq_mul] at this
  have h2 := mul_right_cancel₀ (mem_support_iff.1 hm) this
  exact_mod_cast h2

theorem exists_eq_smul_base {T : Type} [Fintype T] {p n : ℕ} (h : p + 0 ≤ n)
    {P : Poly ℂ T p 0 (Fin n)} (hP : P ≠ 0) (κ : T → Fin n → ℤ) (μ : T → Fin p → ℤ)
    (hup : ∀ t k l, k < l → ∑ a, X (xVar t a k) * pderiv (xVar t a l) P = 0)
    (hwt : ∀ t k, ∑ a, X (xVar t a k) * pderiv (xVar t a k) P = (κ t k : ℂ) • P)
    (hup' : ∀ t a b, a < b → ∑ k, X (xVar t a k) * pderiv (xVar t b k) P = 0)
    (hwt' : ∀ t a, ∑ k, X (xVar t a k) * pderiv (xVar t a k) P = (μ t a : ℂ) • P) :
    ∃ r : ℂ, P = r • basePoly ℂ h (fun t => diffOf fun a : Fin p => (κ t (Fin.castLE (n := p) h a)).toNat)
      (fun _ _ => 0) := by
  classical
  let z : T → Fin p × Fin n → Var T p 0 (Fin n) := fun t w => xVar t w.1 w.2
  let y : T → Fin 0 × Fin n → Var T p 0 (Fin n) := fun t w => yVar t w.1 w.2
  have hz : ∀ t, Function.Injective (z t) := fun t u w e => by simpa [z, Prod.ext_iff] using e
  have hy : ∀ t, Function.Injective (y t) := fun t u w e => u.1.elim0
  have hzy : ∀ t u w, z t u ≠ y t w := fun t u w => w.1.elim0
  have hμ : ∀ t, Antitone (μ t) := fun t => antitone_rowOp (z t) (hz t) hP _ (hup' t) (hwt' t)
  have hκ : ∀ t, Antitone (κ t) := fun t =>
    antitone_rowOp (fun w : Fin n × Fin p => z t w.swap) ((hz t).comp Prod.swap_injective) hP _
      (hup t) (hwt t)
  let a : T → Fin p → ℕ := fun t i => (μ t i).toNat
  have ha : ∀ t, Antitone (a t) := fun t i j hij => Int.toNat_le_toNat (hμ t hij)
  have hdeg : ∀ t i, ∀ m ∈ P.support, ∑ k, m (xVar t i k) = a t i := fun t i m hm => by
    have := degree_of_mem_support (fun k => xVar t i k) (hwt' t i) hm
    simp only [a]
    omega
  have hinv : ∀ t (i j : Fin p), i < j → ∀ s : ℂ,
      bind₁ (fun v => X v + ∑ k, if v = z t (j, k) then C s * X (z t (i, k)) else 0) P = P :=
    fun t i j hij => ((rowAdd_invariant_iff (fun k => z t (i, k)) (fun k => z t (j, k))
      (fun k l e => by simpa using hz t e)
      (fun k l e => hij.ne (congrArg Prod.fst (hz t e))) P).out 2 1).1 (hup' t i j hij)
  have hw : ∀ t, κ t = mixedWeight n (a t) (fun _ : Fin 0 => 0) := fun t =>
    weight_eq_mixedWeight h (z t) (hz t) (y t) (hy t) (hzy t) (a t) _ (ha t) (fun i => i.elim0)
      (hdeg t) (fun i => i.elim0) (hinv t) (fun i => i.elim0) (fun _ i => i.elim0) (κ t) (hκ t)
      (fun k l hkl => by rw [mixedOp_apply]; simpa using hup t k l hkl)
      (fun k => by rw [mixedOp_apply]; simpa using hwt t k) hP
  have e : (fun t => diffOf fun i : Fin p => (κ t (Fin.castLE (n := p) h i)).toNat) = fun t => diffOf (a t) := by
    funext t
    congr 1
    funext i
    rw [hw t, mixedWeight_apply]
    simp
  rw [e]
  refine exists_eq_smul_basePoly h _ _ ?_ κ hκ (fun t k l hkl => by simpa using hup t k l hkl)
    fun t k => by simpa using hwt t k
  refine mem_rowHighest_iff_of_charZero.2 ⟨fun _ _ b => b.elim0, fun t i m hm => ?_,
    fun _ b => b.elim0, fun t i j hij s => ?_, fun _ b => b.elim0⟩
  · rw [partOf_diffOf (ha t)]; exact hdeg t i m hm
  · rw [rowAddX_eq_bind₁]; exact hinv t i j hij s

end GlobalTheory.DefLift.Joint

namespace GlobalTheory.DefLift

theorem joint_highest_proportional (ι : Type) [Fintype ι] (m n : ℕ) (hnm : n ≤ m) (P Q : Pol ι m n)
    (κ : ι → Fin m → ℤ) (μ μ' : ι → Fin n → ℤ) (hP : P ≠ 0)
    (h1 : ∀ τ k l, k < l → rowLie n τ k l P = 0 ∧ rowLie n τ k l Q = 0)
    (h2 : ∀ τ k, rowLie n τ k k P = (κ τ k : ℂ) • P ∧ rowLie n τ k k Q = (κ τ k : ℂ) • Q)
    (h3 : ∀ τ k l, k < l → colLie m τ k l P = 0 ∧ colLie m τ k l Q = 0)
    (h4 : ∀ τ k, colLie m τ k k P = (μ τ k : ℂ) • P ∧ colLie m τ k k Q = (μ' τ k : ℂ) • Q) :
    ∃ r : ℂ, Q = r • P := by
  by_cases hQ : Q = 0
  · exact ⟨0, by simp [hQ]⟩
  let f : ι × Fin m × Fin n → Var ι n 0 (Fin m) := fun v => xVar v.1 v.2.2 v.2.1
  have hf : Function.Injective f := fun u w e => by
    simp only [f, Prod.ext_iff, Sum.inl.injEq] at e
    exact Prod.ext e.1 (Prod.ext e.2.2 e.2.1)
  have hr : ∀ τ k l (R : Pol ι m n), rename f (rowLie n τ k l R) =
      ∑ a, X (xVar τ a k) * pderiv (xVar τ a l) (rename f R) := fun τ k l R => by
    rw [rowLie_apply, map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_mul, rename_X, ← pderiv_rename hf]
  have hc : ∀ τ k l (R : Pol ι m n), rename f (colLie m τ k l R) =
      ∑ a, X (xVar τ k a) * pderiv (xVar τ l a) (rename f R) := fun τ k l R => by
    rw [colLie_apply, map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_mul, rename_X, ← pderiv_rename hf]
  have hi := rename_injective (R := ℂ) f hf
  obtain ⟨r, er⟩ := Joint.exists_eq_smul_base (show n + 0 ≤ m from hnm)
    ((map_ne_zero_iff _ hi).2 hP) κ μ
    (fun t k l h => by rw [← hr, (h1 t k l h).1, map_zero])
    (fun t k => by rw [← hr, (h2 t k).1, map_smul])
    (fun t k l h => by rw [← hc, (h3 t k l h).1, map_zero])
    (fun t k => by rw [← hc, (h4 t k).1, map_smul])
  obtain ⟨s, es⟩ := Joint.exists_eq_smul_base (show n + 0 ≤ m from hnm)
    ((map_ne_zero_iff _ hi).2 hQ) κ μ'
    (fun t k l h => by rw [← hr, (h1 t k l h).2, map_zero])
    (fun t k => by rw [← hr, (h2 t k).2, map_smul])
    (fun t k l h => by rw [← hc, (h3 t k l h).2, map_zero])
    (fun t k => by rw [← hc, (h4 t k).2, map_smul])
  have hr0 : r ≠ 0 := by
    rintro rfl
    exact hP (hi (by rw [er, zero_smul, map_zero]))
  refine ⟨s / r, hi ?_⟩
  rw [map_smul, er, es, smul_smul, div_mul_cancel₀ _ hr0]

end GlobalTheory.DefLift

end
