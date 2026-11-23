import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.LoweringDerivativeVacuum

noncomputable section

open Matrix Filter Topology MeasureTheory
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.HSt.LoweringDerivative

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.HSt

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

private theorem JJ_sq_eq_neg_one : JJ n * JJ n = -1 := by
  rw [JJ, fromBlocks_multiply, ← fromBlocks_one, fromBlocks_neg]
  simp

private theorem inG_mul_JJ_mul_conjTranspose_eq_JJ {x : M2 n} (hx : InG x) : x * JJ n * xᴴ = JJ n := by
  have hJ := (JJ_sq_eq_neg_one (n := n))
  have hx' : xᴴ * JJ n * x = JJ n := hx
  have h1 : (-(JJ n * xᴴ * JJ n)) * x = 1 := by
    calc (-(JJ n * xᴴ * JJ n)) * x = -(JJ n * (xᴴ * JJ n * x)) := by
          simp only [Matrix.neg_mul, Matrix.mul_assoc]
      _ = 1 := by rw [hx', hJ, neg_neg]
  have h2 : x * (-(JJ n * xᴴ * JJ n)) = 1 := mul_eq_one_comm.mp h1
  calc x * JJ n * xᴴ = x * (-(JJ n * xᴴ * JJ n)) * JJ n := by
        simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc, hJ, Matrix.mul_one, neg_neg]
    _ = JJ n := by rw [h2, Matrix.one_mul]

private theorem toBlocks₂_relations_of_inG {x : M2 n} (hx : InG x) :
    toBlocks₂₁ x * (toBlocks₂₂ x)ᴴ = toBlocks₂₂ x * (toBlocks₂₁ x)ᴴ ∧
    toBlocks₂₁ x * (toBlocks₁₂ x)ᴴ - toBlocks₂₂ x * (toBlocks₁₁ x)ᴴ = -1 := by
  have e := inG_mul_JJ_mul_conjTranspose_eq_JJ hx
  rw [← fromBlocks_toBlocks x] at e
  simp only [JJ, fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_inj,
    toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂] at e
  simp at e
  refine ⟨?_, ?_⟩
  · have h := e.2.2.2
    rw [neg_add_eq_sub, sub_eq_zero] at h
    exact h
  · have h := e.2.2.1
    rwa [neg_add_eq_sub] at h

private theorem det_smul_toBlocks₂₁_add_toBlocks₂₂_ne_zero {x : M2 n} (hx : InG x) (t : ℂ) (ht : t ≠ star t) :
    (t • toBlocks₂₁ x + toBlocks₂₂ x).det ≠ 0 := by
  intro h0
  obtain ⟨v, hv, hvM⟩ := exists_vecMul_eq_zero_iff.mpr h0
  obtain ⟨hC, hA⟩ := toBlocks₂_relations_of_inG hx
  rw [Matrix.vecMul_add, Matrix.vecMul_smul] at hvM
  have hβ : v ᵥ* toBlocks₂₂ x = -t • (v ᵥ* toBlocks₂₁ x) := by
    rw [neg_smul, ← sub_eq_zero, sub_neg_eq_add, add_comm]
    exact hvM
  have key : (v ᵥ* toBlocks₂₁ x) ⬝ᵥ star (v ᵥ* toBlocks₂₂ x)
      = (v ᵥ* toBlocks₂₂ x) ⬝ᵥ star (v ᵥ* toBlocks₂₁ x) := by
    have h := congrArg (fun M => (v ᵥ* M) ⬝ᵥ star v) hC
    have e1 : (v ᵥ* (toBlocks₂₁ x * (toBlocks₂₂ x)ᴴ)) ⬝ᵥ star v
        = (v ᵥ* toBlocks₂₁ x) ⬝ᵥ star (v ᵥ* toBlocks₂₂ x) := by
      rw [← vecMul_vecMul, ← dotProduct_mulVec, star_vecMul]
    have e2 : (v ᵥ* (toBlocks₂₂ x * (toBlocks₂₁ x)ᴴ)) ⬝ᵥ star v
        = (v ᵥ* toBlocks₂₂ x) ⬝ᵥ star (v ᵥ* toBlocks₂₁ x) := by
      rw [← vecMul_vecMul, ← dotProduct_mulVec, star_vecMul]
    rw [← e1, ← e2]
    exact h
  rw [hβ, star_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul] at key
  have hs : (v ᵥ* toBlocks₂₁ x) ⬝ᵥ star (v ᵥ* toBlocks₂₁ x) = 0 := by
    have h3 : (t - star t) * ((v ᵥ* toBlocks₂₁ x) ⬝ᵥ star (v ᵥ* toBlocks₂₁ x)) = 0 := by
      rw [star_neg] at key
      linear_combination key
    rcases mul_eq_zero.mp h3 with h4 | h4
    · exact absurd (sub_eq_zero.mp h4) ht
    · exact h4
  have hα : v ᵥ* toBlocks₂₁ x = 0 := by
    open scoped ComplexOrder in exact dotProduct_self_star_eq_zero.mp hs
  have hβ0 : v ᵥ* toBlocks₂₂ x = 0 := by rw [hβ, hα, smul_zero]
  have h5 := congrArg (fun M => v ᵥ* M) hA
  simp only [Matrix.vecMul_sub, ← vecMul_vecMul, hα, hβ0, zero_vecMul, sub_self, vecMul_neg,
    vecMul_one] at h5
  exact hv (neg_eq_zero.mp h5.symm)

theorem det_second_cayley_block_ne {x : M2 n} (hx : InG x) : (u2 x).det ≠ 0 := by
  have h := det_smul_toBlocks₂₁_add_toBlocks₂₂_ne_zero hx (-Complex.I) (by
    rw [star_neg, Complex.star_def, Complex.conj_I, neg_neg]
    intro h
    have := congrArg Complex.im h
    norm_num at this)
  rw [neg_smul] at h
  exact h

theorem inG_of_inK {g : M2 n} (h : InK g) : InG g := h.1

private theorem det_ne_zero_of_inG' {x : M2 n} (hx : InG x) : x.det ≠ 0 := by
  have hJ : JJ n * JJ n = -1 := by
    rw [JJ, fromBlocks_multiply, ← fromBlocks_one, fromBlocks_neg]
    simp
  have hx' : xᴴ * JJ n * x = JJ n := hx
  have h1 : (-(JJ n * xᴴ * JJ n)) * x = 1 := by
    calc (-(JJ n * xᴴ * JJ n)) * x = -(JJ n * (xᴴ * JJ n * x)) := by
          simp only [Matrix.neg_mul, Matrix.mul_assoc]
      _ = 1 := by rw [hx', hJ, neg_neg]
  exact (Matrix.isUnit_det_of_left_inverse h1).ne_zero

theorem continuous_rhoP {Kg : Type} [TopologicalSpace Kg] (ι : Kg → M2 n) (hι : Continuous ι)
    (hK : ∀ k, InG (ι k)) (m : ℕ) (e : ℤ) (Y : Matrix (Fin n) (Fin n) ℂ) : Continuous (rhoP ι m e Y) := by
  have hC : Continuous fun k => toBlocks₂₁ (ι k) :=
    continuous_matrix fun i j => hι.matrix_elem (Sum.inr i) (Sum.inl j)
  have hD : Continuous fun k => toBlocks₂₂ (ι k) :=
    continuous_matrix fun i j => hι.matrix_elem (Sum.inr i) (Sum.inr j)
  have hu1 : Continuous fun k => u1 (ι k) := by
    unfold u1
    fun_prop
  have hu2 : Continuous fun k => u2 (ι k) := by
    unfold u2
    fun_prop
  have hI : Complex.I ≠ star Complex.I := by
    rw [Complex.star_def, Complex.conj_I]
    intro h
    have := congrArg Complex.im h
    norm_num at this
  have hd1 : ∀ k, (u1 (ι k)).det ≠ 0 := fun k => det_smul_toBlocks₂₁_add_toBlocks₂₂_ne_zero (hK k) Complex.I hI
  have hinv : Continuous fun k => (u2 (ι k))⁻¹ := by
    rw [continuous_iff_continuousAt]
    intro k
    refine (continuousAt_matrix_inv _ ?_).comp hu2.continuousAt
    rw [Ring.inverse_eq_inv']
    exact continuousAt_inv₀ (det_second_cayley_block_ne (hK k))
  have hdet : Continuous fun k => (ι k).det := hι.matrix_det
  unfold rhoP fz
  simp only [neg_zero, Complex.cpow_zero, mul_one]
  refine Continuous.star (Continuous.mul (Continuous.mul (hdet.zpow₀ e ?_) ?_)
    (Continuous.matrix_trace ((hinv.matrix_mul continuous_const).matrix_mul hu1)))
  · exact fun k => Or.inl (det_ne_zero_of_inG' (hK k))
  · exact (hu1.matrix_det).zpow₀ _ (fun k => Or.inl (hd1 k))

theorem one_upper_left_block : (1 : M2 n).toBlocks₁₁ = 1 := by ext i j; simp [toBlocks₁₁, Matrix.one_apply]
theorem one_lower_left_block : (1 : M2 n).toBlocks₂₁ = 0 := by ext i j; simp [toBlocks₂₁, Matrix.one_apply]
theorem one_lower_right_block : (1 : M2 n).toBlocks₂₂ = 1 := by ext i j; simp [toBlocks₂₂, Matrix.one_apply]

theorem fz_one (m : ℕ) (e : ℤ) (z : ℂ) : fz m e z (1 : M2 n) = 1 := by
  simp [fz, u1, ub1, one_upper_left_block, one_lower_left_block, one_lower_right_block]

theorem Om_one : Om (1 : M2 n) = -1 := by
  simp [Om, ub2, ub1, one_upper_left_block, one_lower_left_block]

theorem eQ_one (m : ℕ) (e : ℤ) (z : ℂ) (Q : Matrix (Fin n) (Fin n) ℂ) : eQ m e z Q (1 : M2 n) = -Q.trace := by
  simp [eQ, fz_one, Om_one]

theorem eQ_smul (m : ℕ) (e : ℤ) (z c : ℂ) (Q : Matrix (Fin n) (Fin n) ℂ) (x : M2 n) :
    eQ m e z (c • Q) x = c * eQ m e z Q x := by
  simp only [eQ, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]; ring

theorem asmLT : AsmLT := by
  unfold AsmLT LocTau
  intro hLT1 hLT2 hLT3 hCrux n m e hmn Kg _ _ _ _ _ _ μ _ ι hι hιK Q
  have hK : ∀ k, InG (ι k) := fun k => inG_of_inK ((hιK (ι k)).mpr ⟨k, rfl⟩)
  obtain ⟨P, ψ, a, b, x0, hψ, ha, hb, hx0, hder⟩ := hCrux n m e hmn Kg μ ι hι hιK
  obtain ⟨c, hc, hcEq⟩ := hLT2 n m e Kg μ ι hι hιK ψ a b hψ.1 hψ.2.1 ha hb
  have h1G : InG (1 : M2 n) := by simp [InG]
  have hc0 : c 0 = 0 := by
    have h3 := hLT3 n m e hmn Kg μ ι hι hιK (rhoP ι m e 1) ψ a b 1
      (continuous_rhoP ι hι hK m e 1) hψ ha hb h1G
    rw [hcEq 1 0 1 h1G, eQ_smul, eQ_one] at h3
    simp at h3
    rcases h3 with h | h
    · exact h
    · omega
  have hd : deriv c 0 ≠ 0 := by
    intro hd0
    apply hder
    set β := (u1 x0).det * (ub1 x0).det with hβdef
    set K0 := x0.det ^ e * (u1 x0).det ^ (-(m : ℤ)) * (Om x0 * Pᴴ).trace with hK0
    have hF : (fun z => tOp μ ι (rhoP ι m e P) ψ a b (fz m e z) x0)
        = fun z => c z * (K0 * β ^ (-z)) := by
      funext z
      rw [hcEq P z x0 hx0, eQ_smul]
      simp only [eQ, fz, hK0, hβdef]
      ring
    rw [hF]
    by_cases hβ : β = 0
    · have h0 : (fun z => c z * (K0 * β ^ (-z))) = fun _ => 0 := by
        funext z
        by_cases hz : z = 0
        · subst hz
          simp [hc0]
        · simp [hβ, Complex.zero_cpow (neg_ne_zero.mpr hz)]
      rw [h0]
      simp
    · have hg : HasDerivAt (fun z : ℂ => K0 * β ^ (-z)) (K0 * (β ^ (-(0 : ℂ)) * Complex.log β * (-1))) 0 :=
        (((hasDerivAt_id' (0 : ℂ)).neg).const_cpow (Or.inl hβ)).const_mul K0
      have h := ((hc 0).hasDerivAt.mul hg).deriv
      simp only [hd0, hc0, zero_mul, mul_zero, add_zero] at h
      exact h
  refine ⟨1, fun _ => rhoP ι m e Qᴴ, fun _ => ψ, fun _ => a, fun _ => b, dslope c 0, fun _ _ => 1,
    fun _ => continuous_rhoP ι hι hK m e _, fun _ => hψ, fun _ => ⟨ha, hb⟩, ?_, ?_,
    fun _ => differentiable_const _, ?_⟩
  · have h := (Complex.differentiableOn_dslope (s := Set.univ) (c := 0) Filter.univ_mem).mpr
      hc.differentiableOn
    exact differentiableOn_univ.mp h
  · rw [dslope_same]
    exact hd
  · intro z x hx
    simp only [Finset.univ_unique, Finset.sum_singleton, one_mul]
    rw [hLT1 n m e z Q x hx, hcEq Qᴴ z x hx, conjTranspose_conjTranspose, eQ_smul]
    have h := sub_smul_dslope c 0 z
    rw [sub_zero, hc0, sub_zero, smul_eq_mul] at h
    rw [← h]
    ring

end PositivityTheory.Rg.Sw.HSt.LoweringDerivative

namespace PositivityTheory.Rg.Sw.HSt

theorem asmLT : AsmLT := LoweringDerivative.asmLT

end PositivityTheory.Rg.Sw.HSt
