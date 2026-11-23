import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.BlocksRel

noncomputable section

open Matrix Set Filter Topology Polynomial
open scoped ComplexOrder

namespace PositivityTheory.Rg.Sw.AbsSt.DF

open PositivityTheory.Rg.Sw

variable {n : ℕ}

def nbU (l : ℝ) : GL (Fin n ⊕ Fin n) ℂ where
  val := fromBlocks 1 0 ((l : ℂ) • 1) 1
  inv := fromBlocks 1 0 (-((l : ℂ) • 1)) 1
  val_inv := by simp [fromBlocks_multiply, ← fromBlocks_one]
  inv_val := by simp [fromBlocks_multiply, ← fromBlocks_one]

theorem nbU_mem (l : ℝ) : nbU (n := n) l ∈ GR n := by
  change InG (fromBlocks 1 0 ((l : ℂ) • 1) 1)
  simp only [InG, JJ, fromBlocks_conjTranspose, fromBlocks_multiply]
  congr 1 <;> simp [Matrix.smul_eq_diagonal_mul]

def nbG (l : ℝ) : GR n := ⟨nbU l, nbU_mem l⟩

theorem nbG_zero : nbG (n := n) 0 = 1 := by
  apply ext_mR
  show fromBlocks 1 0 (((0 : ℝ) : ℂ) • 1) 1 = 1
  simp [fromBlocks_one]

theorem cont_nbG : Continuous (nbG (n := n)) := by
  apply Continuous.subtype_mk
  rw [Units.continuous_iff]
  constructor
  · show Continuous fun l : ℝ => (fromBlocks 1 0 ((l : ℂ) • 1) 1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ)
    refine continuous_pi fun i => continuous_pi fun j => ?_
    rcases i with i | i <;> rcases j with j | j <;> simp <;> fun_prop
  · show Continuous fun l : ℝ => (fromBlocks 1 0 (-((l : ℂ) • 1)) 1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ)
    refine continuous_pi fun i => continuous_pi fun j => ?_
    rcases i with i | i <;> rcases j with j | j <;> simp <;> fun_prop

theorem nbG_low (l : ℝ) (y : GR n) :
    (mR (nbG l * y)).toBlocks₂₁ = (l : ℂ) • (mR y).toBlocks₁₁ + (mR y).toBlocks₂₁ := by
  have hm : mR (nbG l * y) = fromBlocks 1 0 ((l : ℂ) • 1) 1 * mR y := rfl
  rw [hm]
  conv_lhs => rw [← fromBlocks_toBlocks (mR y)]
  rw [fromBlocks_multiply, toBlocks_fromBlocks₂₁]
  simp

theorem det_I (y : GR n) : (Complex.I • (mR y).toBlocks₁₁ + (mR y).toBlocks₂₁).det ≠ 0 := by
  intro hdet
  obtain ⟨x, hx0, hx⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  let v : Fin n ⊕ Fin n → ℂ := Sum.elim x 0
  have hYv : mR y *ᵥ v = Sum.elim ((mR y).toBlocks₁₁ *ᵥ x) ((mR y).toBlocks₂₁ *ᵥ x) := by
    conv_lhs => rw [← fromBlocks_toBlocks (mR y)]
    rw [fromBlocks_mulVec]
    simp [v]
  have hCx : (mR y).toBlocks₂₁ *ᵥ x = -(Complex.I • ((mR y).toBlocks₁₁ *ᵥ x)) := by
    rw [add_mulVec, smul_mulVec] at hx
    rw [eq_neg_iff_add_eq_zero, add_comm]
    exact hx
  have hy : (mR y)ᴴ * JJ n * mR y = JJ n := y.2
  have hform : star (mR y *ᵥ v) ⬝ᵥ (JJ n *ᵥ (mR y *ᵥ v)) = 0 := by
    rw [star_mulVec, mulVec_mulVec, dotProduct_mulVec, vecMul_vecMul, ← Matrix.mul_assoc, hy,
      ← dotProduct_mulVec]
    simp [v, JJ, fromBlocks_mulVec, dotProduct, Fintype.sum_sum_type]
  rw [hYv, hCx] at hform
  simp [JJ, fromBlocks_mulVec, dotProduct, Fintype.sum_sum_type] at hform
  set u := (mR y).toBlocks₁₁ *ᵥ x with hu
  simp only [neg_mulVec, Pi.neg_apply] at hform
  have h3 : (-2 * Complex.I) * ∑ i, starRingEnd ℂ (u i) * u i = 0 := by
    rw [← hform, Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have h2 : ∑ i, starRingEnd ℂ (u i) * u i = 0 :=
    (mul_eq_zero.mp h3).resolve_left (by simp [Complex.I_ne_zero])
  have hu0 : u = 0 := by
    rw [← dotProduct_star_self_eq_zero]
    simpa [dotProduct] using h2
  have hYv0 : mR y *ᵥ v = 0 := by
    rw [hYv, hCx, hu0]
    ext i
    rcases i with i | i <;> simp
  have hinv : mR y⁻¹ * mR y = 1 := congrArg mR (inv_mul_cancel y)
  have hv : v = 0 := by
    rw [← one_mulVec v, ← hinv, ← mulVec_mulVec, hYv0, mulVec_zero]
  apply hx0
  funext i
  exact congrFun hv (Sum.inl i)

theorem finite_bad (y : GR n) :
    {l : ℝ | ((l : ℂ) • (mR y).toBlocks₁₁ + (mR y).toBlocks₂₁).det = 0}.Finite := by
  let M : Matrix (Fin n) (Fin n) ℂ[X] :=
    (X : ℂ[X]) • (mR y).toBlocks₁₁.map (Polynomial.C : ℂ →+* ℂ[X]) + (mR y).toBlocks₂₁.map (Polynomial.C : ℂ →+* ℂ[X])
  let p : ℂ[X] := M.det
  have hev : ∀ z : ℂ, p.eval z = (z • (mR y).toBlocks₁₁ + (mR y).toBlocks₂₁).det := by
    intro z
    have h := RingHom.map_det (Polynomial.evalRingHom z) M
    rw [Polynomial.coe_evalRingHom] at h
    rw [h]
    congr 1
    ext i j
    simp [M]
    ring
  have hp : p ≠ 0 := by
    intro h0
    apply det_I y
    rw [← hev, h0, Polynomial.eval_zero]
  apply (p.roots.toFinset.finite_toSet.preimage Complex.ofReal_injective.injOn).subset
  intro l hl
  simp only [Set.mem_setOf_eq] at hl
  rw [Set.mem_preimage, Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_roots hp]
  exact (hev _).trans hl

theorem dense_cell : Dense {y : GR n | (mR y).toBlocks₂₁.det ≠ 0} := by
  rw [dense_iff_closure_eq, Set.eq_univ_iff_forall]
  intro y
  have hS := finite_bad y
  set S := {l : ℝ | ((l : ℂ) • (mR y).toBlocks₁₁ + (mR y).toBlocks₂₁).det = 0} with hSdef
  have hT : (S \ {0})ᶜ ∈ 𝓝 (0 : ℝ) :=
    (hS.diff (s := S) (t := {0})).isClosed.isOpen_compl.mem_nhds (by simp)
  have hcont : Continuous fun t : ℝ => nbG (n := n) t * y := cont_nbG.mul continuous_const
  have htend : Tendsto (fun t : ℝ => nbG (n := n) t * y) (𝓝[≠] 0) (𝓝 y) := by
    have h := (hcont.tendsto 0).mono_left (nhdsWithin_le_nhds (s := {0}ᶜ))
    simpa [nbG_zero] using h
  apply mem_closure_of_tendsto htend
  filter_upwards [nhdsWithin_le_nhds hT, self_mem_nhdsWithin] with t h1 h2
  simp only [Set.mem_setOf_eq, nbG_low]
  intro hdet
  exact h1 ⟨hdet, h2⟩

end PositivityTheory.Rg.Sw.AbsSt.DF
