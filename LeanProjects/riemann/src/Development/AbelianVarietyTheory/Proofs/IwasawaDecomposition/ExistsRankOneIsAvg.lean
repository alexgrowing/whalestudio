import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsAvgClosure
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InnerKAvgNeZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompactAverageKFiniteFiniteRankStatement

open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum
open scoped InnerProductSpace Topology

namespace GlobalTheory.TypeSum

theorem eq_zero_of_sum_coef {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Mx n → (H →L[ℂ] H)} {d : ℝ} (hd : IsFdeg (muG ε) σ d) {m : ℕ} {a y : Fin m → H} (ha : Orthonormal ℂ a)
    (h0 : ∀ g ∈ UJset ε, ∑ j, ⟪y j, σ g (a j)⟫_ℂ = 0) (k : Fin m) : y k = 0 := by
  have h1 : ∫ g, ∑ j, coefOn σ (a j) (y j) g * star (coefOn σ (a k) (y k) g) ∂(muG ε) = 0 := by
    have : ∀ g : UJ ε, ∑ j, coefOn σ (a j) (y j) g * star (coefOn σ (a k) (y k) g) = 0 := fun g => by
      rw [← Finset.sum_mul]
      have := h0 (umat g) g.2
      simp only [coefOn]
      rw [this, zero_mul]
    simp only [this, integral_zero]
  rw [integral_finset_sum _ fun j _ => (hd.2 _ _ _ _).1] at h1
  simp only [fun j => (hd.2 (a j) (y j) (a k) (y k)).2, orthonormal_iff_ite.1 ha, ite_mul, ite_div, one_mul, zero_mul,
    zero_div, Finset.sum_ite_eq, Finset.mem_univ, if_true] at h1
  have hd' : (d : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hd.1.ne'
  exact inner_self_eq_zero.1 ((div_eq_zero_iff.1 h1).resolve_right hd')

theorem exists_rank_one_isAvg : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mx n → (H →L[ℂ] H)), Std ε σ → ∃ a c : H, a ≠ 0 ∧ c ≠ 0 ∧ IsKFin ε σ a ∧ IsKFin ε σ c ∧ IsAvg ε σ (fun w => ⟪c, w⟫_ℂ • a) := by
  intro n ε H _ _ _ σ h
  obtain ⟨hσ, -, -, ⟨d, hd⟩, b, hb, hb0⟩ := id h
  obtain ⟨A1, A2, A3, A4, A5⟩ := isAvg_closure n ε H σ hσ
  obtain ⟨B1, B2, -, -⟩ := kCoef_kAvg n ε H σ hσ
  have he := B1 b hb
  obtain ⟨m, a, c, ha, haK, hcK, hQ⟩ := GlobalTheory.T.compactAverage_kFinite_finiteRank n ε H σ h _ he
  have hQavg := A4 _ (by obtain ⟨F, -, h1, h2, -⟩ := he; exact h2 _ h1)
  have hc : ∃ k, c k ≠ 0 := by
    by_contra hc
    push_neg at hc
    apply B2 b hb0
    rw [hQ]; simp [hc]
  obtain ⟨k, hk⟩ := hc
  let V : Submodule ℂ (Fin m × Fin m → ℂ) :=
    Submodule.span ℂ ((fun g (p : Fin m × Fin m) => ⟪c p.1, σ g (a p.2)⟫_ℂ) '' UJset ε)
  have hV : ∀ M ∈ V, IsAvg ε σ (fun w => ∑ i, ∑ j, (M (i, j) * ⟪c j, w⟫_ℂ) • a i) := by
    intro M hM
    induction hM using Submodule.span_induction with
    | mem M hM =>
      obtain ⟨g, hg, rfl⟩ := hM
      have := (A2 _ _ hQavg (A2 _ _ (A1 g hg) hQavg).2).2
      simp only [hQ, map_sum, map_smul, inner_sum, inner_smul_right, Finset.sum_smul] at this
      simpa only [mul_comm] using this
    | zero => simpa using A5
    | add M N _ _ hM hN =>
      simpa only [Pi.add_apply, add_mul, add_smul, Finset.sum_add_distrib] using (A2 _ _ hM hN).1
    | smul t M _ hM =>
      simpa only [Pi.smul_apply, smul_eq_mul, Finset.smul_sum, smul_smul, mul_assoc] using A3 t _ hM
  have hN : (fun p : Fin m × Fin m => if p.2 = k then ⟪c p.1, c k⟫_ℂ else 0) ∈ V := by
    rw [← Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff]
    intro φ hφ
    rw [Submodule.mem_dualAnnihilator] at hφ
    have e : ∀ z : Fin m → H, φ (fun p => ⟪c p.1, z p.2⟫_ℂ) =
        ∑ j, ⟪∑ i, star (φ fun q => if (i, j) = q then 1 else 0) • c i, z j⟫_ℂ := fun z => by
      rw [LinearMap.pi_apply_eq_sum_univ, Fintype.sum_prod_type, Finset.sum_comm]
      simp [sum_inner, inner_smul_left, mul_comm]
    have hy := eq_zero_of_sum_coef hd ha (y := fun j => ∑ i, star (φ fun q => if (i, j) = q then 1 else 0) • c i)
      (fun g hg => by rw [← e fun j => σ g (a j)]; exact hφ _ (Submodule.subset_span ⟨g, hg, rfl⟩))
    have := e fun j => if j = k then c k else 0
    simp only [hy, inner_zero_left, Finset.sum_const_zero] at this
    refine Eq.trans (congrArg φ ?_) this
    funext p
    by_cases hp : p.2 = k <;> simp [hp]
  refine ⟨∑ i, ⟪c i, c k⟫_ℂ • a i, c k, fun h0 => hk ?_, hk,
    (kfin ε σ).sum_mem fun i _ => (kfin ε σ).smul_mem _ (haK i), hcK k, ?_⟩
  · have := ha.inner_right_fintype (fun i => ⟪c i, c k⟫_ℂ) k
    rw [h0, inner_zero_right] at this
    exact inner_self_eq_zero.1 this.symm
  · have := hV _ hN
    simp only [ite_mul, zero_mul, ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true] at this
    simpa only [Finset.smul_sum, smul_smul, mul_comm] using this

end GlobalTheory.TypeSum
