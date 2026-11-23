import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.UnitaryExtremality.SatPowNonvan
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConjTransposeAntidiagFixed

noncomputable section

open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct GlobalTheory.CompanionTheory.SwapRoot Matrix

namespace GlobalTheory.CompanionTheory.SwapRoot

variable {L : Type} [Field L]

theorem partner_wU (σ : L →+* L) : partner σ (wU L) = w2 L := by
  have hw : (((wU L)⁻¹ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) = w2 L := rfl
  have hc : cT σ (w2 L) = w2 L := by
    delta cT w2
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  delta partner
  rw [hw, hc, weyl_mul_weyl, one_mul]

variable [Valued L (WithZero (Multiplicative ℤ))]

theorem cM_conj_int {n : ℕ} (c : Fin 2 → Fin n) (P : Matrix (Fin 2) (Fin 2) L)
    (hP : ∀ p r, Valued.v (P p r) ≤ 1) (b d : Fin n) :
    Valued.v ((cM L c * P * (cM L c)ᵀ) b d) ≤ 1 := by
  have hA : ∀ (x : Fin n) (p : Fin 2), Valued.v (cM L c x p) ≤ 1 := by
    intro x p
    show Valued.v (if x = c p then (1 : L) else 0) ≤ 1
    split_ifs <;> simp
  rw [Matrix.mul_apply]
  refine Valuation.map_sum_le (Valued.v : Valuation L (WithZero (Multiplicative ℤ))) fun r _ => ?_
  rw [Valuation.map_mul, Matrix.transpose_apply, Matrix.mul_apply]
  refine mul_le_one' ?_ (hA d r)
  refine Valuation.map_sum_le (Valued.v : Valuation L (WithZero (Multiplicative ℤ))) fun p _ => ?_
  rw [Valuation.map_mul]
  exact mul_le_one' (hA b p) (hP p r)

theorem weyl_sub_one_entries_integral (p r : Fin 2) : Valued.v ((w2 L - 1) p r) ≤ 1 := by
  delta w2
  fin_cases p <;> fin_cases r <;> simp [Matrix.one_apply]

theorem block_matrix_weyl_integral {n : ℕ} (a : ℕ) (h : 2 * (a + 2) ≤ n) :
    Formalism.UG.P.fIwasawaInt (blockM a h (w2 L) (w2 L)) := by
  delta blockM
  intro i j
  simp only [Matrix.add_apply]
  refine Valuation.map_add_le _ (Valuation.map_add_le _ ?_ (cM_conj_int _ _ weyl_sub_one_entries_integral i j))
    (cM_conj_int _ _ weyl_sub_one_entries_integral i j)
  rw [Matrix.one_apply]
  split_ifs <;> simp

theorem sR_mem_KU : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L)
    (σ : L →+* L) (q n : ℕ) (hU : IsUnramInv ϖ σ q) (a : ℕ) (h : 2 * (a + 2) ≤ n),
    sR σ hU.1 a h ∈ KU σ n := by
  intro L _ _ ϖ σ q n hU a h
  have hval : (((sR σ hU.1 a h : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) =
      blockM a h (w2 L) (w2 L) := by
    show blockM a h (w2 L) (partner σ (wU L)) = _
    rw [partner_wU]
  have hwinv : (wU L)⁻¹ = wU L := Units.ext rfl
  have hginv : (sR σ hU.1 a h)⁻¹ = sR σ hU.1 a h := by
    show ((rootHom σ hU.1 a h) (wU L))⁻¹ = (rootHom σ hU.1 a h) (wU L)
    rw [← map_inv, hwinv]
  have hBB : blockM a h (w2 L) (w2 L) * blockM a h (w2 L) (w2 L) = 1 := by
    have h1 := ((sR σ hU.1 a h : GU σ n) : GL (Fin n) L).mul_inv
    rw [← Subgroup.coe_inv, hginv, hval] at h1
    exact h1
  have hint : ∀ i j, blockM a h (w2 L) (w2 L) i j ∈ intL L := fun i j => block_matrix_weyl_integral (L := L) a h i j
  let Bi : Matrix (Fin n) (Fin n) (intL L) := Matrix.of fun i j => ⟨blockM a h (w2 L) (w2 L) i j, hint i j⟩
  have hBi : ∀ i j, ((Bi * Bi) i j : L) = (blockM a h (w2 L) (w2 L) * blockM a h (w2 L) (w2 L)) i j := by
    intro i j
    simp [Bi, Matrix.mul_apply]
  have hy : Bi * Bi = 1 := by
    ext i j
    rw [hBi, hBB, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  show ((sR σ hU.1 a h : GU σ n) : GL (Fin n) L) ∈ GU σ n ⊓ (bc (intL L).subtype).range
  refine Subgroup.mem_inf.2 ⟨(sR σ hU.1 a h).2, ⟨⟨Bi, Bi, hy, hy⟩, ?_⟩⟩
  apply Units.ext
  rw [hval]
  ext i j
  rfl

end GlobalTheory.CompanionTheory.SwapRoot

end
