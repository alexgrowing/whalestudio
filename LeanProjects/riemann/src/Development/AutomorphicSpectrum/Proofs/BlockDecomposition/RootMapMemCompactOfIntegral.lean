import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.UnitaryExtremality.SatPowNonvan
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConjTransposeAntidiagFixed
open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct GlobalTheory.CompanionTheory.SwapRoot

noncomputable section

namespace GlobalTheory.CompanionTheory.SwapRoot

section RootInt

variable {L : Type} [Field L]

theorem partner_nU (σ : L →+* L) (x : L) : partner σ (nU x) = !![1, -σ x; 0, 1] := by
  have hi : (((nU x)⁻¹ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) = !![1, -x; 0, 1] := rfl
  have hc : cT σ (!![1, -x; 0, 1] : Matrix (Fin 2) (Fin 2) L) = !![1, 0; -σ x, 1] := by
    ext p r
    fin_cases p <;> fin_cases r <;> simp [cT]
  simp only [partner, hi, hc, w2]
  rw [Matrix.mul_fin_two, Matrix.mul_fin_two]
  simp

variable [Valued L (WithZero (Multiplicative ℤ))]

theorem val_cM_conj_le_one {n : ℕ} (c : Fin 2 → Fin n) (P : Matrix (Fin 2) (Fin 2) L)
    (hP : ∀ p r, Valued.v (P p r) ≤ 1) (b d : Fin n) :
    Valued.v ((cM L c * P * (cM L c).transpose) b d) ≤ 1 := by
  rw [cM_conj_apply]
  refine Valuation.map_sum_le _ fun p _ => Valuation.map_sum_le _ fun r _ => ?_
  split_ifs
  · exact hP p r
  · rw [map_zero]; exact zero_le

theorem blockM_int {n : ℕ} (a : ℕ) (h : 2 * (a + 2) ≤ n) (X Y : Matrix (Fin 2) (Fin 2) L)
    (hX : ∀ p r, Valued.v ((X - 1) p r) ≤ 1) (hY : ∀ p r, Valued.v ((Y - 1) p r) ≤ 1) :
    Formalism.UG.P.fIwasawaInt (blockM a h X Y) := by
  intro b d
  simp only [blockM, Matrix.add_apply]
  exact Valuation.map_add_le _ (Valuation.map_add_le _ (Formalism.UG.P.fIwasawa_int_one b d)
    (val_cM_conj_le_one _ _ hX b d)) (val_cM_conj_le_one _ _ hY b d)

theorem val_unip_sub_one_le {y : L} (hy : Valued.v y ≤ 1) (p r : Fin 2) :
    Valued.v (((!![1, y; 0, 1] : Matrix (Fin 2) (Fin 2) L) - 1) p r) ≤ 1 := by
  fin_cases p <;> fin_cases r <;> simp [hy]

theorem uR_mem_KU : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q n : ℕ)
    (hU : IsUnramInv ϖ σ q) (a : ℕ) (h : 2 * (a + 2) ≤ n) (x : L), Valued.v x ≤ 1 → uR σ hU.1 a h x ∈ KU σ n := by
  intro L _ _ ϖ σ q n hU a h x hx
  have hσv := hU.2.1
  have hI : Formalism.UG.P.fIwasawaInt (((uR σ hU.1 a h x : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) := by
    show Formalism.UG.P.fIwasawaInt (blockM a h (nU x : GL (Fin 2) L).val (partner σ (nU x)))
    rw [partner_nU]
    refine blockM_int a h _ _ (val_unip_sub_one_le hx) (val_unip_sub_one_le ?_)
    rw [Valuation.map_neg, hσv]
    exact hx
  have hK := Formalism.UG.P.fIwasawa_mk_mem_K σ hσv _ (Formalism.UG.P.fIwasawa_mem_un σ (uR σ hU.1 a h x)) hI
  have he : Formalism.UG.P.fIwasawaMk σ _ (Formalism.UG.P.fIwasawa_mem_un σ (uR σ hU.1 a h x)) = uR σ hU.1 a h x :=
    Subtype.ext (Units.ext (Formalism.UG.P.fIwasawa_mk_val σ _ _))
  rwa [he] at hK

end RootInt

end GlobalTheory.CompanionTheory.SwapRoot

end
