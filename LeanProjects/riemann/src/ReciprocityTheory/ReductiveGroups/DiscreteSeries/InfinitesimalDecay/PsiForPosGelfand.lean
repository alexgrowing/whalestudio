import ReciprocityTheory.ReductiveGroups.DiscreteSeries.InfinitesimalDecay.DecBoundJ
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.InfChar
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.Sandwich
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.PsiPos
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.PsiGelfand

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.DS.DecInf

variable {n : ℕ}

theorem opPow_congr {ε : Fin n → Bool} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (A : Fin n → Fin n → (Matrix (Fin n) (Fin n) ℂ → E) → (Matrix (Fin n) (Fin n) ℂ → E))
    (hA : ∀ a b (f f' : Matrix (Fin n) (Fin n) ℂ → E), (∀ g, inUJ ε g → f g = f' g) →
      ∀ g, inUJ ε g → A a b f g = A a b f' g) :
    ∀ (k : ℕ) (a b : Fin n) (f f' : Matrix (Fin n) (Fin n) ℂ → E), (∀ g, inUJ ε g → f g = f' g) →
      ∀ g, inUJ ε g → S7.opPow A k a b f g = S7.opPow A k a b f' g
  | 0, a, b, f, f', h, g, hg => by
      simp only [S7.opPow]
      split_ifs
      · exact h g hg
      · rfl
  | k + 1, a, b, f, f', h, g, hg => by
      simp only [S7.opPow, Finset.sum_apply]
      refine Finset.sum_congr rfl fun c _ => ?_
      exact hA a c _ _ (fun g' hg' => opPow_congr A hA k c b f f' h g' hg') g hg

theorem opGelfand_congr {ε : Fin n → Bool} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (A : Fin n → Fin n → (Matrix (Fin n) (Fin n) ℂ → E) → (Matrix (Fin n) (Fin n) ℂ → E))
    (hA : ∀ a b (f f' : Matrix (Fin n) (Fin n) ℂ → E), (∀ g, inUJ ε g → f g = f' g) →
      ∀ g, inUJ ε g → A a b f g = A a b f' g)
    (k : ℕ) {f f' : Matrix (Fin n) (Fin n) ℂ → E} (h : ∀ g, inUJ ε g → f g = f' g)
    {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) :
    S7.opGelfand A k f g = S7.opGelfand A k f' g := by
  simp only [S7.opGelfand, Finset.sum_apply]
  exact Finset.sum_congr rfl fun a _ => opPow_congr A hA k a a f f' h g hg

theorem rightE_congr {ε : Fin n → Bool} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] :
    ∀ a b (f f' : Matrix (Fin n) (Fin n) ℂ → E), (∀ g, inUJ ε g → f g = f' g) →
      ∀ g, inUJ ε g → S7.rightE ε a b f g = S7.rightE ε a b f' g :=
  fun a b _ _ h _ hg => icx_eabV_congr h a b hg

theorem rightEanti_congr {ε : Fin n → Bool} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] :
    ∀ a b (f f' : Matrix (Fin n) (Fin n) ℂ → E), (∀ g, inUJ ε g → f g = f' g) →
      ∀ g, inUJ ε g → S7.rightEanti ε a b f g = S7.rightEanti ε a b f' g := by
  intro a b f f' h g hg
  simp only [S7.rightEanti, Pi.neg_apply]
  rw [icx_eabV_congr h (Fin.rev b) (Fin.rev a) hg]

theorem psiFor_pos_gelfand {ε : Fin n → Bool} {lam : Fin n → ℝ} {T : S7.KType ε (lowK ε lam)}
    {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)} (hlam : S7.IsHCParam lam) {h : ℝ}
    (hgap : GapAtLeast ε lam h) (hth : thrStar ε < h) (hq : 1 ≤ S7.q0 ε) (hP : IsPsiFor ε lam T Ψ) :
    (∀ X, inP ε X → (Ψ (NormedSpace.exp X)).IsPositive) ∧
      ∀ (k : ℕ) (g : Matrix (Fin n) (Fin n) ℂ), inUJ ε g →
        S7.opGelfand (S7.rightE ε) k Ψ g = gval (icShift lam) k • Ψ g ∧
          S7.opGelfand (S7.rightEanti ε) k Ψ g = gval (icShift (-lam)) k • Ψ g := by
  obtain ⟨Ψ', h1, h2, h3, h4, -, h6, h7, h8⟩ := S7.psiAll (n := n) ε lam h T hlam hgap hq
  have hT1 : (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ) + 1 ≤ thrStar ε := le_max_left _ _
  have hT2 : 16 * (n : ℝ) * (S7.q0 ε : ℝ) + 8 * Real.sqrt (2 * (S7.q0 ε : ℝ)) ≤ thrStar ε :=
    le_max_right _ _
  have h8' : 8 * (n : ℝ) * S7.q0 ε < h := by
    have : 0 ≤ (n : ℝ) * (S7.q0 ε : ℝ) := by positivity
    have : 0 ≤ Real.sqrt (2 * (S7.q0 ε : ℝ)) := Real.sqrt_nonneg _
    nlinarith
  have hstd : StdGap ε lam := ⟨hlam.1, h, hgap, by linarith⟩
  have hP' : IsPsiFor ε lam T Ψ' := ⟨h1, h2, h3, h4, fun μ hμ => (h6 μ hμ).2.1 h8'⟩
  have heq : ∀ g ∈ UJset ε, Ψ' g = Ψ g := puniq_psi_eq hstd hP hP' (HW.KType.w_ne_zero T)
  have heq' : ∀ g, inUJ ε g → Ψ g = Ψ' g := fun g hg => (heq g hg).symm
  refine ⟨fun X hX => ?_, fun k g hg => ?_⟩
  · obtain ⟨μ, hμ⟩ := S7.exists_mu hlam
    have hX1 : inUJ ε (NormedSpace.exp X) := by
      have := S7.inUJ_kexp (1 : S7.KG ε) hX
      have hk1 : S7.toMK (1 : S7.KG ε) = 1 := rfl
      rwa [hk1, one_mul] at this
    rw [heq' _ hX1]
    exact psi_exp_isPositive T Ψ' μ hμ (h8 μ hμ) X hX
  · obtain ⟨e1, e2⟩ := h7 k g hg
    refine ⟨?_, ?_⟩
    · rw [opGelfand_congr _ rightE_congr k heq' hg, e1, heq' g hg]
    · rw [opGelfand_congr _ rightEanti_congr k heq' hg, e2, heq' g hg]

end ReciprocityTheory.ChartRestriction.DS.DecInf
