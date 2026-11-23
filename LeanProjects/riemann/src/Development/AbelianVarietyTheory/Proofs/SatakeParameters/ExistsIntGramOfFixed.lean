import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemIntMat
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeisenbergTranslateFixedIntegralUnitaryStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CayleyTransformTrivialPhaseSkewHermitianStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIntegralGramOfPhaseConditionsStatement

noncomputable section
namespace GlobalTheory.Hk3.HoweDuality

theorem exists_int_gram_of_fixed : ∀ (L : Type) [Field L] [CharZero L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q : ℕ) (δ : L)
    (n n' : ℕ) (JS : GL (Fin n) L) (JT : GL (Fin n') L) (ψ : AddChar L ℂ) (M : Type) [AddCommGroup M] [Module ℂ M]
    (ρ : Matrix (Fin n') (Fin n) L → Module.End ℂ M)
    (ω : Formalism.UG.UJ σ (JS : Matrix (Fin n) (Fin n) L) × Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L) →* Module.End ℂ M), GlobalTheory.Hk3.LocPair ϖ σ q δ JS JT ψ ρ ω → ∀ s : M, s ≠ 0 → GlobalTheory.Hk3.LocVac ρ s →
    Submodule.span ℂ (Set.range fun x => ρ x s) = ⊤ → ∀ x : Matrix (Fin n') (Fin n) L,
    (∃ w : M, w ≠ 0 ∧ (∀ h : Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L),
        (h : GL (Fin n') L) ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) → ω (1, h) w = w) ∧
      w ∈ Submodule.span ℂ {v : M | ∃ h : Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L), (h : GL (Fin n') L) ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) ∧
          v = ρ (((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * x) s}) →
    ∃ l ∈ GlobalTheory.Hk3.HoweDuality.intMat L n' n,
      ∀ i j, ((x - l) * ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * Matrix.transpose ((x - l).map σ)) i j ∈ Formalism.UG.intL L := by
  intro L _ _ _ _ ϖ σ q δ n n' JS JT ψ M _ _ ρ ω hP s hs0 hs hspan x hw
  obtain ⟨hne, hfx⟩ := GlobalTheory.T.heisenbergTranslate_fixed_integralUnitary L ϖ σ q δ n n' JS JT ψ M ρ ω hP s hs x hw
  have Hph : ∀ h : Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L), (h : GL (Fin n') L) ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) →
      (∀ i j, (((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * x - x) i j ∈ Formalism.UG.intL L) →
      ψ ((GlobalTheory.Hk3.locH σ δ JS JT x (((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * x - x) + σ (GlobalTheory.Hk3.locH σ δ JS JT x (((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * x - x))) / 2) = 1 := by
    intro h hh hint
    have e := congrArg (fun T : Module.End ℂ M => T s) (hP.rho_mul x (((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * x - x))
    simp only [Module.End.mul_apply, LinearMap.smul_apply, hs _ hint, add_sub_cancel, hfx h hh hint] at e
    have e2 : (ψ ((GlobalTheory.Hk3.locH σ δ JS JT x (((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * x - x) + σ (GlobalTheory.Hk3.locH σ δ JS JT x (((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * x - x))) / 2) - 1) • ρ x s = 0 := by
      rw [sub_smul, one_smul, ← e, sub_self]
    rcases smul_eq_zero.1 e2 with h1 | h1
    · exact sub_eq_zero.1 h1
    · exact absurd h1 hne
  exact GlobalTheory.T.exists_integral_gram_of_phase_conditions L ϖ σ q δ n n' JS ψ hP.unr hP.odd hP.intS hP.hermS hP.delta hP.psi_int hP.psi_ne x
    (GlobalTheory.T.cayleyTransform_trivial_phase_skewHermitian L ϖ σ q δ n n' JS JT ψ hP.unr hP.odd hP.intS hP.intT hP.hermS hP.hermT hP.delta hP.psi_int x Hph)
end GlobalTheory.Hk3.HoweDuality
end
