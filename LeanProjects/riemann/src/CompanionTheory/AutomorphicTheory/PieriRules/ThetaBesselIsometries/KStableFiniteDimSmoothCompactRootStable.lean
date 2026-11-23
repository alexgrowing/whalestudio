import Mathlib
import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.Imports
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.RealPlaceAnalysis.StatementE
import Formalism.RealPlaceAnalysis.StatementKT
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.DerivedActionDiscreteSeriesProperties
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.DiscreteSeriesUnitarySmoothBasic
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.IsDSOfIsDG

namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.CompactStable

open PI.UpqRep

theorem deriv_mem {H : Type} [NormedAddCommGroup H] [NormedSpace ℂ H] (S : Submodule ℂ H) [FiniteDimensional ℂ S]
    {f : ℝ → H} {f' : H} (hf : HasDerivAt f f' 0) (hS : ∀ t, f t ∈ S) : f' ∈ S := by
  have h := hasDerivAt_iff_tendsto_slope.1 hf
  refine S.closed_of_finiteDimensional.mem_of_tendsto h (Filter.Eventually.of_forall fun t => ?_)
  rw [slope_def_module]
  exact S.smul_of_tower_mem _ (S.sub_mem (hS t) (hS 0))

variable {k r : ℕ}

theorem dsig_mem (R : Rep k r) (S : Submodule ℂ R.H) [FiniteDimensional ℂ S]
    (hS : ∀ g ∈ UH (Hpk k r) ∩ (Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ : Set _), ∀ x ∈ S, R.σ g x ∈ S)
    {X : Mx k r} (hX : Xᴴ = -X) (hc : Hpk k r * X = X * Hpk k r) {v : R.H} (hv : v ∈ S) (hsm : v ∈ R.sm) :
    dsig (k := k) (r := r) R.σ X v ∈ S := by
  have hL : InLieHpk k r X := by
    show Xᴴ * Hpk k r + Hpk k r * X = 0
    rw [hX, hc]; simp
  refine deriv_mem S (GlobalTheory.DerivedAction.hasDerivAt_dsig hL hsm) fun t => hS _ ⟨GlobalTheory.DerivedAction.exp_mem hL t, ?_⟩ v hv
  have h := CCRuleCW.exp_mem_UH 1 ((t : ℂ) • X) (by
    rw [Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, hX]; simp)
  have h' : (NormedSpace.exp ((t : ℂ) • X))ᴴ * 1 * NormedSpace.exp ((t : ℂ) • X) = 1 := h
  rw [Matrix.mul_one] at h'
  exact Matrix.mem_unitaryGroup_iff'.2 h'

theorem dC_mem (R : Rep k r) (S : Submodule ℂ R.H) [FiniteDimensional ℂ S]
    (hS : ∀ g ∈ UH (Hpk k r) ∩ (Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ : Set _), ∀ x ∈ S, R.σ g x ∈ S)
    (h1 : (Hpk k r)ᴴ = Hpk k r) (h2 : Hpk k r * Hpk k r = 1)
    {Y : Mx k r} (hc : Hpk k r * Y = Y * Hpk k r) {v : R.H} (hv : v ∈ S) (hsm : v ∈ R.sm) :
    R.dC Y v ∈ S := by
  have hc' : Hpk k r * Yᴴ = Yᴴ * Hpk k r := by
    have := congrArg Matrix.conjTranspose hc
    rw [conjTranspose_mul, conjTranspose_mul, h1] at this
    exact this.symm
  have e : Formalism.QuantumDeterminants.Hpk k r * Yᴴ * Formalism.QuantumDeterminants.Hpk k r = Yᴴ := by
    show Hpk k r * Yᴴ * Hpk k r = Yᴴ
    rw [hc', Matrix.mul_assoc, h2, Matrix.mul_one]
  unfold Rep.dC
  rw [e]
  refine S.add_mem (dsig_mem R S hS ?_ ?_ hv hsm) (S.smul_mem _ (dsig_mem R S hS ?_ ?_ hv hsm))
  · rw [conjTranspose_smul, conjTranspose_add, conjTranspose_neg, conjTranspose_conjTranspose, ← smul_neg]
    congr 1
    · simp
    · abel
  · rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_neg, Matrix.neg_mul, hc, hc']
  · rw [conjTranspose_smul, conjTranspose_sub, conjTranspose_neg, conjTranspose_conjTranspose, ← neg_smul]
    congr 1
    · simp
    · abel
  · rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_neg, Matrix.neg_mul, hc, hc']

theorem Jm_single {n : ℕ} (ε : Fin n → Bool) {a b : Fin n} (h : ε a = ε b) :
    Jm ε * Matrix.single a b (1 : ℂ) = Matrix.single a b 1 * Jm ε := by
  ext i j
  unfold Jm
  rw [diagonal_mul, mul_diagonal]
  by_cases hij : a = i ∧ b = j
  · obtain ⟨rfl, rfl⟩ := hij
    simp [h]
  · simp [Matrix.single, hij]

theorem kStable_smooth_and_stable : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), R.IsDG ε mu → ∀ (Q : Mx k r), PI.UpqRep.IsCayleyU k r ε Q → ∀ S : Submodule ℂ R.H, FiniteDimensional ℂ S → PI.UpqRep.IsKStableOn ε (fun g => R.σ (Q⁻¹ * g * Q)) S → (∀ v ∈ S, R.KFin v ∧ v ∈ R.sm) ∧ ∀ a b, ε a = ε b → ∀ v ∈ S, R.dC (Q⁻¹ * Matrix.single a b 1 * Q) v ∈ S := by
  intro hK k r ε mu R hR Q hQ S hfd hst
  have hS : ∀ g ∈ UH (Hpk k r) ∩ (Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ : Set _), ∀ x ∈ S, R.σ g x ∈ S := by
    intro g hg x hx
    obtain ⟨hk, hback⟩ := PI.UnitaryGroupMassFormula.LowSmooth.conj_mem_Kset hQ hg
    have h := hst _ hk x hx
    simp only [hback] at h
    exact h
  have hA : ∀ v ∈ S, R.KFin v ∧ v ∈ R.sm := fun v hv =>
    ⟨⟨S, hfd, hv, hS⟩, hK k r ε mu R.H R.σ hR.1 hR.2 v ⟨S, hfd, hv, hS⟩⟩
  refine ⟨hA, fun a b hab v hv => ?_⟩
  have hsP : Qᴴ * Q = 1 := Matrix.mem_unitaryGroup_iff'.mp hQ.2
  have hPs : Q * Qᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hQ.2
  have hinv : Q⁻¹ = Qᴴ := Matrix.inv_eq_left_inv hsP
  have hH : Qᴴ * Jm ε * Q = Hpk k r := hQ.1.2
  have hJ1 : (Jm ε)ᴴ = Jm ε := by
    unfold Jm
    rw [diagonal_conjTranspose]
    congr 1
    funext c
    by_cases hc : ε c = true <;> simp [hc]
  have hJ2 : Jm ε * Jm ε = 1 := by
    unfold Jm
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext c
    by_cases hc : ε c = true <;> simp [hc]
  have hm : ∀ A B : Mx k r, Qᴴ * A * Q * (Qᴴ * B * Q) = Qᴴ * (A * B) * Q := by
    intro A B
    calc Qᴴ * A * Q * (Qᴴ * B * Q) = Qᴴ * A * (Q * Qᴴ) * B * Q := by simp only [Matrix.mul_assoc]
      _ = Qᴴ * (A * B) * Q := by rw [hPs, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  refine dC_mem R S hS ?_ ?_ ?_ hv (hA v hv).2
  · rw [← hH, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hJ1, Matrix.mul_assoc]
  · rw [← hH, hm, hJ2, Matrix.mul_one, hsP]
  · rw [← hH, hinv, hm, hm, Jm_single ε hab]

end GlobalTheory.CompactStable
