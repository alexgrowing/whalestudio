import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LowersMulZero
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalPointsCountableDiscreteSubgroupAdelic

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov

namespace GlobalTheory.AlgCutSubgroup

variable {n : ℕ} {ε : Fin n → Bool}

theorem sign_sq : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := by
  unfold Formalism.REAL.Jm
  rw [diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext i
  split_ifs <;> norm_num

theorem inv_sub_one (g : Formalism.REAL.UJ ε) :
    uMat g⁻¹ - 1 = Formalism.REAL.Jm ε * (uMat g - 1)ᴴ * Formalism.REAL.Jm ε := by
  have hJ : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := sign_sq
  have hg : (uMat g)ᴴ * Formalism.REAL.Jm ε * uMat g = Formalism.REAL.Jm ε := g.2
  have hMN : uMat g * uMat g⁻¹ = 1 := by
    unfold uMat
    simp
  have hN : uMat g⁻¹ = Formalism.REAL.Jm ε * (uMat g)ᴴ * Formalism.REAL.Jm ε := by
    calc uMat g⁻¹ = (Formalism.REAL.Jm ε * ((uMat g)ᴴ * Formalism.REAL.Jm ε * uMat g)) * uMat g⁻¹ := by
          rw [hg, hJ, Matrix.one_mul]
      _ = Formalism.REAL.Jm ε * (uMat g)ᴴ * Formalism.REAL.Jm ε * (uMat g * uMat g⁻¹) := by
          simp only [Matrix.mul_assoc]
      _ = Formalism.REAL.Jm ε * (uMat g)ᴴ * Formalism.REAL.Jm ε := by rw [hMN, Matrix.mul_one]
  rw [hN, conjTranspose_sub, conjTranspose_one, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hJ]

theorem exists_subgroup : ∀ (I : AutInst) (xf : I.Gf) (A : InfinitePlace I.F → Submodule ℂ (Matrix (Fin I.n) (Fin I.n) ℂ)), (∀ v, ∀ X ∈ A v, ∀ Y ∈ A v, X * Y ∈ A v) → (∀ v, ∀ X ∈ A v, Formalism.REAL.Jm (I.ε v) * Xᴴ * Formalism.REAL.Jm (I.ε v) ∈ A v) → ∃ Γ : Subgroup I.Ginf, (Γ : Set I.Ginf) = {g | g ∈ latGroup I xf ∧ ∀ v, uMat (g v) - 1 ∈ A v} := by
  intro I xf A h1 h2
  obtain ⟨Γ0, hΓ0⟩ := (GlobalTheory.RatDiscrete.subgroup_countable_discrete I).1
  have hKmul : ∀ a b : I.Gf, a ∈ I.Kset → b ∈ I.Kset → a * b ∈ I.Kset := fun a b ha hb =>
    (Formalism.UG.stabGL I.Lf).mul_mem ha hb
  have hKinv : ∀ a : I.Gf, a ∈ I.Kset → a⁻¹ ∈ I.Kset := fun a ha =>
    (Formalism.UG.stabGL I.Lf).inv_mem ha
  have hKone : (1 : I.Gf) ∈ I.Kset := (Formalism.UG.stabGL I.Lf).one_mem
  have hUmul : ∀ (v : InfinitePlace I.F) (g h : I.Ginf), uMat ((g * h) v) = uMat (g v) * uMat (h v) :=
    fun _ _ _ => rfl
  have hUinv : ∀ (v : InfinitePlace I.F) (g : I.Ginf), uMat (g⁻¹ v) = uMat (g v)⁻¹ := fun _ _ => rfl
  have hUone : ∀ v : InfinitePlace I.F, uMat ((1 : I.Ginf) v) = 1 := fun _ => rfl
  refine ⟨{ carrier := {g | g ∈ latGroup I xf ∧ ∀ v, uMat (g v) - 1 ∈ A v},
            mul_mem' := ?_, one_mem' := ?_, inv_mem' := ?_ }, rfl⟩
  · rintro g h ⟨hg, hgA⟩ ⟨hh, hhA⟩
    refine ⟨?_, fun v => ?_⟩
    · unfold latGroup at hg hh ⊢
      obtain ⟨γ, hγ, rfl, hk⟩ := hg
      obtain ⟨δ, hδ, rfl, hk'⟩ := hh
      refine ⟨γ * δ, ?_, rfl, ?_⟩
      · rw [← hΓ0] at hγ hδ ⊢
        exact Γ0.mul_mem hγ hδ
      · have e : xf⁻¹ * (γ * δ).2 * xf = (xf⁻¹ * γ.2 * xf) * (xf⁻¹ * δ.2 * xf) := by
          simp [mul_assoc]
        rw [e]
        exact hKmul _ _ hk hk'
    · have e : uMat ((g * h) v) - 1 =
          (uMat (g v) - 1) * (uMat (h v) - 1) + (uMat (g v) - 1) + (uMat (h v) - 1) := by
        rw [hUmul]
        noncomm_ring
      rw [e]
      exact add_mem (add_mem (h1 v _ (hgA v) _ (hhA v)) (hgA v)) (hhA v)
  · refine ⟨?_, fun v => ?_⟩
    · unfold latGroup
      refine ⟨1, ?_, rfl, ?_⟩
      · rw [← hΓ0]
        exact Γ0.one_mem
      · simpa using hKone
    · rw [hUone, sub_self]
      exact zero_mem _
  · rintro g ⟨hg, hgA⟩
    refine ⟨?_, fun v => ?_⟩
    · unfold latGroup at hg ⊢
      obtain ⟨γ, hγ, rfl, hk⟩ := hg
      refine ⟨γ⁻¹, ?_, rfl, ?_⟩
      · rw [← hΓ0] at hγ ⊢
        exact Γ0.inv_mem hγ
      · have e : xf⁻¹ * γ⁻¹.2 * xf = (xf⁻¹ * γ.2 * xf)⁻¹ := by
          simp [mul_assoc]
        rw [e]
        exact hKinv _ hk
    · rw [hUinv, inv_sub_one]
      exact h2 v _ (hgA v)

end GlobalTheory.AlgCutSubgroup
