import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothReal
open NumberField IsDedekindDomain Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolRead
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

open scoped Matrix.Norms.Operator in

theorem commute_of_countable_commutators_exp {n : ℕ} (X a : Matrix (Fin n) (Fin n) ℂ)
    (S : Set (Matrix (Fin n) (Fin n) ℂ)) (ha : IsUnit a.det) (hS : S.Countable)
    (h : ∀ t : ℝ, NormedSpace.exp (t • X) * a * NormedSpace.exp (-(t • X)) * a⁻¹ ∈ S) :
    X * a = a * X := by
  have hd : ∀ t : ℝ, HasDerivAt (fun u : ℝ => NormedSpace.exp (u • X))
      (NormedSpace.exp (t • X) * X) t := fun t => hasDerivAt_exp_smul_const X t
  have hc : Continuous (fun u : ℝ => NormedSpace.exp (u • X)) :=
    continuous_iff_continuousAt.2 fun t => (hd t).continuousAt
  have hc' : Continuous (fun u : ℝ => NormedSpace.exp (-(u • X))) := by
    have := hc.comp continuous_neg
    refine this.congr fun u => ?_
    simp [Function.comp, neg_smul]
  set f : ℝ → Matrix (Fin n) (Fin n) ℂ :=
    fun t => NormedSpace.exp (t • X) * a * NormedSpace.exp (-(t • X)) * a⁻¹ with hf
  have hfc : Continuous f := ((hc.mul continuous_const).mul hc').mul continuous_const
  have hcount : (Set.range f).Countable := hS.mono (by rintro _ ⟨t, rfl⟩; exact h t)
  have hsub : (Set.range f).Subsingleton :=
    hcount.isTotallyDisconnected _ subset_rfl (isPreconnected_range hfc)
  have hone : ∀ t, f t = 1 := by
    intro t
    rw [hsub ⟨t, rfl⟩ ⟨0, rfl⟩]
    simp [hf, Matrix.mul_nonsing_inv a ha]
  have hcomm : ∀ t : ℝ, NormedSpace.exp (t • X) * a = a * NormedSpace.exp (t • X) := by
    intro t
    have h1 := hone t
    have h2 : NormedSpace.exp (-(t • X)) * NormedSpace.exp (t • X) = 1 := by
      rw [← Matrix.exp_add_of_commute _ _ (Commute.refl (t • X)).neg_left]
      simp
    have h3 : f t * a * NormedSpace.exp (t • X) = NormedSpace.exp (t • X) * a := by
      simp only [hf]
      rw [Matrix.mul_assoc _ a⁻¹ a, Matrix.nonsing_inv_mul a ha, Matrix.mul_one,
        Matrix.mul_assoc _ (NormedSpace.exp (-(t • X))), h2, Matrix.mul_one]
    rw [← h3, h1, Matrix.one_mul]
  have e1 := (hd 0).mul_const a
  have e2 := (hd 0).const_mul a
  simp only [hcomm] at e1
  have := e1.unique e2
  simpa using this

theorem central_of_countable_commutators_unitary :
    ∀ (n : ℕ) (J a : Matrix (Fin n) (Fin n) ℂ) (S : Set (Matrix (Fin n) (Fin n) ℂ)), Jᴴ = J → IsUnit J.det → IsUnit a.det → S.Countable → (∀ X ∈ {X : Matrix (Fin n) (Fin n) ℂ | Xᴴ * J + J * X = 0}, ∀ t : ℝ, NormedSpace.exp (t • X) * a * NormedSpace.exp (-(t • X)) * a⁻¹ ∈ S) → ∀ u, u * a = a * u := by
  intro n J a S hJ hJu ha hS h u
  have key : ∀ X : Matrix (Fin n) (Fin n) ℂ, Xᴴ * J + J * X = 0 → X * a = a * X :=
    fun X hX => commute_of_countable_commutators_exp X a S ha hS (h X hX)
  set v : Matrix (Fin n) (Fin n) ℂ := J⁻¹ * uᴴ * J with hv
  have hJv : J * v = uᴴ * J := by
    rw [hv, Matrix.mul_assoc, ← Matrix.mul_assoc J, Matrix.mul_nonsing_inv J hJu, Matrix.one_mul]
  have hvJ : vᴴ * J = J * u := by
    have := congrArg Matrix.conjTranspose hJv
    simpa [Matrix.conjTranspose_mul, hJ] using this
  have h1 := key (u - v) (by
    rw [Matrix.conjTranspose_sub, Matrix.sub_mul, Matrix.mul_sub, hJv, hvJ]; abel)
  have h2 := key (Complex.I • (u + v)) (by
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.add_mul, Matrix.mul_add, hJv, hvJ, add_comm (J * u), ← add_smul]
    simp)
  rw [Matrix.smul_mul, Matrix.mul_smul] at h2
  have h3 : (u + v) * a = a * (u + v) := smul_right_injective _ Complex.I_ne_zero h2
  have h4 : (2 : ℂ) • (u * a) = (2 : ℂ) • (a * u) := by
    rw [Matrix.sub_mul, Matrix.mul_sub] at h1
    rw [Matrix.add_mul, Matrix.mul_add] at h3
    rw [two_smul, two_smul]
    calc u * a + u * a = (u * a - v * a) + (u * a + v * a) := by abel
      _ = (a * u - a * v) + (a * u + a * v) := by rw [h1, h3]
      _ = a * u + a * u := by abel
  exact smul_right_injective _ two_ne_zero h4

end GlobalTheory
