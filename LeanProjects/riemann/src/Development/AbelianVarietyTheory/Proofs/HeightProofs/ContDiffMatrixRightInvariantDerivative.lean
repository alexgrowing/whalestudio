import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.FinitePartTypes
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqExistsIffDsExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqUniqueOfClassification
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasTypeAllAddOfEquiv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OneAddHsConjLe
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnAtTau
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoefBoundOfCasselmanWallach
import Development.AbelianVarietyTheory.Proofs.HeightProofs.FiniteDimensionalPolyV
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.KFourier

open Matrix

variable {n : ℕ}

open scoped Matrix.Norms.Operator in
theorem hasDerivAt_exp_entry_real (X : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    HasDerivAt (fun t : ℝ => (NormedSpace.exp ((t : ℂ) • X)) i j) (X i j) 0 := by
  have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) X (0 : ℝ)
  simp only [zero_smul, NormedSpace.exp_zero, one_mul] at h
  let L : Matrix (Fin n) (Fin n) ℂ →L[ℝ] ℂ :=
    LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℂ i j)
  have h2 : HasDerivAt (fun t : ℝ => (NormedSpace.exp (t • X)) i j) (X i j) 0 :=
    L.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h
  have e : (fun t : ℝ => (NormedSpace.exp ((t : ℂ) • X)) i j) = fun t : ℝ => (NormedSpace.exp (t • X)) i j := by
    funext t; rw [Complex.coe_smul]
  rw [e]; exact h2

theorem coord_mul_expK_zero {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X)
    (c : Fin n × Fin n × Bool) (k : KG ε) : coord ε c (k * expK ε X 0) = coord ε c k := by
  simp [coord, toMK_mul, toMK_expK hX, NormedSpace.exp_zero]

theorem mono_mul_expK_zero {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X)
    (s : List (Fin n × Fin n × Bool)) (k : KG ε) : mono ε s (k * expK ε X 0) = mono ε s k := by
  simp only [mono, coord_mul_expK_zero hX]

theorem hasDerivAt_coord {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X)
    (c : Fin n × Fin n × Bool) : ∃ ψ ∈ polyV ε 1, ∀ k : KG ε,
      HasDerivAt (fun t : ℝ => coord ε c (k * expK ε X t)) (ψ k) 0 := by
  obtain ⟨a, b, f⟩ := c
  have hent : ∀ k : KG ε, HasDerivAt (fun t : ℝ => (toMK (k * expK ε X t)) a b)
      (∑ l, toMK k a l * X l b) 0 := by
    intro k
    have e : (fun t : ℝ => (toMK (k * expK ε X t)) a b) =
        fun t : ℝ => ∑ l, toMK k a l * (NormedSpace.exp ((t : ℂ) • X)) l b := by
      funext t; simp only [toMK_mul, toMK_expK hX, Matrix.mul_apply]
    rw [e]
    exact HasDerivAt.fun_sum fun l _ => (hasDerivAt_exp_entry_real X l b).const_mul _
  cases f
  · refine ⟨∑ l, star (X l b) • coord ε (a, l, false), ?_, fun k => ?_⟩
    · exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (coord_mem ε _)
    · have h := (hent k).star
      have e1 : (fun t : ℝ => coord ε (a, b, false) (k * expK ε X t)) =
          fun t => star ((toMK (k * expK ε X t)) a b) := by
        funext t; simp [coord]
      rw [e1]
      have hv : (∑ l, star (X l b) • coord ε (a, l, false)) k = star (∑ l, toMK k a l * X l b) := by
        rw [Finset.sum_apply, star_sum]
        refine Finset.sum_congr rfl fun l _ => ?_
        simp only [Pi.smul_apply, smul_eq_mul, coord, Bool.false_eq_true, if_false, star_mul']
        exact mul_comm _ _
      rw [hv]; exact h
  · refine ⟨∑ l, X l b • coord ε (a, l, true), ?_, fun k => ?_⟩
    · exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (coord_mem ε _)
    · have e1 : (fun t : ℝ => coord ε (a, b, true) (k * expK ε X t)) =
          fun t => (toMK (k * expK ε X t)) a b := by
        funext t; simp [coord]
      rw [e1]
      have hv : (∑ l, X l b • coord ε (a, l, true)) k = ∑ l, toMK k a l * X l b := by
        rw [Finset.sum_apply]
        refine Finset.sum_congr rfl fun l _ => ?_
        simp only [Pi.smul_apply, smul_eq_mul, coord, if_true]
        exact mul_comm _ _
      rw [hv]; exact hent k

theorem hasDerivAt_mono {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X)
    (s : List (Fin n × Fin n × Bool)) : ∀ d, s.length ≤ d → ∃ ψ ∈ polyV ε d, ∀ k : KG ε,
      HasDerivAt (fun t : ℝ => mono ε s (k * expK ε X t)) (ψ k) 0 := by
  induction s with
  | nil =>
    intro d _
    refine ⟨0, Submodule.zero_mem _, fun k => ?_⟩
    simpa [mono] using hasDerivAt_const (0 : ℝ) (1 : ℂ)
  | cons c s ih =>
    intro d hd
    simp only [List.length_cons] at hd
    obtain ⟨ψc, hψc, hc⟩ := hasDerivAt_coord hX c
    obtain ⟨ψs, hψs, hs⟩ := ih (d - 1) (by omega)
    refine ⟨ψc * mono ε s + coord ε c * ψs, ?_, fun k => ?_⟩
    · have hle : 1 + (d - 1) ≤ d := by omega
      exact add_mem (polyV_mono ε hle (mul_mem hψc (mono_mem (by omega))))
        (polyV_mono ε hle (mul_mem (coord_mem ε c) hψs))
    · have h := (hc k).mul (hs k)
      have e : (fun t : ℝ => mono ε (c :: s) (k * expK ε X t)) =
          fun t => coord ε c (k * expK ε X t) * mono ε s (k * expK ε X t) := by
        funext t; simp [mono]
      rw [e]
      rw [coord_mul_expK_zero hX, mono_mul_expK_zero hX] at h
      exact h

theorem hasDerivAt_of_mem {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X) {d : ℕ}
    {φ : KG ε → ℂ} (hφ : φ ∈ polyV ε d) : ∃ ψ ∈ polyV ε d, ∀ k : KG ε,
      HasDerivAt (fun t : ℝ => φ (k * expK ε X t)) (ψ k) 0 := by
  induction hφ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨s, hs, rfl⟩ := hx
    exact hasDerivAt_mono hX s d hs
  | zero =>
    exact ⟨0, Submodule.zero_mem _, fun k => by simpa using hasDerivAt_const (0 : ℝ) (0 : ℂ)⟩
  | add x y _ _ hx hy =>
    obtain ⟨ψ₁, h₁, d₁⟩ := hx
    obtain ⟨ψ₂, h₂, d₂⟩ := hy
    exact ⟨ψ₁ + ψ₂, add_mem h₁ h₂, fun k => (d₁ k).add (d₂ k)⟩
  | smul a x _ hx =>
    obtain ⟨ψ, h, dψ⟩ := hx
    exact ⟨a • ψ, Submodule.smul_mem _ a h, fun k => by simpa using (dψ k).const_mul a⟩

theorem rder_mem_and_hasDerivAt (ε : Fin n → Bool) (d : ℕ) (φ : KG ε → ℂ) (hφ : φ ∈ polyV ε d)
    (X : Mx n) (hX : inK ε X) : rder ε [X] φ ∈ polyV ε d ∧
      ∀ k : KG ε, HasDerivAt (fun t : ℝ => φ (k * expK ε X t)) (rder ε [X] φ k) 0 := by
  obtain ⟨ψ, hψ, hd⟩ := hasDerivAt_of_mem hX hφ
  have e : rder ε [X] φ = ψ := by
    funext k
    rw [rder_cons, rder_nil]
    exact (hd k).deriv
  rw [e]
  exact ⟨hψ, hd⟩

end GlobalTheory.KFourier

end
