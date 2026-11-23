import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsTateZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryInvariantHermitianFormSymmEqSmulTrace
open CategoryTheory AlgebraicGeometry Set Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.ArInt GlobalTheory.TorsionForm GlobalTheory.ThetaRR
open GlobalTheory.LB (toMod)
open GlobalTheory.LieVB (omega)
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe (Fl Pt stdLat symMat tauU siegel symPart ChernIsFlat IsMetric InducesPolarisation cov)
open ReciprocityTheory.L2DbarEstimates (V)
open Filter Topology
open scoped ContDiff

noncomputable section

namespace GlobalTheory.SchurUnitary

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra in

theorem fderiv_frac {n : Type} [Fintype n] [DecidableEq n] {E F : Type}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (T : E →ₗ[ℂ] Matrix n n ℂ) (S : Matrix n n ℂ →ₗ[ℂ] F) (a b c d R : Matrix n n ℂ) (x : E)
    (hR : (c * T x + d) * R = 1) (v : E) :
    fderiv ℂ (fun s => S ((a * T s + b) * (c * T s + d)⁻¹)) x v =
      S (a * T v * R - (a * T x + b) * (R * (c * T v) * R)) := by
  have hR' : R * (c * T x + d) = 1 := mul_eq_one_comm.1 hR
  let u : (Matrix n n ℂ)ˣ := ⟨c * T x + d, R, hR, hR'⟩
  have hT : HasFDerivAt (fun s => T s) (LinearMap.toContinuousLinearMap T) x :=
    (LinearMap.toContinuousLinearMap T).hasFDerivAt
  have hN := (hT.const_mul a).add_const b
  have hD := (hT.const_mul c).add_const d
  have hI := (hasFDerivAt_ringInverse (𝕜 := ℂ) u).comp x (f := fun s => c * T s + d) hD
  have hP := hN.mul' hI
  have hS := (LinearMap.toContinuousLinearMap S).hasFDerivAt.comp x hP
  have e : (fun s => S ((a * T s + b) * (c * T s + d)⁻¹)) =
      (LinearMap.toContinuousLinearMap S) ∘ ((fun s => a * T s + b) *
        (Ring.inverse ∘ fun s => c * T s + d)) := by
    funext s
    simp [Matrix.nonsing_inv_eq_ringInverse]
  rw [e, hS.fderiv]
  have hi : Ring.inverse (c * T x + d) = R := Ring.inverse_unit u
  change S ((a * T x + b) * (-(R * (c * T v) * R)) + a * T v * Ring.inverse (c * T x + d)) = _
  rw [hi, Matrix.mul_neg, neg_add_eq_sub]

variable {g : ℕ}

def tauL (g : ℕ) : symMat g →ₗ[ℂ] Matrix (Fin g) (Fin g) ℂ where
  toFun := tauU
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def symL (g : ℕ) : Matrix (Fin g) (Fin g) ℂ →ₗ[ℂ] symMat g where
  toFun := symPart
  map_add' A B := by
    apply Subtype.ext; funext i j; simp [symPart]; ring
  map_smul' c A := by
    apply Subtype.ext; funext i j; simp [symPart]; ring

theorem tauU_I : tauU (symPart (Complex.I • (1 : Matrix (Fin g) (Fin g) ℂ))) = Complex.I • 1 := by
  ext i j
  by_cases h : i = j
  · subst h; simp [tauU, symPart]
  · simp [tauU, symPart, Matrix.one_apply, h, Ne.symm h]

theorem mem_sp (k : Matrix.unitaryGroup (Fin g) ℂ) :
    fromBlocks (k.1.map Complex.re) (k.1.map Complex.im) (-(k.1.map Complex.im))
      (k.1.map Complex.re) ∈ symplecticGroup (Fin g) ℝ := by
  have hk : k.1 * star k.1 = 1 := k.2.2
  set a := k.1.map Complex.re
  set b := k.1.map Complex.im
  have h1 : a * aᵀ + b * bᵀ = 1 := by
    ext i j
    have := congrArg Complex.re (congrFun (congrFun hk i) j)
    simp only [Matrix.mul_apply, Complex.re_sum, Matrix.one_apply] at this
    simp only [a, b, Matrix.add_apply, Matrix.mul_apply, Matrix.one_apply, ← Finset.sum_add_distrib]
    split_ifs at this ⊢ <;> simpa using this
  have h2 : b * aᵀ = a * bᵀ := by
    ext i j
    have := congrArg Complex.im (congrFun (congrFun hk i) j)
    simp only [Matrix.mul_apply, Complex.im_sum, Matrix.one_apply] at this
    rw [← sub_eq_zero]
    simp only [a, b, Matrix.mul_apply, ← Finset.sum_sub_distrib]
    have h0 : (if i = j then (1 : ℂ) else 0).im = 0 := by split_ifs <;> simp
    rw [h0] at this
    rw [← this]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp; ring
  rw [SymplecticGroup.mem_iff, Matrix.J, fromBlocks_transpose, fromBlocks_multiply,
    fromBlocks_multiply]
  congr 1
  · simp [h2]
  · simp only [Matrix.mul_zero, Matrix.mul_one, Matrix.mul_neg, zero_add, add_zero, transpose_neg,
      Matrix.neg_mul]
    rw [← h1]; abel
  · simp only [Matrix.mul_zero, Matrix.mul_one, Matrix.mul_neg, zero_add, add_zero, transpose_neg,
      Matrix.neg_mul, neg_neg]
    exact h1
  · simp [h2]

theorem main : ∀ (g : ℕ) (k : Matrix.unitaryGroup (Fin g) ℂ), ∃ γ : GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe.Sp g, actB γ (symPart (Complex.I • (1 : Matrix (Fin g) (Fin g) ℂ))) = symPart (Complex.I • 1) ∧ ∀ v : symMat g, fderiv ℂ (actB γ) (symPart (Complex.I • (1 : Matrix (Fin g) (Fin g) ℂ))) v = symPart (k.1 * tauU v * k.1ᵀ) := by
  intro g k
  have hk : k.1 * star k.1 = 1 := k.2.2
  let a : Matrix (Fin g) (Fin g) ℂ := (k.1.map Complex.re).map fun t : ℝ => (t : ℂ)
  let b : Matrix (Fin g) (Fin g) ℂ := (k.1.map Complex.im).map fun t : ℝ => (t : ℂ)
  let γ : GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe.Sp g := ⟨_, mem_sp k⟩
  have hact : actB γ = fun s => symL g ((a * tauL g s + b) * ((-b) * tauL g s + a)⁻¹) := by
    funext s
    have : (-(k.1.map Complex.im)).map (fun t : ℝ => (t : ℂ)) = -b := by
      ext i j; simp [b]
    rw [← this]
    rfl
  have hx : tauL g (symPart (Complex.I • (1 : Matrix (Fin g) (Fin g) ℂ))) = Complex.I • 1 := tauU_I
  have hD : -b * (Complex.I • (1 : Matrix (Fin g) (Fin g) ℂ)) + a = (star k.1)ᵀ := by
    ext i j
    simp only [Matrix.mul_smul, Matrix.mul_one]
    apply Complex.ext <;> simp [a, b]
  have hN : a * (Complex.I • (1 : Matrix (Fin g) (Fin g) ℂ)) + b = Complex.I • (star k.1)ᵀ := by
    ext i j
    simp only [Matrix.mul_smul, Matrix.mul_one]
    apply Complex.ext <;> simp [a, b]
  have hab : a + Complex.I • b = k.1 := by
    ext i j
    apply Complex.ext <;> simp [a, b]
  have hR : (star k.1)ᵀ * k.1ᵀ = 1 := by rw [← transpose_mul, hk, transpose_one]
  refine ⟨γ, ?_, fun v => ?_⟩
  · rw [hact]
    simp only [hx, hD, hN]
    rw [Matrix.inv_eq_right_inv hR, Matrix.smul_mul, hR]
    rfl
  · rw [hact, fderiv_frac (tauL g) (symL g) a b (-b) a k.1ᵀ _ (by rw [hx, hD, hR]) v, hx, hN]
    change symPart _ = symPart (k.1 * tauL g v * k.1ᵀ)
    congr 1
    rw [Matrix.smul_mul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hR, Matrix.one_mul]
    generalize k.1ᵀ = R
    rw [← hab]
    simp [Matrix.add_mul]

end GlobalTheory.SchurUnitary
