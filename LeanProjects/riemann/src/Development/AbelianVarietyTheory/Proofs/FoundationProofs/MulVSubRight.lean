import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators Matrix

noncomputable section

namespace GlobalTheory.RatEqui

variable (D : D7) {N N' : ℕ}

theorem embT_conj (τ : D.what₂.Tau) (x : D.host.E) :
    embT D τ (D.host.conj x) = (starRingEnd ℂ) (embT D τ x) :=
  Formalism.HC.HostAx.conjE_apply D.host.toHostAx _ _

def adj {n : ℕ} (M : Matrix (Fin n) (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E :=
  (M.map D.host.conj).transpose

theorem adj_map {n : ℕ} (M : Matrix (Fin n) (Fin n) D.host.E) (τ : D.what₂.Tau) :
    (adj D M).map (embT D τ) = (M.map (embT D τ))ᴴ := by
  ext i j
  simp [adj, embT_conj]

def mulV (M' : Matrix (Fin N') (Fin N') D.host.E) (M : Matrix (Fin N) (Fin N) D.host.E) :
    VC D N N' →ₗ[ℂ] VC D N N' where
  toFun z := fun τ => (M'.map (embT D τ) * Matrix.of (z τ) * M.map (embT D τ) : Matrix _ _ ℂ)
  map_add' z w := by
    funext τ
    change M'.map (embT D τ) * (Matrix.of (z τ) + Matrix.of (w τ)) * M.map (embT D τ) = _
    rw [Matrix.mul_add, Matrix.add_mul]; rfl
  map_smul' c z := by
    funext τ
    change M'.map (embT D τ) * (c • Matrix.of (z τ)) * M.map (embT D τ) = _
    rw [Matrix.mul_smul, Matrix.smul_mul]; rfl

theorem mulV_apply (M' : Matrix (Fin N') (Fin N') D.host.E) (M : Matrix (Fin N) (Fin N) D.host.E)
    (z : VC D N N') (τ : D.what₂.Tau) :
    mulV D M' M z τ = (M'.map (embT D τ) * Matrix.of (z τ) * M.map (embT D τ) : Matrix _ _ ℂ) := rfl

theorem mulV_mulV (M₁' M₂' : Matrix (Fin N') (Fin N') D.host.E) (M₁ M₂ : Matrix (Fin N) (Fin N) D.host.E)
    (z : VC D N N') : mulV D M₁' M₁ (mulV D M₂' M₂ z) = mulV D (M₁' * M₂') (M₂ * M₁) z := by
  funext τ
  change M₁'.map (embT D τ) * (M₂'.map (embT D τ) * Matrix.of (z τ) * M₂.map (embT D τ)) * M₁.map (embT D τ) =
    (M₁' * M₂').map (embT D τ) * Matrix.of (z τ) * (M₂ * M₁).map (embT D τ)
  simp only [Matrix.map_mul, Matrix.mul_assoc]

theorem mulV_one (z : VC D N N') : mulV D 1 1 z = z := by
  funext τ
  rw [mulV_apply, Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_one _ (map_zero _) (map_one _),
    Matrix.one_mul, Matrix.mul_one]
  rfl

theorem mulV_sub_left (M₁' M₂' : Matrix (Fin N') (Fin N') D.host.E) (M : Matrix (Fin N) (Fin N) D.host.E)
    (z : VC D N N') : mulV D (M₁' - M₂') M z = mulV D M₁' M z - mulV D M₂' M z := by
  funext τ
  change (M₁' - M₂').map (embT D τ) * Matrix.of (z τ) * M.map (embT D τ) =
    M₁'.map (embT D τ) * Matrix.of (z τ) * M.map (embT D τ) - M₂'.map (embT D τ) * Matrix.of (z τ) * M.map (embT D τ)
  rw [Matrix.map_sub _ (map_sub _), Matrix.sub_mul, Matrix.sub_mul]

theorem mulV_sub_right (M' : Matrix (Fin N') (Fin N') D.host.E) (M₁ M₂ : Matrix (Fin N) (Fin N) D.host.E)
    (z : VC D N N') : mulV D M' (M₁ - M₂) z = mulV D M' M₁ z - mulV D M' M₂ z := by
  funext τ
  change M'.map (embT D τ) * Matrix.of (z τ) * (M₁ - M₂).map (embT D τ) =
    M'.map (embT D τ) * Matrix.of (z τ) * M₁.map (embT D τ) - M'.map (embT D τ) * Matrix.of (z τ) * M₂.map (embT D τ)
  rw [Matrix.map_sub _ (map_sub _), Matrix.mul_sub]

theorem Hf_eq_trace (T : Tor D) (z w : VC D N N') :
    Hf D T z w = (∑ τ, Matrix.trace (Matrix.of (z τ) * (Matrix.of (w τ))ᴴ)) / (area T.abelian₂ : ℂ) := by
  simp [Hf, Matrix.trace, Matrix.mul_apply]

theorem Hf_mulV (T : Tor D) (M' : Matrix (Fin N') (Fin N') D.host.E) (M : Matrix (Fin N) (Fin N) D.host.E)
    (z w : VC D N N') : Hf D T (mulV D M' M z) w = Hf D T z (mulV D (adj D M') (adj D M) w) := by
  rw [Hf_eq_trace, Hf_eq_trace]
  congr 1
  refine Finset.sum_congr rfl fun τ _ => ?_
  change Matrix.trace (M'.map (embT D τ) * Matrix.of (z τ) * M.map (embT D τ) * (Matrix.of (w τ))ᴴ) =
    Matrix.trace (Matrix.of (z τ) * ((adj D M').map (embT D τ) * Matrix.of (w τ) * (adj D M).map (embT D τ))ᴴ)
  rw [adj_map, adj_map, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

theorem pull_eq (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (γ : Matrix (Fin N) (Fin N) D.host.E)
    (γ' : Matrix (Fin N') (Fin N') D.host.E) (G : VC D N N' → ℂ) :
    pull D (tor0 D cc δ) γ γ' G = fun z => G (mulV D (adj D γ') γ z) := by
  funext z
  unfold pull
  congr 1
  funext τ
  rw [mulV_apply, adj_map]
  rfl

theorem mulV_pt (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (M' : Matrix (Fin N') (Fin N') D.host.E)
    (M : Matrix (Fin N) (Fin N) D.host.E) (z : Matrix (Fin N') (Fin N) D.host.E) :
    mulV D M' M (pt D (tor0 D cc δ) δ z) = pt D (tor0 D cc δ) δ (M' * z * M) := by
  unfold pt
  rw [map_smul]
  congr 1
  funext τ
  change M'.map (embT D τ) * z.map (embT D τ) * M.map (embT D τ) = (M' * z * M).map (embT D τ)
  simp only [Matrix.map_mul]

theorem adj_mul {n : ℕ} (M₁ M₂ : Matrix (Fin n) (Fin n) D.host.E) : adj D (M₁ * M₂) = adj D M₂ * adj D M₁ := by
  unfold adj
  rw [← Matrix.transpose_mul]
  congr 1
  exact Matrix.map_mul (f := (D.host.conj : D.host.E →+* D.host.E))

theorem adj_one {n : ℕ} : adj D (1 : Matrix (Fin n) (Fin n) D.host.E) = 1 := by
  unfold adj
  rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one]

end GlobalTheory.RatEqui
