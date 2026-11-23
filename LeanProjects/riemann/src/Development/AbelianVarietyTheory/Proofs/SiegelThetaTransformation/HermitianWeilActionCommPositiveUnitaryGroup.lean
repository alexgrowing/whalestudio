import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HermitianWeilActionUnitaryGroupTestFunctionsStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SchwartzBruhatInvariantIntegralMatrixMulStatement

open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real

namespace GlobalTheory.SW.UnitaryLeft

noncomputable section

theorem sum_rows_eq_trace {n N : ℕ} (U V : Matrix (Fin n) (Fin N) ℂ) (A : Matrix (Fin N) (Fin N) ℂ) :
    ∑ k, U k ⬝ᵥ A *ᵥ V k = (U * A * Vᵀ).trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, dotProduct, Matrix.mulVec,
    Matrix.transpose_apply, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

theorem sum_rows_unitary {n N : ℕ} (P Q : Matrix (Fin n) (Fin n) ℂ) (hPQ : Qᵀ * P = 1)
    (U V : Matrix (Fin n) (Fin N) ℂ) (A : Matrix (Fin N) (Fin N) ℂ) :
    ∑ k, (P * U) k ⬝ᵥ A *ᵥ (Q * V) k = ∑ k, U k ⬝ᵥ A *ᵥ V k := by
  rw [sum_rows_eq_trace, sum_rows_eq_trace, Matrix.transpose_mul, Matrix.mul_assoc P,
    Matrix.mul_assoc P, Matrix.trace_mul_comm, ← Matrix.mul_assoc, Matrix.mul_assoc _ Qᵀ, hPQ,
    Matrix.mul_one]

theorem sum_rows_unitary' {n N : ℕ} (P Q : Matrix (Fin n) (Fin n) ℂ) (hPQ : Qᵀ * P = 1)
    (U V : Matrix (Fin n) (Fin N) ℂ) :
    ∑ k, (P * U) k ⬝ᵥ (Q * V) k = ∑ k, U k ⬝ᵥ V k := by
  simpa using sum_rows_unitary P Q hPQ U V 1

variable {E : Type} [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)) {n N : ℕ}

theorem emb_cc (τ : E →+* ℂ) (x : E) : τ (cc x) = conj (τ x) :=
  IsCMField.complexEmbedding_complexConj E τ x

theorem unit_map {h : Matrix (Fin n) (Fin n) E} (hh : ccT h * h = 1) (τ : E →+* ℂ) :
    ((h.map τ).map conj)ᵀ * h.map τ = 1 := by
  have h1 := congrArg (fun M : Matrix (Fin n) (Fin n) E => M.map τ) hh
  simp only [Matrix.map_mul] at h1
  rw [Matrix.map_one _ (map_zero τ) (map_one τ)] at h1
  rw [← h1]
  congr 1
  ext i j
  simp [ccT, emb_cc]

theorem unit_map' {h : Matrix (Fin n) (Fin n) E} (hh : ccT h * h = 1) (τ : E →+* ℂ) :
    (h.map τ)ᵀ * (h.map τ).map conj = 1 := by
  have h1 := congrArg Matrix.transpose (unit_map hh τ)
  simpa [Matrix.transpose_mul] using h1

def mv (h : Matrix (Fin n) (Fin n) E) (z : CM Ψ n N) : CM Ψ n N :=
  fun τ => (h.map τ.1).map conj * z τ

def mv' (h : Matrix (Fin n) (Fin n) E) (z : CM Ψ n N) : CM Ψ n N :=
  fun τ => h.map τ.1 * z τ

theorem expo_mul {h : Matrix (Fin n) (Fin n) E} (hh : ccT h * h = 1)
    (x : Matrix (Fin n) (Fin N) E) (Z : CM Ψ N N) (z z' : CM Ψ n N) :
    expo Ψ (h * x) Z (mv Ψ h z) (mv' Ψ h z') = expo Ψ x Z z z' := by
  unfold expo
  refine Finset.sum_congr rfl fun τ _ => ?_
  have e1 : ∀ (y : Matrix (Fin n) (Fin N) E) k, (fun a => τ.1 (y k a)) = (y.map τ.1) k :=
    fun _ _ => rfl
  have e2 : ∀ (y : Matrix (Fin n) (Fin N) E) k,
      (fun a => conj (τ.1 (y k a))) = ((y.map τ.1).map conj) k := fun _ _ => rfl
  simp only [e1, e2, Finset.sum_add_distrib, mv, mv']
  rw [Matrix.map_mul, Matrix.map_mul, sum_rows_unitary _ _ (unit_map hh τ.1),
    sum_rows_unitary' _ _ (unit_map hh τ.1), sum_rows_unitary' _ _ (unit_map hh τ.1)]

theorem thH_mul {h : Matrix (Fin n) (Fin n) E} (hh : ccT h * h = 1)
    (φ : Matrix (Fin n) (Fin N) E → ℂ) (Z : CM Ψ N N) (z z' : CM Ψ n N) :
    thH Ψ (fun x : Matrix (Fin n) (Fin N) E => φ (h * x)) Z z z' = thH Ψ φ Z (mv Ψ h z) (mv' Ψ h z') := by
  have hh' : h * ccT h = 1 := mul_eq_one_comm.1 hh
  let e : Matrix (Fin n) (Fin N) E ≃ Matrix (Fin n) (Fin N) E :=
    { toFun := fun x => h * x
      invFun := fun x => ccT h * x
      left_inv := fun x => by simp only [← Matrix.mul_assoc, hh, Matrix.one_mul]
      right_inv := fun x => by simp only [← Matrix.mul_assoc, hh', Matrix.one_mul] }
  unfold thH
  rw [← e.tsum_eq (fun x => φ x * cexp (2 * Real.pi * I * expo Ψ x Z (mv Ψ h z) (mv' Ψ h z')))]
  refine tsum_congr fun x => ?_
  change _ = φ (h * x) * cexp (2 * Real.pi * I * expo Ψ (h * x) Z (mv Ψ h z) (mv' Ψ h z'))
  rw [expo_mul Ψ hh]

theorem hFac_mv {h : Matrix (Fin n) (Fin n) E} (hh : ccT h * h = 1) (γ : M2 E N)
    (Z : CM Ψ N N) (z z' : CM Ψ n N) :
    hFac Ψ γ Z (mv Ψ h z) (mv' Ψ h z') = hFac Ψ γ Z z z' := by
  unfold hFac
  refine Finset.prod_congr rfl fun τ _ => ?_
  simp only [mv, mv']
  rw [sum_rows_unitary _ _ (unit_map hh τ.1)]

theorem mul_of_mulVec (P : Matrix (Fin n) (Fin n) ℂ) (A : Matrix (Fin N) (Fin N) ℂ)
    (z : Matrix (Fin n) (Fin N) ℂ) :
    P * (Matrix.of fun k => A *ᵥ z k) = Matrix.of fun k => A *ᵥ (P * z) k := by
  have e : ∀ w : Matrix (Fin n) (Fin N) ℂ, (Matrix.of fun k => A *ᵥ w k) = w * Aᵀ := by
    intro w; ext k a
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, mul_comm]
  rw [e, e, Matrix.mul_assoc]

theorem mul_of_vecMul (P : Matrix (Fin n) (Fin n) ℂ) (A : Matrix (Fin N) (Fin N) ℂ)
    (z : Matrix (Fin n) (Fin N) ℂ) :
    P * (Matrix.of fun k => z k ᵥ* A) = Matrix.of fun k => (P * z) k ᵥ* A := by
  have e : ∀ w : Matrix (Fin n) (Fin N) ℂ, (Matrix.of fun k => w k ᵥ* A) = w * A := by
    intro w; ext k a
    simp [Matrix.mul_apply, Matrix.vecMul, dotProduct]
  rw [e, e, Matrix.mul_assoc]

theorem transH_mul {h : Matrix (Fin n) (Fin n) E} (hh : ccT h * h = 1) (γ : M2 E N)
    {φ ψ : Matrix (Fin n) (Fin N) E → ℂ} (H : TransH Ψ γ φ ψ) :
    TransH Ψ γ (fun x : Matrix (Fin n) (Fin N) E => φ (h * x))
      (fun x : Matrix (Fin n) (Fin N) E => ψ (h * x)) := by
  intro Z hZ z z'
  rw [thH_mul Ψ hh ψ, thH_mul Ψ hh φ, ← hFac_mv Ψ hh, ← H Z hZ]
  congr 1
  · funext τ; exact mul_of_mulVec _ _ _
  · funext τ; exact mul_of_vecMul _ _ _

end

end GlobalTheory.SW.UnitaryLeft

open GlobalTheory.SW.UnitaryLeft in

theorem GlobalTheory.SW.weil_comp_unitary : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), IsType Ψ → ∀ (n N : ℕ), Even n → ∀ h : Matrix (Fin n) (Fin n) E, ccT h * h = 1 → ∀ φ : Matrix (Fin n) (Fin N) E → ℂ, IsSB φ → IsSB (fun x : Matrix (Fin n) (Fin N) E => φ (h * x)) ∧ (∀ γ ∈ UU E N, weil Ψ γ (fun x => φ (h * x)) = fun x => weil Ψ γ φ (h * x)) ∧ ∀ Z ∈ Hn Ψ N, thH Ψ (fun x => φ (h * x)) Z 0 0 = thH Ψ φ Z 0 0 ∧ eis Ψ (fun x => φ (h * x)) Z 0 0 = eis Ψ φ Z 0 0 := by
  intro E _ _ _ Ψ hΨ n N hn h hh φ hφ
  have hdet : h.det ≠ 0 := by
    have h1 := congrArg Matrix.det hh
    rw [Matrix.det_mul, Matrix.det_one] at h1
    exact right_ne_zero_of_mul_eq_one h1
  have hSB : ∀ ψ : Matrix (Fin n) (Fin N) E → ℂ, IsSB ψ →
      IsSB (fun x : Matrix (Fin n) (Fin N) E => ψ (h * x)) :=
    fun ψ hψ => ((GlobalTheory.T.schwartzBruhatInvariantIntegral_matrix_mul E (Fin n) (Fin N) ψ hψ).2 h hdet).1
  have hw : ∀ γ ∈ UU E N, weil Ψ γ (fun x => φ (h * x)) = fun x => weil Ψ γ φ (h * x) := by
    intro γ hγ
    obtain ⟨h1, h2, -⟩ := GlobalTheory.T.hermitianWeilAction_unitaryGroup_testFunctions E Ψ hΨ n N hn γ hγ φ hφ
    exact ((GlobalTheory.T.hermitianWeilAction_unitaryGroup_testFunctions E Ψ hΨ n N hn γ hγ _ (hSB φ hφ)).2.2.1 _ (hSB _ h1)
      (transH_mul Ψ hh γ h2)).symm
  refine ⟨hSB φ hφ, hw, fun Z _ => ⟨?_, ?_⟩⟩
  · refine (thH_mul Ψ hh φ Z 0 0).trans ?_
    congr 1
    · funext τ; simp [mv]
    · funext τ; simp [mv']
  · unfold eis
    refine tsum_congr fun U => ?_
    unfold eisTerm
    rw [hw _ U.2.choose_spec.1]
    simp
