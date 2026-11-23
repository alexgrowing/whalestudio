import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.StrSMul
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Imports

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

theorem UpperTheory.iwahori_factorization_lower_diag_upper :
    ∀ {H Q : Type} [CommRing Q] (r : H → Matrix (Fin 3) (Fin 3) Q) (ψ : Fin 3 → H → Q) (s₀ : H), (∀ i j, i ≠ j → IsUnit (ψ i s₀ - ψ j s₀)) → (∀ s i j, i < j → r s i j = 0) → (∀ s i, r s i i = ψ i s) → (∀ g, ordProd r ψ g = 0) → ∃ α β γ : Q, ∀ s, r s 1 0 = (ψ 0 s - ψ 1 s) * α ∧ r s 2 1 = (ψ 1 s - ψ 2 s) * β ∧ r s 2 0 = (ψ 0 s - ψ 2 s) * γ - (ψ 1 s - ψ 2 s) * (α * β) := by
  intro H Q _ r ψ s₀ hu hup hd h0
  have key : ∀ a b c : H, (r a - ψ 0 a • 1) * ((r b - ψ 1 b • 1) * (r c - ψ 2 c • 1)) = 0 := by
    intro a b c
    simpa [ordProd, List.ofFn_succ] using h0 ![a, b, c]
  obtain ⟨u', e1⟩ : ∃ u' : Q, (ψ 0 s₀ - ψ 1 s₀) * u' = 1 := ⟨_, (hu 0 1 (by decide)).mul_val_inv⟩
  obtain ⟨v', e2⟩ : ∃ v' : Q, (ψ 1 s₀ - ψ 2 s₀) * v' = 1 := ⟨_, (hu 1 2 (by decide)).mul_val_inv⟩
  obtain ⟨w', e3⟩ : ∃ w' : Q, (ψ 0 s₀ - ψ 2 s₀) * w' = 1 := ⟨_, (hu 0 2 (by decide)).mul_val_inv⟩
  have hx : ∀ s, r s 1 0 = (ψ 0 s - ψ 1 s) * (r s₀ 1 0 * u') := by
    intro s
    have e := congrFun (congrFun (key s₀ s s₀) 1) 0
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply, hd, hup _ 0 1 (by decide),
      hup _ 0 2 (by decide), hup _ 1 2 (by decide)] at e
    have F : r s₀ 1 0 * (ψ 0 s - ψ 1 s) = (ψ 0 s₀ - ψ 1 s₀) * r s 1 0 := by
      linear_combination w' * e - (r s₀ 1 0 * (ψ 0 s - ψ 1 s) - (ψ 0 s₀ - ψ 1 s₀) * r s 1 0) * e3
    linear_combination (-(r s 1 0)) * e1 - u' * F
  have hy : ∀ s, r s 2 1 = (ψ 1 s - ψ 2 s) * (r s₀ 2 1 * v') := by
    intro s
    have e := congrFun (congrFun (key s₀ s₀ s) 2) 1
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply, hd, hup _ 0 1 (by decide),
      hup _ 0 2 (by decide), hup _ 1 2 (by decide)] at e
    have G : r s₀ 2 1 * (ψ 1 s - ψ 2 s) = (ψ 1 s₀ - ψ 2 s₀) * r s 2 1 := by
      linear_combination (-w') * e - (r s₀ 2 1 * (ψ 1 s - ψ 2 s) - (ψ 1 s₀ - ψ 2 s₀) * r s 2 1) * e3
    linear_combination (-(r s 2 1)) * e2 - v' * G
  refine ⟨r s₀ 1 0 * u', r s₀ 2 1 * v',
    r s₀ 1 0 * u' * (r s₀ 2 1 * v') +
      ((ψ 1 s₀ - ψ 2 s₀) * r s₀ 2 0 - r s₀ 2 1 * r s₀ 1 0) * w' * v', fun s => ⟨hx s, hy s, ?_⟩⟩
  have e := congrFun (congrFun (key s₀ s₀ s) 2) 0
  simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply, hd, hup _ 0 1 (by decide),
    hup _ 0 2 (by decide), hup _ 1 2 (by decide)] at e
  have Z : (ψ 0 s₀ - ψ 2 s₀) * (ψ 1 s₀ - ψ 2 s₀) * r s 2 0 =
      (ψ 0 s₀ - ψ 2 s₀) * r s₀ 2 1 * r s 1 0 +
        (ψ 0 s - ψ 2 s) * ((ψ 1 s₀ - ψ 2 s₀) * r s₀ 2 0 - r s₀ 2 1 * r s₀ 1 0) := by
    linear_combination e
  linear_combination w' * v' * Z + r s₀ 2 1 * v' * hx s +
    (r s₀ 2 1 * v' * r s 1 0 - r s 2 0) * e3 - (ψ 0 s₀ - ψ 2 s₀) * w' * r s 2 0 * e2
