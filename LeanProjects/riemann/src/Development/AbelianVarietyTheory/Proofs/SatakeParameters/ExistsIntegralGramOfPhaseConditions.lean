import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemIntMat
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmithNormalFormIntegralMatrixStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CompleteSquareDiagonalNegPowUniformizerStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PhaseConditionSubIntegralMatrixStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PhaseConditionIntegralBasisChangeStatement

noncomputable section
open Matrix

namespace GlobalTheory.Hk3.HoweDuality.Square

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem mul_int {a b c : ℕ} {A : Matrix (Fin a) (Fin b) L} {B : Matrix (Fin b) (Fin c) L}
    (hA : ∀ i j, A i j ∈ Formalism.UG.intL L) (hB : ∀ i j, B i j ∈ Formalism.UG.intL L) (i : Fin a) (j : Fin c) :
    (A * B) i j ∈ Formalism.UG.intL L := by
  rw [Matrix.mul_apply]
  exact Subring.sum_mem _ fun k _ => Subring.mul_mem _ (hA i k) (hB k j)

theorem star_int {σ : L →+* L} (hv : ∀ x, Valued.v (σ x) = Valued.v x) {a b : ℕ} {A : Matrix (Fin a) (Fin b) L}
    (hA : ∀ i j, A i j ∈ Formalism.UG.intL L) (i : Fin b) (j : Fin a) :
    (Matrix.transpose (A.map σ)) i j ∈ Formalism.UG.intL L := by
  have h := hA j i
  simp only [Matrix.transpose_apply, Matrix.map_apply]
  change Valued.v (σ (A j i)) ≤ 1
  rw [hv]; exact h

theorem gen {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {ϖ : L} {σ : L →+* L} {q : ℕ} {δ : L}
    {n n' : ℕ} {A B : Matrix (Fin n) (Fin n) L} {ψ : AddChar L ℂ}
    (hU : Formalism.UG.IsUnramInv ϖ σ q) (hq : Odd q) (hA : ∀ i j, A i j ∈ Formalism.UG.intL L)
    (hB : ∀ i j, B i j ∈ Formalism.UG.intL L) (hAB : A * B = 1) (hAh : ∀ i j, σ (A i j) = A j i)
    (hδ : Valued.v δ = 1 ∧ σ δ = -δ) (hpi : ∀ a ∈ Formalism.UG.intL L, σ a = a → ψ a = 1)
    (hne : ∃ a ∈ Formalism.UG.intL L, σ a = a ∧ ψ (ϖ⁻¹ * a) ≠ 1) (x : Matrix (Fin n') (Fin n) L)
    (hx : (∀ C : Matrix (Fin n') (Fin n') L, (∀ i j, σ (C i j) = - C j i) → (∀ i j, Valued.v (C i j) < 1) →
      (∀ i j, (C * x) i j ∈ Formalism.UG.intL L) →
      ψ ((δ * Matrix.trace (C * (x * A * Matrix.transpose ((x).map σ))) + σ (δ * Matrix.trace (C * (x * A * Matrix.transpose ((x).map σ))))) / 2) = 1)) :
    ∃ l ∈ GlobalTheory.Hk3.HoweDuality.intMat L n' n,
      ∀ i j, ((x - l) * A * Matrix.transpose ((x - l).map σ)) i j ∈ Formalism.UG.intL L := by
  have hσ : ∀ x, σ (σ x) = x := hU.1
  have hv : ∀ x, Valued.v (σ x) = Valued.v x := hU.2.1
  obtain ⟨P, P', Q, Q', a, hP, hP', hPP', hQ, hQ', hQQ', hE⟩ := GlobalTheory.T.smith_normal_form_integral_matrix L ϖ hU.2.2.2.1 n n' x
  have hQ'Q : Q' * Q = 1 := mul_eq_one_comm.mp hQQ'
  have hP'P : P' * P = 1 := mul_eq_one_comm.mp hPP'
  have hA'i : ∀ i j, (Q' * A * Matrix.transpose (Q'.map σ)) i j ∈ Formalism.UG.intL L :=
    mul_int (mul_int hQ' hA) (star_int hv hQ')
  have hB'i : ∀ i j, (Matrix.transpose (Q.map σ) * B * Q) i j ∈ Formalism.UG.intL L :=
    mul_int (mul_int (star_int hv hQ) hB) hQ
  have h1 : Matrix.transpose (Q'.map σ) * Matrix.transpose (Q.map σ) = 1 := by
    rw [← Matrix.transpose_mul, ← Matrix.map_mul, hQQ', Matrix.map_one σ (map_zero σ) (map_one σ), Matrix.transpose_one]
  have hA'B' : (Q' * A * Matrix.transpose (Q'.map σ)) * (Matrix.transpose (Q.map σ) * B * Q) = 1 := by
    calc (Q' * A * Matrix.transpose (Q'.map σ)) * (Matrix.transpose (Q.map σ) * B * Q)
        = Q' * A * (Matrix.transpose (Q'.map σ) * Matrix.transpose (Q.map σ)) * B * Q := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [h1, Matrix.mul_one, Matrix.mul_assoc Q' A B, hAB, Matrix.mul_one, hQ'Q]
  have hAm : A.map σ = Matrix.transpose A := by ext i j; simp [hAh]
  have hQm : (Q'.map σ).map σ = Q' := by ext i j; simp [hσ]
  have hA'h : ∀ i j, σ ((Q' * A * Matrix.transpose (Q'.map σ)) i j) = (Q' * A * Matrix.transpose (Q'.map σ)) j i := by
    have hm : (Q' * A * Matrix.transpose (Q'.map σ)).map σ = Matrix.transpose (Q' * A * Matrix.transpose (Q'.map σ)) := by
      have hQt : (Matrix.transpose (Q'.map σ)).map σ = Matrix.transpose Q' := by ext i j; simp [hσ]
      rw [Matrix.map_mul, Matrix.map_mul, hAm, hQt]
      simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
    intro i j
    have := congrFun (congrFun hm i) j
    simpa using this
  have hy := GlobalTheory.T.phaseCondition_integral_basisChange L σ δ n n' A ψ P Q Q' hσ hv hP hQ' hQQ' x hx
  have hD := GlobalTheory.T.phaseCondition_sub_integral_matrix L ϖ σ q δ n n' _ ψ hU hq hA'i hδ.1 hδ.2 hpi (P * x * Q) _ hE hy
  rw [sub_sub_cancel] at hD
  obtain ⟨l', hl', hG⟩ := GlobalTheory.T.completeSquare_diagonalNegPowUniformizer L ϖ σ q δ n n' _ _ ψ hU hq hA'i hB'i hA'B' hA'h hδ hpi hne a hD
  refine ⟨P' * ((P * x * Q - (Matrix.of (fun (i : Fin n') (j : Fin n) => if (i : ℕ) = (j : ℕ) ∧ 0 < a i then ϖ⁻¹ ^ a i else 0))) + l') * Q', ?_, ?_⟩
  · intro i j
    exact mul_int (mul_int hP' (fun i j => add_mem (hE i j) (hl' i j))) hQ' i j
  · have hxe : x - P' * ((P * x * Q - (Matrix.of (fun (i : Fin n') (j : Fin n) => if (i : ℕ) = (j : ℕ) ∧ 0 < a i then ϖ⁻¹ ^ a i else 0))) + l') * Q' = P' * ((Matrix.of (fun (i : Fin n') (j : Fin n) => if (i : ℕ) = (j : ℕ) ∧ 0 < a i then ϖ⁻¹ ^ a i else 0)) - l') * Q' := by
      have hx0 : x = P' * (P * x * Q) * Q' := by
        simp only [Matrix.mul_assoc, hQQ', Matrix.mul_one]
        rw [← Matrix.mul_assoc, hP'P, Matrix.one_mul]
      rw [show x - P' * ((P * x * Q - (Matrix.of (fun (i : Fin n') (j : Fin n) => if (i : ℕ) = (j : ℕ) ∧ 0 < a i then ϖ⁻¹ ^ a i else 0))) + l') * Q' = P' * (P * x * Q) * Q' - P' * ((P * x * Q - (Matrix.of (fun (i : Fin n') (j : Fin n) => if (i : ℕ) = (j : ℕ) ∧ 0 < a i then ϖ⁻¹ ^ a i else 0))) + l') * Q' from by rw [← hx0]]
      have hab : P * x * Q - ((P * x * Q - (Matrix.of (fun (i : Fin n') (j : Fin n) => if (i : ℕ) = (j : ℕ) ∧ 0 < a i then ϖ⁻¹ ^ a i else 0))) + l') = (Matrix.of (fun (i : Fin n') (j : Fin n) => if (i : ℕ) = (j : ℕ) ∧ 0 < a i then ϖ⁻¹ ^ a i else 0)) - l' := by abel
      rw [← Matrix.sub_mul, ← Matrix.mul_sub, hab]
    rw [hxe]
    have hg : (P' * ((Matrix.of (fun (i : Fin n') (j : Fin n) => if (i : ℕ) = (j : ℕ) ∧ 0 < a i then ϖ⁻¹ ^ a i else 0)) - l') * Q') * A * Matrix.transpose ((P' * ((Matrix.of (fun (i : Fin n') (j : Fin n) => if (i : ℕ) = (j : ℕ) ∧ 0 < a i then ϖ⁻¹ ^ a i else 0)) - l') * Q').map σ) =
        P' * (((Matrix.of (fun (i : Fin n') (j : Fin n) => if (i : ℕ) = (j : ℕ) ∧ 0 < a i then ϖ⁻¹ ^ a i else 0)) - l') * (Q' * A * Matrix.transpose (Q'.map σ)) * Matrix.transpose (((Matrix.of (fun (i : Fin n') (j : Fin n) => if (i : ℕ) = (j : ℕ) ∧ 0 < a i then ϖ⁻¹ ^ a i else 0)) - l').map σ)) * Matrix.transpose (P'.map σ) := by
      simp only [Matrix.map_mul, Matrix.transpose_mul, Matrix.mul_assoc]
    rw [hg]
    exact mul_int (mul_int hP' hG) (star_int hv hP')

end GlobalTheory.Hk3.HoweDuality.Square

theorem GlobalTheory.Hk3.HoweDuality.exists_int_gram_of_phases : ∀ (L : Type) [Field L] [CharZero L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ) (δ : L)
    (n n' : ℕ) (JS : GL (Fin n) L) (ψ : AddChar L ℂ),
    Formalism.UG.IsUnramInv ϖ σ q → Odd q → JS ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL L) →
    (∀ i j, σ ((JS : Matrix (Fin n) (Fin n) L) i j) = (JS : Matrix (Fin n) (Fin n) L) j i) →
    (Valued.v δ = 1 ∧ σ δ = -δ) → (∀ a ∈ Formalism.UG.intL L, σ a = a → ψ a = 1) →
    (∃ a ∈ Formalism.UG.intL L, σ a = a ∧ ψ (ϖ⁻¹ * a) ≠ 1) → ∀ x : Matrix (Fin n') (Fin n) L,
    (∀ C : Matrix (Fin n') (Fin n') L, (∀ i j, σ (C i j) = - C j i) → (∀ i j, Valued.v (C i j) < 1) →
    (∀ i j, (C * x) i j ∈ Formalism.UG.intL L) →
    ψ ((δ * Matrix.trace (C * (x * ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * Matrix.transpose (x.map σ))) + σ (δ * Matrix.trace (C * (x * ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * Matrix.transpose (x.map σ))))) / 2) = 1) →
    ∃ l ∈ GlobalTheory.Hk3.HoweDuality.intMat L n' n,
      ∀ i j, ((x - l) * ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * Matrix.transpose ((x - l).map σ)) i j ∈ Formalism.UG.intL L := by
  intro L _ _ _ ϖ σ q δ n n' JS ψ hU hq hJS hJh hδ hpi hne x hx
  have hσ : ∀ x, σ (σ x) = x := hU.1
  have glint_entry : ∀ {g : GL (Fin n) L}, g ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL L) → ∀ i j,
      (g : Matrix (Fin n) (Fin n) L) i j ∈ Formalism.UG.intL L := by
    intro g hg i j
    obtain ⟨k, rfl⟩ := MonoidHom.mem_range.mp hg
    exact (k.val i j).2
  have hJi : (JS⁻¹ : GL (Fin n) L) ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL L) := Subgroup.inv_mem _ hJS
  set P : Matrix (Fin n) (Fin n) L := ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) with hPdef
  have hSm : (JS : Matrix (Fin n) (Fin n) L).map σ = Matrix.transpose (JS : Matrix (Fin n) (Fin n) L) := by
    ext i j; simp [hJh]
  have hPJ : P * (JS : Matrix (Fin n) (Fin n) L) = 1 := by rw [hPdef]; exact JS.inv_mul
  have hJP : (JS : Matrix (Fin n) (Fin n) L) * P = 1 := by rw [hPdef]; exact JS.mul_inv
  have e1 : P.map σ * Matrix.transpose (JS : Matrix (Fin n) (Fin n) L) = 1 := by
    rw [← hSm, ← Matrix.map_mul, hPJ]; exact Matrix.map_one σ (map_zero σ) (map_one σ)
  have e2 : (JS : Matrix (Fin n) (Fin n) L) * Matrix.transpose (P.map σ) = 1 := by
    have := congrArg Matrix.transpose e1
    rwa [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_one] at this
  have e3 : Matrix.transpose (P.map σ) = P := by
    calc Matrix.transpose (P.map σ) = (P * (JS : Matrix (Fin n) (Fin n) L)) * Matrix.transpose (P.map σ) := by
          rw [hPJ, Matrix.one_mul]
      _ = P := by rw [Matrix.mul_assoc, e2, Matrix.mul_one]
  have hPh : ∀ i j, σ (P i j) = P j i := by
    intro i j
    have := congrFun (congrFun e3 j) i
    simpa using this
  exact GlobalTheory.Hk3.HoweDuality.Square.gen hU hq (glint_entry hJi) (glint_entry hJS) hPJ hPh hδ hpi hne x hx
