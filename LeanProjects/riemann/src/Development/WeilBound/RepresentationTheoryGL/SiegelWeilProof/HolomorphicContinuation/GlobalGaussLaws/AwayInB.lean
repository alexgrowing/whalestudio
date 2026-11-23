import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.AwayInA

noncomputable section

open scoped Matrix ComplexConjugate SchwartzMap
open Matrix

namespace PositivityTheory.Rg.Sw.Glob.AwayPf

section
variable {T : Type} [Fintype T] [DecidableEq T] {m n : ℕ} (τ : T)

abbrev Bsp (τ : T) (m n : ℕ) : Type := {τ' : T // τ' ≠ τ} → Fin m → Fin n → ℂ

def extF (b : Bsp τ m n) : T → Fin m → Fin n → ℂ := fun τ' => if h : τ' = τ then 0 else b ⟨τ', h⟩

def extL : Bsp τ m n →L[ℝ] (T → Fin m → Fin n → ℂ) :=
  LinearMap.toContinuousLinearMap
    { toFun := extF τ
      map_add' := fun b b' => by
        funext τ' i j
        by_cases h : τ' = τ <;> simp [extF, h]
      map_smul' := fun r b => by
        funext τ' i j
        by_cases h : τ' = τ <;> simp [extF, h] }

def coordL (k : T × Fin m × Fin n) : Bsp τ m n →L[ℝ] ℂ :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℂ) k.2.2).comp
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => Fin n → ℂ) k.2.1).comp
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : T => Fin m → Fin n → ℂ) k.1).comp (extL τ)))

theorem tg_eval {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {σ : Type} (v : σ → E → ℂ)
    (hv : ∀ k, (v k).HasTemperateGrowth) (p : MvPolynomial σ ℂ) :
    (fun x => MvPolynomial.eval (fun k => v k x) p).HasTemperateGrowth := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    have := Function.HasTemperateGrowth.const (E := E) a
    convert this using 1
    all_goals first | rfl | (funext x; simp)
  | add p q hp hq =>
    have := hp.add hq
    convert this using 1
    all_goals first | rfl | (funext x; simp)
  | mul_X p k hp =>
    have := hp.mul (hv k)
    convert this using 1
    all_goals first | rfl | (funext x; simp)

def vC (k : T × Fin m × Fin n × Bool) (b : Bsp τ m n) : ℂ :=
  if k.2.2.2 then conj (coordL τ (k.1, k.2.1, k.2.2.1) b) else coordL τ (k.1, k.2.1, k.2.2.1) b

theorem tg_vC (k : T × Fin m × Fin n × Bool) : (vC (m := m) (n := n) τ k).HasTemperateGrowth := by
  by_cases hk : k.2.2.2 = true
  · have e : vC (m := m) (n := n) τ k = ⇑(Complex.conjCLE.toContinuousLinearMap.comp (coordL τ (k.1, k.2.1, k.2.2.1))) := by
      funext b
      simp [vC, hk]
    rw [e]
    exact ContinuousLinearMap.hasTemperateGrowth _
  · have e : vC (m := m) (n := n) τ k = ⇑(coordL τ (k.1, k.2.1, k.2.2.1)) := by
      funext b
      simp [vC, hk]
    rw [e]
    exact ContinuousLinearMap.hasTemperateGrowth _

theorem tg_poly (p : MvPolynomial (T × Fin m × Fin n × Bool) ℂ) :
    (fun b : Bsp τ m n => MvPolynomial.eval (fun k => vC τ k b) p).HasTemperateGrowth :=
  tg_eval _ (tg_vC τ) p

variable (fr : Matrix (Fin m) (Fin m) ℂ)

def eL (hfr : IsUnit fr.det) : (T → Fin m → Fin n → ℂ) ≃ₗ[ℝ] ((Fin m → Fin n → ℂ) × Bsp τ m n) where
  toFun z := (Matrix.of.symm (fr⁻¹ * Matrix.of (z τ)), fun τ' => z τ'.1)
  invFun ab := fun τ' => if h : τ' = τ then Matrix.of.symm (fr * Matrix.of ab.1) else ab.2 ⟨τ', h⟩
  map_add' z w := by
    ext1
    · exact Matrix.mul_add fr⁻¹ (of (z τ)) (of (w τ))
    · rfl
  map_smul' r z := by
    ext1
    · exact Matrix.mul_smul fr⁻¹ r (of (z τ))
    · rfl
  left_inv z := by
    funext τ'
    by_cases h : τ' = τ
    · subst h
      simp [Matrix.mul_nonsing_inv_cancel_left _ _ hfr]
    · simp [h]
  right_inv ab := by
    ext1
    · simp [Matrix.nonsing_inv_mul_cancel_left _ _ hfr]
    · funext τ'
      simp [τ'.2]

end

end PositivityTheory.Rg.Sw.Glob.AwayPf
