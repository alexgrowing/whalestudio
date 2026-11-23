import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.LineFormulas.RightRule
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.MemUnitaryGroupIffMulConjTranspose

noncomputable section

open Finset Matrix
open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.RightRule

open CompanionTheory.RgExh CompanionTheory.RgExh.Dec

variable {n : ℕ}

def RightOK (ε : Fin n → Bool) (X : GMod n) (c : X.V →ₗ[ℂ] (Matrix (Fin n) (Fin n) ℂ → ℂ)) : Prop :=
  ∀ (u : X.V) (Y : Matrix (Fin n) (Fin n) ℂ), Formalism.REAL.inG ε Y → ∀ g, Formalism.REAL.inUJ ε g →
    HasDerivAt (fun t : ℝ => c u (g * NormedSpace.exp ((t : ℂ) • Y))) (c (∑ a, ∑ b, Y a b • X.E a b u) g) 0

set_option backward.isDefEq.respectTransparency false in
theorem exp_entry (Y : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp ((t : ℂ) • Y) i j) (Y i j) 0 := by
  have e1 : (fun t : ℝ => NormedSpace.exp ((t : ℂ) • Y) i j) =
      fun t : ℝ => Matrix.entryLinearMap ℝ ℂ i j (NormedSpace.exp (t • Y)) := by
    funext t
    have : (t : ℂ) • Y = t • Y := by ext a b; simp [Complex.real_smul]
    rw [this]; rfl
  have e2 : Y i j = Matrix.entryLinearMap ℝ ℂ i j (NormedSpace.exp ((0 : ℝ) • Y) * Y) := by
    simp [NormedSpace.exp_zero]
  rw [e1, e2]
  open scoped Matrix.Norms.Operator in
  exact (LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℂ i j)).hasFDerivAt.comp_hasDerivAt
    (0 : ℝ) (hasDerivAt_exp_smul_const (𝕂 := ℝ) Y 0)

theorem mul_exp_entry (g Y : Matrix (Fin n) (Fin n) ℂ) (j i : Fin n) :
    HasDerivAt (fun t : ℝ => (g * NormedSpace.exp ((t : ℂ) • Y)) j i) ((g * Y) j i) 0 := by
  simp only [Matrix.mul_apply]
  exact HasDerivAt.fun_sum (u := Finset.univ) (A := fun l (t : ℝ) => g j l * NormedSpace.exp ((t : ℂ) • Y) l i)
    fun l _ => (exp_entry Y l i).const_mul (g j l)

theorem mul_exp_zero (g Y : Matrix (Fin n) (Fin n) ℂ) : g * NormedSpace.exp (((0 : ℝ) : ℂ) • Y) = g := by
  simp [NormedSpace.exp_zero]

theorem tens_action (X : GMod n) (Y : Matrix (Fin n) (Fin n) ℂ) (u : Fin n → X.V) (i : Fin n) :
    (∑ a, ∑ b, Y a b • (tens X).E a b u) i = (∑ a, ∑ b, Y a b • X.E a b (u i)) + ∑ b, Y i b • u b := by
  show (∑ a, ∑ b, (Y a b • tensE X a b u : Fin n → X.V)) i = _
  simp only [Finset.sum_apply, Pi.smul_apply, tensE_apply, smul_add, sum_add_distrib]
  congr 1
  rw [Finset.sum_eq_single i (fun a _ ha => by simp [Ne.symm ha]) (by simp)]
  simp

theorem tens_ok {ε : Fin n → Bool} {X : GMod n} {c : X.V →ₗ[ℂ] (Matrix (Fin n) (Fin n) ℂ → ℂ)}
    (h : RightOK ε X c) (j : Fin n) : RightOK ε (tens X) (tensCoef X c j) := by
  intro u Y hY g hg
  have h1 : ∀ i, HasDerivAt (fun t : ℝ => (g * NormedSpace.exp ((t : ℂ) • Y)) j i *
      c (u i) (g * NormedSpace.exp ((t : ℂ) • Y)))
      ((g * Y) j i * c (u i) g + g j i * c (∑ a, ∑ b, Y a b • X.E a b (u i)) g) 0 := by
    intro i
    refine ((mul_exp_entry g Y j i).fun_mul (h (u i) Y hY g hg)).congr_deriv ?_
    simp only [mul_exp_zero]
  have h2 := HasDerivAt.fun_sum (u := Finset.univ)
    (A := fun i (t : ℝ) => (g * NormedSpace.exp ((t : ℂ) • Y)) j i * c (u i) (g * NormedSpace.exp ((t : ℂ) • Y)))
    fun i _ => h1 i
  refine h2.congr_deriv ?_
  have e : ∀ i, c ((∑ a, ∑ b, Y a b • (tens X).E a b u) i) g =
      c (∑ a, ∑ b, Y a b • X.E a b (u i)) g + ∑ b, Y i b * c (u b) g := by
    intro i
    refine (congrArg (fun v => c v g) (tens_action X Y u i)).trans ?_
    simp only [map_add, Pi.add_apply, map_sum, Finset.sum_apply, map_smul, Pi.smul_apply, smul_eq_mul]
  show _ = ∑ i, g j i * c ((∑ a, ∑ b, Y a b • (tens X).E a b u) i) g
  refine Eq.trans ?_ (sum_congr rfl fun i _ => congrArg (g j i * ·) (e i).symm)
  simp only [mul_add, sum_add_distrib, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
  rw [add_comm]
  congr 1
  rw [Finset.sum_comm]
  exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring

theorem step_ok {ε : Fin n → Bool} {X : GMod n} {c : X.V →ₗ[ℂ] (Matrix (Fin n) (Fin n) ℂ → ℂ)}
    (h : RightOK ε X c) (z : ℂ) (j : Fin n) : RightOK ε (step X z) (stepCoef X z c j) := by
  intro u Y hY g hg
  let S : (step X z).V →ₗ[ℂ] (tens X).V := (stepSub X z).subtype
  have hS : ∀ a b w, S ((step X z).E a b w) = (tens X).E a b (S w) := fun _ _ _ => rfl
  have e : S (∑ a, ∑ b, Y a b • (step X z).E a b u) = ∑ a, ∑ b, Y a b • (tens X).E a b (S u) := by
    simp only [map_sum, map_smul, hS]
  have h1 := tens_ok h j (S u) Y hY g hg
  refine h1.congr_deriv ?_
  show tensCoef X c j _ g = tensCoef X c j (S _) g
  rw [e]

theorem path_ok {ε : Fin n → Bool} : ∀ (ss : List (Fin n)) (X : GMod n)
    (c : X.V →ₗ[ℂ] (Matrix (Fin n) (Fin n) ℂ → ℂ)) (χ : Fin n → ℂ) (js : List (Fin n)),
    RightOK ε X c → RightOK ε (path X χ ss) (pathCoef X c χ ss js)
  | [], _, _, _, _, h => h
  | s :: ss, X, c, χ, js, h => path_ok ss (step X (χ s)) (stepCoef X (χ s) c (js.headD s)) (χ + Pi.single s 1) js.tail
      (step_ok h _ _)

theorem base_ok {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}
    (hK : CompanionTheory.D.LK.IsKMod ε σ D E) (hσ : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ) (ξ : H) :
    RightOK ε ⟨D, E, hK.gl⟩ (baseCoef σ D ξ) := by
  intro u Y hY g hg
  let L : H →L[ℝ] ℂ := ((innerSL ℂ ξ).comp (σ g)).restrictScalars ℝ
  have h1 := L.hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hK.real Y hY u)
  have e : (fun t : ℝ => baseCoef σ D ξ u (g * NormedSpace.exp ((t : ℂ) • Y))) =
      L ∘ fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • Y)) (u : H) := by
    funext t
    show ⟪ξ, σ (g * NormedSpace.exp ((t : ℂ) • Y)) (u : H)⟫_ℂ = ⟪ξ, σ g (σ (NormedSpace.exp ((t : ℂ) • Y)) (u : H))⟫_ℂ
    rw [hσ.1.2 g hg _ (Formalism.REAL.exp_indefinite_unitary_holds n ε Y hY t)]
    rfl
  rw [e]
  refine h1.congr_deriv ?_
  show ⟪ξ, σ g (∑ a, ∑ b, Y a b • (E a b u : H))⟫_ℂ = ⟪ξ, σ g ((∑ a, ∑ b, Y a b • E a b u : D) : H)⟫_ℂ
  simp only [Submodule.coe_sum, Submodule.coe_smul]

theorem rightRule : CompanionTheory.RgExh.Dec.N.RightRule := by
  intro n ε H _ _ _ σ D E hK χ ss hσ i u X hX g hg
  exact path_ok ss ⟨D, E, hK.gl⟩ (baseCoef σ D (i.1 : H)) χ i.2 (base_ok hK hσ _) u X hX g hg

end GlobalTheory.CompanionTheory.RightRule
