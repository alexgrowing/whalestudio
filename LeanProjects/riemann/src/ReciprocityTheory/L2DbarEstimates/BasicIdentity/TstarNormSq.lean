import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.Imports
import ReciprocityTheory.L2DbarEstimates.BasicIdentity.BasicIdentityStatement
import ReciprocityTheory.L2DbarEstimates.BasicIdentity.HasCompactSupportDTw

namespace ReciprocityTheory.L2DbarEstimates.E

open MeasureTheory
open scoped ComplexConjugate

noncomputable section

theorem tStarIbp (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] : TStarIbpStatement n M := by
  intro z hz ph₁ ph₂ g f _hph₁ hph₂ hg hf
  have hE := ck_expNeg n z 1 ph₂ hph₂
  have hF : ∀ j, Ck n z 1 (fun y => (Real.exp (-ph₂ y) : ℂ) * f y j) :=
    fun j => Ck.mul n z 1 _ _ hE (hf j).1
  have hFc : ∀ j, HasCompactSupport (fun y => (Real.exp (-ph₂ y) : ℂ) * f y j) :=
    fun j => (hf j).2.mul_left
  have hG : ∀ j, Ck n z 1 (fun y => conj ((Real.exp (-ph₂ y) : ℂ) * f y j)) :=
    fun j => Ck.conj n z 1 _ (hF j)
  have hGc : ∀ j, HasCompactSupport (fun y => conj ((Real.exp (-ph₂ y) : ℂ) * f y j)) :=
    fun j => (hFc j).comp_left (map_zero (starRingEnd ℂ))
  have hj : ∀ j, ∫ x, db n z j g x * conj ((Real.exp (-ph₂ x) : ℂ) * f x j) ∂vol n z =
      -∫ x, g x * conj (d n z j (fun y => (Real.exp (-ph₂ y) : ℂ) * f y j) x) ∂vol n z := by
    intro j
    rw [integral_db_mul n z hz j g _ hg (hG j) (hGc j)]
    congr 2
    funext x
    rw [db_conj]
  have hint1 : ∀ j ∈ (Finset.univ : Finset (Fin n)), Integrable
      (fun x => db n z j g x * conj ((Real.exp (-ph₂ x) : ℂ) * f x j)) (vol n z) := by
    intro j _
    apply integrable_of_continuous n z hz
    · exact (Ck.continuous n z hz 0 _ (Ck.db n z 0 j g hg)).mul
        (Ck.continuous n z hz 1 _ (hG j))
    · exact (hGc j).mul_left
  have hint2 : ∀ j ∈ (Finset.univ : Finset (Fin n)), Integrable
      (fun x => g x * conj (d n z j (fun y => (Real.exp (-ph₂ y) : ℂ) * f y j) x)) (vol n z) := by
    intro j _
    apply integrable_of_continuous n z hz
    · exact (Ck.continuous n z hz 1 _ hg).mul
        (Ck.continuous n z hz 0 _ (Ck.conj n z 0 _ (Ck.d n z 0 j _ (hF j))))
    · exact ((hasCompactSupport_d n z j _ (hFc j)).comp_left (map_zero (starRingEnd ℂ))).mul_left
  have lhs : ∫ x, (∑ j, db n z j g x * conj (f x j)) * (Real.exp (-ph₂ x) : ℂ) ∂vol n z =
      ∑ j, ∫ x, db n z j g x * conj ((Real.exp (-ph₂ x) : ℂ) * f x j) ∂vol n z := by
    rw [← integral_finsetSum _ hint1]
    congr 1
    funext x
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    simp only [map_mul, Complex.conj_ofReal]
    ring
  have rhs : ∫ x, g x * conj (tstar n z ph₁ ph₂ f x) * (Real.exp (-ph₁ x) : ℂ) ∂vol n z =
      ∑ j, -∫ x, g x * conj (d n z j (fun y => (Real.exp (-ph₂ y) : ℂ) * f y j) x) ∂vol n z := by
    rw [Finset.sum_neg_distrib, ← integral_finsetSum _ hint2, ← integral_neg]
    congr 1
    funext x
    have he : (Real.exp (ph₁ x) : ℂ) * (Real.exp (-ph₁ x) : ℂ) = 1 := by
      rw [← Complex.ofReal_mul, ← Real.exp_add, add_neg_cancel, Real.exp_zero, Complex.ofReal_one]
    unfold tstar
    rw [← Finset.mul_sum]
    simp only [map_neg, map_mul, map_sum, Complex.conj_ofReal]
    generalize (∑ j : Fin n, conj (d n z j (fun y => (Real.exp (-ph₂ y) : ℂ) * f y j) x)) = S
    linear_combination (-(g x * S)) * he
  rw [lhs, rhs]
  exact Finset.sum_congr rfl (fun j _ => hj j)

private theorem d_sub_of_ck_one (n : ℕ) {M : Type*} [TopologicalSpace M] (z : M → V n) (f g : M → ℂ)
    (hf : Ck n z 1 f) (hg : Ck n z 1 g) (j : Fin n) (x : M) :
    d n z j (fun y => f y - g y) x = d n z j f x - d n z j g x := by
  have h := d_add n z (fun y => f y - g y) g (Ck.sub n z 1 f g hf hg) hg j x
  simp only [sub_add_cancel] at h
  rw [h]
  ring

theorem tStarPoint (n : ℕ) (M : Type*) [TopologicalSpace M] : TStarPointStatement n M := by
  intro z hz ph ψ f hph hψ hf x
  have hg : Ck n z 1 (fun y => (ψ y : ℂ) - (ph y : ℂ)) := Ck.sub n z 1 _ _ hψ hph
  have hE : Ck n z 1 (fun y => Complex.exp ((ψ y : ℂ) - (ph y : ℂ))) := Ck.cexp n z 1 _ hg
  have hEfun : (fun y => (Real.exp (-(ph y - ψ y)) : ℂ)) =
      fun y => Complex.exp ((ψ y : ℂ) - (ph y : ℂ)) := by
    funext y
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  have hdE : ∀ j, d n z j (fun y => Complex.exp ((ψ y : ℂ) - (ph y : ℂ))) x =
      Complex.exp ((ψ x : ℂ) - (ph x : ℂ)) *
        (d n z j (fun y => (ψ y : ℂ)) x - d n z j (fun y => (ph y : ℂ)) x) := by
    intro j
    rw [d_cexp n z _ hg j x, d_sub_of_ck_one n z _ _ hψ hph j x]
  have key : ∀ j, d n z j (fun y => (Real.exp (-(ph y - ψ y)) : ℂ) * f y j) x =
      Complex.exp ((ψ x : ℂ) - (ph x : ℂ)) *
        (dTw n z ph j (fun y => f y j) x + f x j * d n z j (fun y => (ψ y : ℂ)) x) := by
    intro j
    have hfun : (fun y => (Real.exp (-(ph y - ψ y)) : ℂ) * f y j) =
        fun y => Complex.exp ((ψ y : ℂ) - (ph y : ℂ)) * f y j := by
      funext y
      rw [congrFun hEfun y]
    rw [hfun, d_mul n z _ _ hE (hf j) j x, hdE j]
    simp only [dTw]
    ring
  show (Real.exp (ψ x) : ℂ) * -((Real.exp (ph x - 2 * ψ x) : ℂ) *
      ∑ j, d n z j (fun y => (Real.exp (-(ph y - ψ y)) : ℂ) * f y j) x) = _
  rw [Finset.sum_congr rfl (fun j _ => key j), ← Finset.mul_sum]
  have hexp : (Real.exp (ψ x) : ℂ) * (Real.exp (ph x - 2 * ψ x) : ℂ) *
      Complex.exp ((ψ x : ℂ) - (ph x : ℂ)) = 1 := by
    rw [← Complex.ofReal_mul, ← Real.exp_add, Complex.ofReal_exp, ← Complex.exp_add,
      ← Complex.exp_zero]
    congr 1
    push_cast
    ring
  linear_combination (-(∑ j, (dTw n z ph j (fun y => f y j) x +
    f x j * d n z j (fun y => (ψ y : ℂ)) x))) * hexp

theorem tstar_norm_sq (n : ℕ) {M : Type*} [TopologicalSpace M] (z : M → V n)
    (hz : IsLocalHomeomorph z) (ph ψ : M → ℝ) (f : M → V n) (hph : CkR n z 1 ph)
    (hψ : CkR n z 1 ψ) (hf : ∀ j, Ck n z 1 (fun x => f x j)) (x : M) :
    ‖tstar n z (fun y => ph y - 2 * ψ y) (fun y => ph y - ψ y) f x‖ ^ 2 *
        Real.exp (-(ph x - 2 * ψ x)) =
      ‖∑ j, (dTw n z ph j (fun y => f y j) x + f x j * d n z j (fun y => (ψ y : ℂ)) x)‖ ^ 2 *
        Real.exp (-ph x) := by
  have hp := tStarPoint n M z hz ph ψ f hph hψ hf x
  set S := ∑ j, (dTw n z ph j (fun y => f y j) x + f x j * d n z j (fun y => (ψ y : ℂ)) x) with hS
  set T := tstar n z (fun y => ph y - 2 * ψ y) (fun y => ph y - ψ y) f x with hT
  have he := Real.exp_pos (ψ x)
  have hn : Real.exp (ψ x) * ‖T‖ = ‖S‖ := by
    have h1 := congrArg (fun w : ℂ => ‖w‖) hp
    simp only [norm_mul, norm_neg] at h1
    rw [← h1]
    congr 1
    first
      | rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos he]
      | simp [abs_of_pos he]
  have hT' : ‖T‖ = ‖S‖ * Real.exp (-ψ x) := by
    rw [Real.exp_neg, ← hn]
    first
      | rw [mul_comm (Real.exp (ψ x)), mul_assoc, mul_inv_cancel₀ he.ne', mul_one]
      | field_simp
  have hx : Real.exp (-ψ x) ^ 2 * Real.exp (-(ph x - 2 * ψ x)) = Real.exp (-ph x) := by
    rw [sq, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  rw [hT', mul_pow, mul_assoc, hx]

end

end ReciprocityTheory.L2DbarEstimates.E
