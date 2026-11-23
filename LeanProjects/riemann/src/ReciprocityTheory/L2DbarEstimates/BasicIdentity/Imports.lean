import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.Imports
import ReciprocityTheory.L2DbarEstimates.BasicIdentity.BasicIdentityStatement
import ReciprocityTheory.L2DbarEstimates.BasicIdentity.HasCompactSupportDTw
import ReciprocityTheory.L2DbarEstimates.BasicIdentity.HalfSumNormSubSq
import ReciprocityTheory.L2DbarEstimates.BasicIdentity.HasCompactSupportOfVanish
import ReciprocityTheory.L2DbarEstimates.BasicIdentity.TstarNormSq

namespace ReciprocityTheory.L2DbarEstimates.E

open MeasureTheory
open scoped ComplexConjugate

noncomputable section

theorem ap (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [MeasurableSpace M] [BorelSpace M] : APStatement n M := by
  intro z hz ph ψ ε f hph hψ hε hf
  have hph1 : CkR n z 1 ph := Ck.mono n z 1 2 (by norm_num) _ hph
  have hf1 : ∀ j, Ck n z 1 (fun y => f y j) := fun j => Ck.mono n z 1 2 (by norm_num) _ (hf j).1

  have hphc : Continuous ph := Complex.continuous_re.comp (Ck.continuous n z hz 2 _ hph)
  have hEr : Continuous (fun x => Real.exp (-ph x)) := Real.continuous_exp.comp hphc.neg
  have hFc : ∀ j, Continuous (fun y => f y j) := fun j => Ck.continuous n z hz 2 _ (hf j).1
  have hTc : ∀ j, Continuous (dTw n z ph j (fun y => f y j)) :=
    fun j => Ck.continuous n z hz 1 _ (ck_dTw n z 1 ph j _ hph (hf j).1)
  have hDc : ∀ j k, Continuous (db n z k (fun y => f y j)) :=
    fun j k => Ck.continuous n z hz 1 _ (Ck.db n z 1 k _ (hf j).1)
  have hLc : ∀ j k, Continuous (d n z j (db n z k (fun y => (ph y : ℂ)))) :=
    fun j k => Ck.continuous n z hz 0 _ (Ck.d n z 0 j _ (Ck.db n z 1 k _ hph))
  have hψc : ∀ j, Continuous (d n z j (fun y => (ψ y : ℂ))) :=
    fun j => Ck.continuous n z hz 0 _ (Ck.d n z 0 j _ hψ)
  have hAc : Continuous (fun x => ∑ j, dTw n z ph j (fun y => f y j) x) :=
    continuous_finsetSum _ (fun j _ => hTc j)
  have hSc : Continuous (fun x => ∑ j, (dTw n z ph j (fun y => f y j) x +
      f x j * d n z j (fun y => (ψ y : ℂ)) x)) :=
    continuous_finsetSum _ (fun j _ => (hTc j).add ((hFc j).mul (hψc j)))
  have hLevic : Continuous (fun x => (Levi n z ph x (fun j => f x j)).re) := by
    unfold Levi
    exact Complex.continuous_re.comp (continuous_finsetSum _ (fun j _ =>
      continuous_finsetSum _ (fun k _ =>
        ((hLc j k).mul (hFc j)).mul (Complex.continuous_conj.comp (hFc k)))))
  have hGc : Continuous (fun x => ∑ j, ∑ k, ‖db n z k (fun y => f y j) x‖ ^ 2) :=
    continuous_finsetSum _ (fun j _ => continuous_finsetSum _ (fun k _ => (hDc j k).norm.pow 2))
  have hdSc : Continuous (fun x => dSqR n z ψ x) :=
    continuous_finsetSum _ (fun j _ => (hψc j).norm.pow 2)
  have hF2c : Continuous (fun x => ∑ j, ‖f x j‖ ^ 2) :=
    continuous_finsetSum _ (fun j _ => (hFc j).norm.pow 2)

  set K : Set M := ⋃ j, tsupport (fun y => f y j) with hKdef
  have hK : IsCompact K := isCompact_iUnion (fun j => (hf j).2)
  have hcs : ∀ g : M → ℝ, (∀ x, x ∉ K → g x = 0) → HasCompactSupport g :=
    fun g hg => HasCompactSupport.intro hK hg
  have v0 : ∀ x, x ∉ K → ∀ j, f x j = 0 := fun x hx j =>
    image_eq_zero_of_notMem_tsupport (f := fun y => f y j) (x := x)
      (fun h => hx (Set.mem_iUnion.2 ⟨j, h⟩))
  have vD : ∀ x, x ∉ K → ∀ j k, db n z k (fun y => f y j) x = 0 := fun x hx j k =>
    image_eq_zero_of_notMem_tsupport
      (fun h => hx (Set.mem_iUnion.2 ⟨j, tsupport_db_subset n z k _ h⟩))
  have vT : ∀ x, x ∉ K → ∀ j, dTw n z ph j (fun y => f y j) x = 0 := fun x hx j =>
    image_eq_zero_of_notMem_tsupport
      (fun h => hx (Set.mem_iUnion.2 ⟨j, tsupport_dTw_subset n z ph j _ h⟩))
  have hnf : ∀ x, ‖f x‖ ^ 2 = ∑ j, ‖f x j‖ ^ 2 := fun x => EuclideanSpace.norm_sq_eq (f x)

  have iL : Integrable (fun x => (Levi n z ph x (fun j => f x j)).re * Real.exp (-ph x))
      (vol n z) :=
    integrable_of_continuous_real n z hz _ (hLevic.mul hEr)
      (hcs _ (fun x hx => by simp [Levi, v0 x hx]))
  have iG : Integrable (fun x => (∑ j, ∑ k, ‖db n z k (fun y => f y j) x‖ ^ 2) *
      Real.exp (-ph x)) (vol n z) :=
    integrable_of_continuous_real n z hz _ (hGc.mul hEr)
      (hcs _ (fun x hx => by simp [vD x hx]))
  have iA : Integrable (fun x => ‖∑ j, dTw n z ph j (fun y => f y j) x‖ ^ 2 *
      Real.exp (-ph x)) (vol n z) :=
    integrable_of_continuous_real n z hz _ ((hAc.norm.pow 2).mul hEr)
      (hcs _ (fun x hx => by simp [vT x hx]))
  have iS : Integrable (fun x => ‖∑ j, (dTw n z ph j (fun y => f y j) x +
      f x j * d n z j (fun y => (ψ y : ℂ)) x)‖ ^ 2 * Real.exp (-ph x)) (vol n z) :=
    integrable_of_continuous_real n z hz _ ((hSc.norm.pow 2).mul hEr)
      (hcs _ (fun x hx => by simp [vT x hx, v0 x hx]))
  have i1 : Integrable (fun x => ((Levi n z ph x (fun j => f x j)).re -
      (1 + 1 / ε) * dSqR n z ψ x * ‖f x‖ ^ 2) * Real.exp (-ph x)) (vol n z) := by
    simp only [hnf]
    exact integrable_of_continuous_real n z hz _
      ((hLevic.sub ((continuous_const.mul hdSc).mul hF2c)).mul hEr)
      (hcs _ (fun x hx => by simp [Levi, v0 x hx]))

  have hpt : ∀ x, ((Levi n z ph x (fun j => f x j)).re -
      (1 + 1 / ε) * dSqR n z ψ x * ‖f x‖ ^ 2) * Real.exp (-ph x) ≤
      (Levi n z ph x (fun j => f x j)).re * Real.exp (-ph x) +
        (∑ j, ∑ k, ‖db n z k (fun y => f y j) x‖ ^ 2) * Real.exp (-ph x) -
        ‖∑ j, dTw n z ph j (fun y => f y j) x‖ ^ 2 * Real.exp (-ph x) +
        (1 + ε) * (‖∑ j, (dTw n z ph j (fun y => f y j) x +
          f x j * d n z j (fun y => (ψ y : ℂ)) x)‖ ^ 2 * Real.exp (-ph x)) := by
    intro x
    have hsplit : (∑ j, (dTw n z ph j (fun y => f y j) x +
        f x j * d n z j (fun y => (ψ y : ℂ)) x)) =
        (∑ j, dTw n z ph j (fun y => f y j) x) +
          ∑ j, f x j * d n z j (fun y => (ψ y : ℂ)) x := Finset.sum_add_distrib
    have h1 := norm_sq_le_split (∑ j, dTw n z ph j (fun y => f y j) x)
      (∑ j, f x j * d n z j (fun y => (ψ y : ℂ)) x) ε hε
    rw [← hsplit] at h1
    have h2 := norm_sum_mul_sq_le (fun j => f x j) (fun j => d n z j (fun y => (ψ y : ℂ)) x)
    have hc : 0 ≤ 1 + 1 / ε := by positivity
    have he : 0 < Real.exp (-ph x) := Real.exp_pos _
    have hG0 : 0 ≤ ∑ j, ∑ k, ‖db n z k (fun y => f y j) x‖ ^ 2 := by positivity
    have h3 : ‖∑ j, dTw n z ph j (fun y => f y j) x‖ ^ 2 ≤
        (1 + ε) * ‖∑ j, (dTw n z ph j (fun y => f y j) x +
          f x j * d n z j (fun y => (ψ y : ℂ)) x)‖ ^ 2 +
          (1 + 1 / ε) * (dSqR n z ψ x * ‖f x‖ ^ 2) := by
      rw [hnf x]
      unfold dSqR
      nlinarith [mul_le_mul_of_nonneg_left h2 hc]
    nlinarith [mul_le_mul_of_nonneg_right h3 he.le, mul_nonneg hG0 he.le]

  have hmono : ∫ x, ((Levi n z ph x (fun j => f x j)).re - (1 + 1 / ε) * dSqR n z ψ x * ‖f x‖ ^ 2) * Real.exp (-ph x) ∂vol n z ≤
      (∫ x, (Levi n z ph x (fun j => f x j)).re * Real.exp (-ph x) ∂vol n z) +
        (∫ x, (∑ j, ∑ k, ‖db n z k (fun y => f y j) x‖ ^ 2) * Real.exp (-ph x) ∂vol n z) -
        (∫ x, ‖∑ j, dTw n z ph j (fun y => f y j) x‖ ^ 2 * Real.exp (-ph x) ∂vol n z) +
        (1 + ε) * ∫ x, ‖∑ j, (dTw n z ph j (fun y => f y j) x + f x j * d n z j (fun y => (ψ y : ℂ)) x)‖ ^ 2 * Real.exp (-ph x) ∂vol n z := by
    have j1 : Integrable (fun x => (Levi n z ph x (fun j => f x j)).re * Real.exp (-ph x) +
        (∑ j, ∑ k, ‖db n z k (fun y => f y j) x‖ ^ 2) * Real.exp (-ph x)) (vol n z) := iL.add iG
    have j2 : Integrable (fun x => (Levi n z ph x (fun j => f x j)).re * Real.exp (-ph x) +
        (∑ j, ∑ k, ‖db n z k (fun y => f y j) x‖ ^ 2) * Real.exp (-ph x) - ‖∑ j, dTw n z ph j (fun y => f y j) x‖ ^ 2 * Real.exp (-ph x)) (vol n z) := j1.sub iA
    have j3 : Integrable (fun x => (1 + ε) * (‖∑ j, (dTw n z ph j (fun y => f y j) x + f x j * d n z j (fun y => (ψ y : ℂ)) x)‖ ^ 2 * Real.exp (-ph x))) (vol n z) := iS.const_mul (1 + ε)
    rw [← integral_add iL iG, ← integral_sub j1 iA, ← integral_const_mul, ← integral_add j2 j3]
    exact integral_mono i1 (j2.add j3) hpt
  have hB := basicIdentity n M z hz ph f hph hf
  have hT : ∫ x, ‖tstar n z (fun y => ph y - 2 * ψ y) (fun y => ph y - ψ y) f x‖ ^ 2 *
      Real.exp (-(ph x - 2 * ψ x)) ∂vol n z =
      ∫ x, ‖∑ j, (dTw n z ph j (fun y => f y j) x +
        f x j * d n z j (fun y => (ψ y : ℂ)) x)‖ ^ 2 * Real.exp (-ph x) ∂vol n z := by
    congr 1
    funext x
    exact tstar_norm_sq n z hz ph ψ f hph1 hψ hf1 x
  rw [hT]
  linarith

end

end ReciprocityTheory.L2DbarEstimates.E
