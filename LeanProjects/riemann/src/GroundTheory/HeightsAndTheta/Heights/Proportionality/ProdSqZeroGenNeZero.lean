import Mathlib
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.IsPshLocallyIntegrableStatement
import GroundTheory.HeightsAndTheta.Heights.FubiniStudyChern
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Proportionality

open Filter Topology Finset

noncomputable section

def RegMaxHessian.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [Nonempty ι] [DecidableEq ι], ∃ C : ℝ, ∀ η : ℝ, 0 < η → ∀ (t : ι → ℝ) (i j : ι),
    |fderiv ℝ (fderiv ℝ (ReciprocityTheory.AnForm.A.regMax (ι := ι) η)) t (Pi.single i 1) (Pi.single j 1)|
      ≤ C / η

def mixedDeriv (f : (Fin 1 → ℂ) → ℂ) (z : Fin 1 → ℂ) : ℂ :=
  GroundTheory.Heights₂.Heights.wirtinger
    (fun w => GroundTheory.Heights₂.Heights.wirtingerBar f 0 w) 0 z

def CurvaturePlus.Statement : Prop :=
  ∀ z : Fin 1 → ℂ,
    mixedDeriv (fun u => ((Real.log (1 + ‖u 0‖ ^ 2) : ℝ) : ℂ)) z =
      (((1 + ‖z 0‖ ^ 2) ^ (-2 : ℤ) : ℝ) : ℂ)

def CurvatureMinus.Statement : Prop :=
  ∀ z : Fin 1 → ℂ, ‖z 0‖ < 1 →
    mixedDeriv (fun u => ((-Real.log (1 - ‖u 0‖ ^ 2) : ℝ) : ℂ)) z =
        (((1 - ‖z 0‖ ^ 2) ^ (-2 : ℤ) : ℝ) : ℂ) ∧
      0 < (1 - ‖z 0‖ ^ 2) ^ (-2 : ℤ)

example : ‖(fun _ : Fin 1 => (1 / 2 : ℂ)) 0‖ < 1 := by norm_num

def TopPowerDiagonal.Statement : Prop :=
  ∀ (R : Type) [CommRing R] (D : ℕ) (e a : Fin D → R), (∀ j, e j ^ 2 = 0) →
    (∑ j, a j * e j) ^ D = (D.factorial : R) * (∏ j, a j) * ∏ j, e j

def squaresIdeal (σ : Type) : Ideal (MvPolynomial σ ℚ) :=
  Ideal.span ((fun s => MvPolynomial.monomial s (1 : ℚ)) ''
    Set.range (fun i : σ => Finsupp.single i 2))

abbrev SquareZeroRing (σ : Type) : Type := MvPolynomial σ ℚ ⧸ squaresIdeal σ

def sqZeroGen {σ : Type} (i : σ) : SquareZeroRing σ :=
  Ideal.Quotient.mk _ (MvPolynomial.X i)

theorem sqZeroGen_sq {σ : Type} (i : σ) : sqZeroGen i ^ 2 = 0 := by
  rw [sqZeroGen, ← map_pow, Ideal.Quotient.eq_zero_iff_mem, MvPolynomial.X_pow_eq_monomial]
  exact Ideal.subset_span ⟨_, ⟨i, rfl⟩, rfl⟩

theorem prod_sqZeroGen_ne_zero {σ : Type} [Fintype σ] : ∏ i : σ, sqZeroGen i ≠ 0 := by
  classical
  have hx : ∏ i : σ, (MvPolynomial.X i : MvPolynomial σ ℚ) =
      MvPolynomial.monomial (∑ i : σ, Finsupp.single i 1) 1 := by
    rw [MvPolynomial.monomial_sum_one]
    rfl
  have hp : ∏ i : σ, sqZeroGen i =
      Ideal.Quotient.mk (squaresIdeal σ) (∏ i : σ, MvPolynomial.X i) := by
    simp [sqZeroGen, map_prod]
  rw [hp, ne_eq, Ideal.Quotient.eq_zero_iff_mem, hx, squaresIdeal,
    MvPolynomial.mem_ideal_span_monomial_image]
  intro h
  obtain ⟨si, ⟨j, rfl⟩, hle⟩ := h (∑ i : σ, Finsupp.single i 1)
    (by rw [MvPolynomial.support_monomial, if_neg one_ne_zero]; exact Finset.mem_singleton_self _)
  have := hle j
  simp [Finsupp.finsetSum_apply, Finsupp.single_apply] at this

example (D : ℕ) : (∀ j : Fin D, sqZeroGen j ^ 2 = 0) ∧ ∏ j : Fin D, sqZeroGen j ≠ 0 :=
  ⟨sqZeroGen_sq, prod_sqZeroGen_ne_zero⟩

def pairDiffProd {ι R : Type} [CommRing R] (P : Finset (ι × ι)) (lam : ι → R) : R :=
  ∏ p ∈ P, (lam p.1 - lam p.2)

def increasingPairs (N : ℕ) : Finset (Fin N × Fin N) :=
  Finset.univ.filter fun p => p.1 < p.2

def vandermondeDesc {R : Type} [CommRing R] (N : ℕ) (lam : Fin N → R) : R :=
  ∏ i : Fin N, ∏ l ∈ Finset.Ioi i, (lam i - lam l)

def TopPowerPairs.Statement : Prop :=
  (∀ (ι : Type) [LinearOrder ι] (R : Type) [CommRing R] (P : Finset (ι × ι)) (e : ι × ι → R)
      (lam : ι → R), (∀ p ∈ P, p.1 < p.2) → (∀ p ∈ P, e p ^ 2 = 0) →
      (∑ p ∈ P, (lam p.1 - lam p.2) * e p) ^ P.card =
        (P.card.factorial : R) * pairDiffProd P lam * ∏ p ∈ P, e p) ∧
  (∀ (R : Type) [CommRing R] (N : ℕ) (e : Fin N × Fin N → R) (lam : Fin N → R),
      (∀ p ∈ increasingPairs N, e p ^ 2 = 0) →
      (∑ p ∈ increasingPairs N, (lam p.1 - lam p.2) * e p) ^ N.choose 2 =
        ((N.choose 2).factorial : R) * vandermondeDesc N lam * ∏ p ∈ increasingPairs N, e p)

example : (∀ p ∈ increasingPairs 3, p.1 < p.2) ∧
    (∀ p ∈ increasingPairs 3, sqZeroGen p ^ 2 = 0) ∧ ∏ p : Fin 3 × Fin 3, sqZeroGen p ≠ 0 :=
  ⟨fun _p hp => (Finset.mem_filter.mp hp).2, fun q _ => sqZeroGen_sq q, prod_sqZeroGen_ne_zero⟩

def linForm {n : ℕ} (lam : Fin n → ℝ) : MvPolynomial (Fin n) ℝ :=
  ∑ i, MvPolynomial.C (lam i) * MvPolynomial.X i

def PolarisationPowers.Statement : Prop :=
  ∀ (n D : ℕ) (A B : MvPolynomial (Fin n) ℝ →ₗ[ℝ] ℝ),
    (∀ lam : Fin n → ℝ, A (linForm lam ^ D) = B (linForm lam ^ D)) →
      ∀ p ∈ MvPolynomial.homogeneousSubmodule (Fin n) ℝ D, A p = B p

example : (∀ lam : Fin 2 → ℝ,
      MvPolynomial.constantCoeff (linForm lam ^ 1) = (0 : MvPolynomial (Fin 2) ℝ →ₗ[ℝ] ℝ)
        (linForm lam ^ 1)) ∧
    MvPolynomial.constantCoeff (1 : MvPolynomial (Fin 2) ℝ) ≠ 0 := by
  refine ⟨fun lam => ?_, by simp⟩
  simp [linForm]

structure UICoreData where

  J : ℕ → ℝ → ℝ → ℝ

  j₀ : ℝ → ℝ

  C : ℝ → ℝ

  E : ℝ → ℝ
  J_nonneg : ∀ a ε t, 0 ≤ J a ε t
  J_mono : ∀ a t, MonotoneOn (fun ε => J a ε t) (Set.Ioi 0)
  J_zero_le : ∀ ε t, 0 < ε → 0 < t → J 0 ε t ≤ j₀ ε
  j₀_tendsto : Tendsto j₀ (𝓝[>] 0) (𝓝 0)
  C_nonneg : ∀ t₀, 0 ≤ C t₀
  E_tendsto : Tendsto E (𝓝[>] 0) (𝓝 0)
  step : ∀ a ε t t₀, 0 < ε → 0 < t → t ≤ t₀ → J (a + 1) ε t ≤ (1 + C t₀) * J a ε t + E t₀

def UniformIntegrabilityCore.Statement : Prop :=
  ∀ (d : UICoreData) (a : ℕ) (η : ℝ), 0 < η → ∃ ε₀ t₁ : ℝ, 0 < ε₀ ∧ 0 < t₁ ∧
    ∀ ε t, 0 < ε → ε ≤ ε₀ → 0 < t → t ≤ t₁ → d.J a ε t ≤ η

def UICoreData.example : UICoreData where
  J a ε t := |ε| + a * |t|
  j₀ ε := |ε|
  C t₀ := |t₀|
  E t₀ := |t₀|
  J_nonneg a ε t := by positivity
  J_mono a t := by
    intro x hx y hy hxy
    simp only [Set.mem_Ioi] at hx hy
    simp only [abs_of_pos hx, abs_of_pos hy]
    linarith
  J_zero_le ε t _ _ := by simp
  j₀_tendsto := by
    have : Tendsto (fun ε : ℝ => |ε|) (𝓝 0) (𝓝 0) := by
      simpa using (continuous_abs.tendsto (0 : ℝ))
    exact this.mono_left nhdsWithin_le_nhds
  C_nonneg t₀ := abs_nonneg t₀
  E_tendsto := by
    have : Tendsto (fun ε : ℝ => |ε|) (𝓝 0) (𝓝 0) := by
      simpa using (continuous_abs.tendsto (0 : ℝ))
    exact this.mono_left nhdsWithin_le_nhds
  step a ε t t₀ _ ht htt := by
    have h1 : |t| ≤ |t₀| := by
      rw [abs_of_pos ht, abs_of_pos (ht.trans_le htt)]; exact htt
    have h2 : 0 ≤ |t₀| * (|ε| + a * |t|) := by positivity
    push_cast
    nlinarith

structure CauchyPolyFamily (n D : ℕ) where

  F : ℝ → MvPolynomial (Fin n) ℝ

  δ : ℝ → ℝ

  R : ℝ
  degree_le : ∀ t, 0 < t → t ≤ 1 → (F t).totalDegree ≤ D
  δ_tendsto : Tendsto δ (𝓝[>] 0) (𝓝 0)
  R_pos : 0 < R
  cauchy : ∀ t t' (lam : Fin n → ℝ), 0 < t' → t' ≤ t → t ≤ 1 → ‖lam‖ ≤ R →
    |MvPolynomial.eval lam (F t) - MvPolynomial.eval lam (F t')| ≤ δ t

def CoefficientwiseLimit.Statement : Prop :=
  ∀ (n D : ℕ) (c : CauchyPolyFamily n D), ∃ P : MvPolynomial (Fin n) ℝ,
    P.totalDegree ≤ D ∧
    (∀ m : Fin n →₀ ℕ, Tendsto (fun t => (c.F t).coeff m) (𝓝[>] 0) (𝓝 (P.coeff m))) ∧
    ∀ lam : Fin n → ℝ,
      Tendsto (fun t => MvPolynomial.eval lam (c.F t)) (𝓝[>] 0) (𝓝 (MvPolynomial.eval lam P))

def CauchyPolyFamily.example : CauchyPolyFamily 1 1 where
  F t := MvPolynomial.C (1 + t) * MvPolynomial.X 0
  δ t := |t|
  R := 1
  degree_le t _ _ := by
    refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    rw [MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X]
  δ_tendsto := by
    have : Tendsto (fun ε : ℝ => |ε|) (𝓝 0) (𝓝 0) := by
      simpa using (continuous_abs.tendsto (0 : ℝ))
    exact this.mono_left nhdsWithin_le_nhds
  R_pos := one_pos
  cauchy t t' lam ht' htt _ hlam := by
    have hl : |lam 0| ≤ 1 := by
      have := norm_le_pi_norm lam 0
      rw [Real.norm_eq_abs] at this
      linarith
    simp only [MvPolynomial.eval_mul, MvPolynomial.eval_C, MvPolynomial.eval_X]
    have : (1 + t) * lam 0 - (1 + t') * lam 0 = (t - t') * lam 0 := by ring
    rw [this, abs_mul, abs_of_pos (ht'.trans_le htt)]
    rw [abs_of_nonneg (by linarith)]
    have h0 : 0 ≤ t - t' := by linarith
    nlinarith [abs_nonneg (lam 0)]

def AmplePerturbation.Statement : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℝ V] (D : ℕ) (hD : 0 < D)
    (I : MultilinearMap ℝ (fun _ : Fin D => V) ℝ) (L H b : V),
    (∀ (σ : Equiv.Perm (Fin D)) (v : Fin D → V), I (v ∘ σ) = I v) →
    0 < I (fun _ => L) →
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℚ, 0 < ε → (ε : ℝ) < ε₀ →
      (D : ℝ) * I (Function.update (fun _ => L + (ε : ℝ) • H) ⟨0, hD⟩
          ((ε : ℝ) • ((2 : ℝ) • H + b))) <
        I (fun _ => L + (ε : ℝ) • H)

example (D : ℕ) : (∀ (σ : Equiv.Perm (Fin D)) (v : Fin D → ℝ),
      MultilinearMap.mkPiAlgebra ℝ (Fin D) ℝ (v ∘ σ) = MultilinearMap.mkPiAlgebra ℝ (Fin D) ℝ v) ∧
    0 < MultilinearMap.mkPiAlgebra ℝ (Fin D) ℝ (fun _ => (1 : ℝ)) := by
  refine ⟨fun σ v => ?_, by simp⟩
  simp only [MultilinearMap.mkPiAlgebra_apply, Function.comp_apply]
  exact Equiv.prod_comp σ v

section Reflection

variable {M : Type} [AddCommGroup M] [Module ℝ M]

def diffCoeff (N : ℕ) (lam : ℕ → ℝ) (l : ℕ) : ℝ :=
  if l = N then lam N else lam l - lam (l + 1)

def weightComb (N : ℕ) (y : ℕ → M) (lam : ℕ → ℝ) : M :=
  ∑ l ∈ Finset.Icc 1 N, diffCoeff N lam l • y l

def reflXi (y : ℕ → M) (i : ℕ) : M :=
  (1 / 2 : ℝ) • (y (i - 1) + y (i + 1)) - y i

def reflInvPart (N : ℕ) (y : ℕ → M) (lam : ℕ → ℝ) (i : ℕ) : M :=
  ∑ l ∈ (Finset.Icc 1 N).erase i, diffCoeff N lam l • y l +
    diffCoeff N lam i • ((1 / 2 : ℝ) • (y (i - 1) + y (i + 1)))

def reflInvCoeff (N : ℕ) (lam : ℕ → ℝ) (i l : ℕ) : ℝ :=
  if l + 1 = i ∨ l = i + 1 then diffCoeff N lam l + diffCoeff N lam i / 2 else diffCoeff N lam l

def ReflectionWeights.Statement : Prop :=
  ∀ (M : Type) [AddCommGroup M] [Module ℝ M] (y : ℕ → M) (N : ℕ) (lam : ℕ → ℝ) (i : ℕ),
    y 0 = 0 → 2 ≤ N → 1 ≤ i → i < N →
    weightComb N y lam = reflInvPart N y lam i - diffCoeff N lam i • reflXi y i ∧
    weightComb N y (lam ∘ Equiv.swap i (i + 1)) =
      reflInvPart N y lam i + diffCoeff N lam i • reflXi y i ∧
    reflInvPart N y lam i = ∑ l ∈ (Finset.Icc 1 N).erase i, reflInvCoeff N lam i l • y l ∧
    ∀ l, l ≠ i → reflInvCoeff N (lam ∘ Equiv.swap i (i + 1)) i l = reflInvCoeff N lam i l

example : (fun l : ℕ => (l : ℝ)) 0 = 0 ∧ 2 ≤ 3 ∧ 1 ≤ 1 ∧ 1 < 3 := by norm_num

end Reflection

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Proportionality
