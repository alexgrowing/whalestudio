import Mathlib
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.CapelliDeterminantBlockProduct
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds

open Matrix Finset

noncomputable section

namespace GlobalTheory.CompanionTheory.WtLinkPf

open PI.UpqRep

variable {n : ℕ}

def tor (θ : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.diagonal (fun a => Complex.exp ((θ a : ℂ) * Complex.I))

lemma tor_add (θ η : Fin n → ℝ) : tor (θ + η) = tor θ * tor η := by
  unfold tor
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext a
  rw [← Complex.exp_add]
  congr 1
  simp only [Pi.add_apply]
  push_cast
  ring

lemma tor_zero : tor (0 : Fin n → ℝ) = 1 := by
  unfold tor
  simp

lemma star_exp_mul (x : ℝ) : star (Complex.exp ((x : ℂ) * Complex.I)) * Complex.exp ((x : ℂ) * Complex.I) = 1 := by
  rw [Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]
  simp

lemma tor_mem_UJ (ε : Fin n → Bool) (θ : Fin n → ℝ) : tor θ ∈ UJset ε := by
  show (tor θ).conjTranspose * PI.UpqRep.Jm ε * tor θ = PI.UpqRep.Jm ε
  unfold tor PI.UpqRep.Jm
  rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext a
  rw [Pi.star_apply, mul_right_comm, star_exp_mul, one_mul]

lemma tor_mem_K (ε : Fin n → Bool) (θ : Fin n → ℝ) : tor θ ∈ Kset ε := by
  show tor θ ∈ Matrix.unitaryGroup (Fin n) ℂ ∧ tor θ * PI.UpqRep.Jm ε = PI.UpqRep.Jm ε * tor θ
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
    unfold tor
    rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal,
      show (1 : Matrix (Fin n) (Fin n) ℂ) = Matrix.diagonal (fun _ => 1) from Matrix.diagonal_one.symm]
    congr 1
    funext a
    rw [Pi.star_apply]
    exact star_exp_mul (θ a)
  · unfold tor PI.UpqRep.Jm
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext a
    ring

lemma diag_inG (ε : Fin n → Bool) (θ : Fin n → ℝ) :
    inG ε (Matrix.diagonal fun a => (θ a : ℂ) * Complex.I) := by
  show (Matrix.diagonal fun a => (θ a : ℂ) * Complex.I).conjTranspose * PI.UpqRep.Jm ε +
      PI.UpqRep.Jm ε * Matrix.diagonal (fun a => (θ a : ℂ) * Complex.I) = 0
  unfold PI.UpqRep.Jm
  rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal,
    Matrix.diagonal_add, ← Matrix.diagonal_zero]
  congr 1
  funext a
  rw [Pi.star_apply, Complex.star_def, map_mul, Complex.conj_ofReal, Complex.conj_I]
  ring

lemma exp_diag (θ : Fin n → ℝ) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • Matrix.diagonal fun a => (θ a : ℂ) * Complex.I) = tor (t • θ) := by
  rw [← Matrix.diagonal_smul, Matrix.exp_diagonal, Pi.exp_def]
  unfold tor
  congr 1
  funext a
  rw [← Complex.exp_eq_exp_ℂ]
  congr 1
  simp only [Pi.smul_apply, smul_eq_mul]
  push_cast
  ring

section

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

lemma deriv_zero {ε : Fin n → Bool} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {S : Submodule ℂ H}
    {E : Fin n → Fin n → Module.End ℂ S} (h : CompanionTheory.D.DSIC.IsSmMod ε σ S E) (θ : Fin n → ℝ) (v : S) :
    HasDerivAt (fun t : ℝ => σ (tor (t • θ)) v) (∑ a, ((θ a : ℂ) * Complex.I) • (E a a v : H)) 0 := by
  have h1 := h.real (Matrix.diagonal fun a => (θ a : ℂ) * Complex.I) (diag_inG ε θ) v
  simp only [exp_diag] at h1
  convert h1 using 1
  simp [Matrix.diagonal_apply]

lemma hasDerivAt_exp_mul (c : ℂ) (s : ℝ) :
    HasDerivAt (fun t : ℝ => Complex.exp ((t : ℂ) * c)) (Complex.exp ((s : ℂ) * c) * c) s := by
  have := ((hasDerivAt_id s).ofReal_comp.mul_const c).cexp
  simpa using this

lemma one_param (φ : ℝ → (H →L[ℂ] H)) (hadd : ∀ s t, φ (s + t) = φ s * φ t) (h0 : φ 0 = 1) (v : H) (c : ℂ)
    (hd : HasDerivAt (fun t => φ t v) (c • v) 0) : φ 1 v = Complex.exp c • v := by
  have hder : ∀ s : ℝ, HasDerivAt (fun t => φ t v) (c • φ s v) s := by
    intro s
    have h1 : HasDerivAt (fun u => φ s (φ u v)) (φ s (c • v)) 0 := by
      have := ((φ s).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hd
      simpa [Function.comp_def] using this
    have h2 : HasDerivAt (fun u => φ s (φ u v)) (φ s (c • v)) (s - s) := by
      rwa [sub_self]
    have h3 := HasDerivAt.comp_sub_const s s h2
    rw [map_smul] at h3
    convert h3 using 1
    funext t
    show φ t v = φ s (φ (t - s) v)
    rw [← ContinuousLinearMap.mul_apply, ← hadd, show s + (t - s) = t by ring]
  have hg : ∀ s : ℝ, HasDerivAt (fun t : ℝ => Complex.exp ((t : ℂ) * -c) • φ t v) 0 s := by
    intro s
    have := (hasDerivAt_exp_mul (-c) s).smul (hder s)
    convert this using 1
    · funext t
      rfl
    · rw [smul_smul, ← add_smul]
      simp
  have hdiff : Differentiable ℝ (fun t : ℝ => Complex.exp ((t : ℂ) * -c) • φ t v) :=
    fun s => (hg s).differentiableAt
  have hconst := is_const_of_deriv_eq_zero hdiff (fun s => (hg s).deriv) 1 0
  have hfinal : Complex.exp (-c) • φ 1 v = v := by
    simp only [Complex.ofReal_one, Complex.ofReal_zero, one_mul, zero_mul, Complex.exp_zero, one_smul, h0,
      ContinuousLinearMap.one_apply] at hconst
    exact hconst
  calc φ 1 v = Complex.exp c • (Complex.exp (-c) • φ 1 v) := by
        rw [smul_smul, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, one_smul]
    _ = Complex.exp c • v := by rw [hfinal]

end

theorem wtLink : CompanionTheory.D.DSIC.WtLink := by
  intro n ε H _ _ σ S E hrep h μ v
  have hG : ∀ a ∈ UJset ε, ∀ b ∈ UJset ε, σ (a * b) = σ a * σ b := by
    intro a ha b hb
    rw [ContinuousLinearMap.mul_def]
    exact hrep.1.2 a ha b hb
  have h1 : σ 1 = 1 := hrep.1.1
  constructor
  · intro hw θ _
    have hw' : ∀ a, E a a v = (μ a : ℂ) • v := hw
    let φ : ℝ → (H →L[ℂ] H) := fun t => σ (tor (t • θ))
    have hadd : ∀ s t, φ (s + t) = φ s * φ t := by
      intro s t
      show σ (tor ((s + t) • θ)) = σ (tor (s • θ)) * σ (tor (t • θ))
      rw [add_smul, tor_add]
      exact hG _ (tor_mem_UJ ε _) _ (tor_mem_UJ ε _)
    have hz : φ 0 = 1 := by
      show σ (tor ((0 : ℝ) • θ)) = 1
      rw [zero_smul, tor_zero]
      exact h1
    have hd : HasDerivAt (fun t => φ t (v : H))
        ((((∑ a, μ a * θ a : ℝ) : ℂ) * Complex.I) • (v : H)) 0 := by
      have := deriv_zero h θ v
      convert this using 1
      simp only [hw', Submodule.coe_smul, smul_smul]
      rw [← Finset.sum_smul]
      congr 1
      push_cast
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl (fun a _ => by ring)
    have key := one_param φ hadd hz (v : H) _ hd
    show σ (tor θ) (v : H) = _
    rw [show tor θ = tor ((1 : ℝ) • θ) by rw [one_smul]]
    exact key
  · intro hK a
    apply Subtype.ext
    rw [Submodule.coe_smul]
    let θ : Fin n → ℝ := Pi.single a 1
    have hf : (fun t : ℝ => σ (tor (t • θ)) (v : H)) =
        fun t : ℝ => Complex.exp ((t : ℂ) * ((μ a : ℂ) * Complex.I)) • (v : H) := by
      funext t
      have ht := hK (t • θ) (tor_mem_K ε _)
      rw [show tor (t • θ) = Matrix.diagonal (fun b => Complex.exp ((((t • θ) b : ℝ) : ℂ) * Complex.I)) from rfl, ht]
      congr 2
      simp [θ, Pi.single_apply]
      try (push_cast; ring)
    have d1 := deriv_zero h θ v
    rw [hf] at d1
    have d2 : HasDerivAt (fun t : ℝ => Complex.exp ((t : ℂ) * ((μ a : ℂ) * Complex.I)) • (v : H))
        (((μ a : ℂ) * Complex.I) • (v : H)) 0 := by
      have := (hasDerivAt_exp_mul ((μ a : ℂ) * Complex.I) 0).smul_const (v : H)
      simpa using this
    have hu := d1.unique d2
    have hsum : ∑ b, ((θ b : ℂ) * Complex.I) • (E b b v : H) = Complex.I • (E a a v : H) := by
      rw [Finset.sum_eq_single a]
      · simp [θ]
      · intro b _ hb
        simp [θ, Pi.single_apply, hb]
      · intro ha
        exact absurd (Finset.mem_univ a) ha
    rw [hsum] at hu
    calc (E a a v : H) = (-Complex.I * Complex.I) • (E a a v : H) := by
          rw [show -Complex.I * Complex.I = 1 by rw [neg_mul, Complex.I_mul_I, neg_neg], one_smul]
      _ = (-Complex.I) • (Complex.I • (E a a v : H)) := by rw [smul_smul]
      _ = (-Complex.I) • (((μ a : ℂ) * Complex.I) • (v : H)) := by rw [hu]
      _ = (μ a : ℂ) • (v : H) := by
          rw [smul_smul]
          congr 1
          rw [show -Complex.I * ((μ a : ℂ) * Complex.I) = (μ a : ℂ) * -(Complex.I * Complex.I) by ring,
            Complex.I_mul_I, neg_neg, mul_one]

end GlobalTheory.CompanionTheory.WtLinkPf
