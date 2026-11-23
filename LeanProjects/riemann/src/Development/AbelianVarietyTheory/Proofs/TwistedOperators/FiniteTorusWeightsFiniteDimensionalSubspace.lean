import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.PseudoCoefficientSeparation
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Formalism.RealPlaceAnalysis.StatementE
import Formalism.RealPlaceAnalysis.StatementB
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace

namespace GlobalTheory.TorusWtFin

open Complex

noncomputable abbrev dg {n : ℕ} (θ : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.diagonal (fun a => Complex.exp ((θ a : ℂ) * Complex.I))

lemma diag_mem (n : ℕ) (ε : Fin n → Bool) (θ : Fin n → ℝ) : dg θ ∈ Formalism.REAL.Kset ε := by
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff]
    rw [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal,
      ← Matrix.diagonal_one]
    congr 1
    funext a
    simp only [Pi.star_apply]
    rw [Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]
    simp [Complex.conj_ofReal]
  · unfold Formalism.REAL.Jm
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext a
    ring

lemma sum_single {n : ℕ} (μ : Fin n → ℝ) (a : Fin n) (c : ℝ) :
    (∑ b, μ b * (Pi.single a c : Fin n → ℝ) b) = μ a * c := by
  simp [Pi.single_apply]

lemma wt_int {n : ℕ} (ε : Fin n → Bool) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) {μ : Fin n → ℝ} {v : H} (hv : v ≠ 0)
    (hw : Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset ε) ρ μ v) (a : Fin n) : ∃ k : ℤ, μ a = k := by
  have h1 := hw (Pi.single a (2 * Real.pi)) (diag_mem n ε _)
  have h0 := hw 0 (diag_mem n ε _)
  change ρ (dg _) v = _ at h1 h0
  have hD : dg (Pi.single a (2 * Real.pi) : Fin n → ℝ) = dg (0 : Fin n → ℝ) := by
    unfold dg
    congr 1
    funext b
    by_cases hb : b = a
    · subst hb
      simp only [Pi.single_eq_same, Pi.zero_apply, Complex.ofReal_zero, zero_mul, Complex.exp_zero]
      push_cast
      exact Complex.exp_two_pi_mul_I
    · simp [Pi.single_apply, hb]
  rw [sum_single] at h1
  rw [hD, h0] at h1
  simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero, Complex.ofReal_zero, zero_mul,
    Complex.exp_zero, one_smul] at h1
  have h2 : (Complex.exp (((μ a * (2 * Real.pi) : ℝ) : ℂ) * Complex.I) - 1) • v = 0 := by
    rw [sub_smul, one_smul, ← h1, sub_self]
  have h3 : Complex.exp (((μ a * (2 * Real.pi) : ℝ) : ℂ) * Complex.I) = 1 := by
    rcases smul_eq_zero.1 h2 with h | h
    · exact sub_eq_zero.1 h
    · exact absurd h hv
  obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.1 h3
  refine ⟨k, ?_⟩
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h4 : ((μ a : ℝ) : ℂ) = (k : ℂ) := by
    have := hk
    push_cast at this
    have hI : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by simp [hpi, Complex.I_ne_zero]
    apply mul_right_cancel₀ hI
    linear_combination this
  exact_mod_cast h4

lemma exp_injOn : Set.InjOn (fun x : ℝ => Complex.exp ((x : ℂ) * Complex.I)) {x | ∃ k : ℤ, x = k} := by
  rintro x ⟨k, rfl⟩ y ⟨k', rfl⟩ h
  simp only at h
  have h1 : Complex.exp ((((k - k' : ℤ) : ℝ) : ℂ) * Complex.I) = 1 := by
    have h' : Complex.exp ((k : ℂ) * Complex.I) = Complex.exp ((k' : ℂ) * Complex.I) := by
      exact_mod_cast h
    push_cast
    rw [sub_mul, Complex.exp_sub, h', div_self (Complex.exp_ne_zero _)]
  obtain ⟨m, hm⟩ := Complex.exp_eq_one_iff.1 h1
  have hm' : (((k - k' : ℤ) : ℝ) : ℂ) = ((2 * m * Real.pi : ℝ) : ℂ) := by
    push_cast
    apply mul_right_cancel₀ Complex.I_ne_zero
    push_cast at hm
    linear_combination hm
  have hm'' : ((k - k' : ℤ) : ℝ) = ((2 * m : ℤ) : ℝ) * Real.pi := by
    have := Complex.ofReal_injective hm'
    push_cast at this ⊢
    linarith
  by_cases h0 : (2 * m : ℤ) = 0
  · rw [h0] at hm''
    simp only [Int.cast_zero, zero_mul] at hm''
    have : (k - k' : ℤ) = 0 := by exact_mod_cast hm''
    have : k = k' := by omega
    rw [this]
  · exact absurd hm''.symm ((irrational_pi.intCast_mul h0).ne_int _)

theorem finite_weights : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (S : Submodule ℂ H), FiniteDimensional ℂ S → ∃ F : Finset (Fin n → ℝ), ∀ (μ : Fin n → ℝ) (v : H), v ∈ S → v ≠ 0 → Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset ε) ρ μ v → μ ∈ F := by
  intro n ε H _ _ ρ S hS
  let W : Set (Fin n → ℝ) := {μ | ∃ v ∈ S, v ≠ 0 ∧ Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset ε) ρ μ v}
  suffices hW : W.Finite by
    exact ⟨hW.toFinset, fun μ v hv h0 hw => hW.mem_toFinset.2 ⟨v, hv, h0, hw⟩⟩

  let T : Fin n → Module.End ℂ H := fun a => (ρ (dg (Pi.single a (1 : ℝ)))).toLinearMap
  let C : Fin n → Set ℂ := fun a => {c | ∃ v ∈ S, v ≠ 0 ∧ T a v = c • v}
  have hC : ∀ a, (C a).Finite := by
    intro a
    have hx : ∀ c : C a, ∃ v : S, (v : H) ≠ 0 ∧ T a v = (c : ℂ) • (v : H) := fun c => by
      obtain ⟨v, hvS, hv0, hv⟩ := c.2
      exact ⟨⟨v, hvS⟩, hv0, hv⟩
    choose xs hxs using hx
    have hli : LinearIndependent ℂ (fun c : C a => ((xs c : S) : H)) :=
      (T a).eigenvectors_linearIndependent (C a) (fun c => (xs c : H))
        (fun c => ⟨Module.End.mem_eigenspace_iff.2 (hxs c).2, (hxs c).1⟩)
    have hli' : LinearIndependent ℂ xs := LinearIndependent.of_comp S.subtype hli
    have := hli'.finite
    exact Set.finite_coe_iff.1 this
  let Z : Fin n → Set ℝ := fun a => {x | (∃ k : ℤ, x = k) ∧ Complex.exp ((x : ℂ) * Complex.I) ∈ C a}
  have hZ : ∀ a, (Z a).Finite := by
    intro a
    refine Set.Finite.of_finite_image ((hC a).subset ?_) (exp_injOn.mono fun x hx => hx.1)
    rintro _ ⟨x, hx, rfl⟩
    exact hx.2
  refine (Set.Finite.pi hZ).subset ?_
  rintro μ ⟨v, hvS, hv0, hw⟩ a _
  refine ⟨wt_int ε ρ hv0 hw a, v, hvS, hv0, ?_⟩
  have h := hw (Pi.single a (1 : ℝ)) (diag_mem n ε _)
  rw [sum_single, mul_one] at h
  exact h

end GlobalTheory.TorusWtFin
