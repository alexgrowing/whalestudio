import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.TwoTorsionKernelUniqueHolds
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.CoeffTwoPSeries
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.NotInKernelOfMultiplierTorsion
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.LatticePointInKernelSubgroup
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.StatementL

noncomputable section
open scoped BigOperators ComplexConjugate

namespace Formalism.L2.Th1.B.LCm

open Formalism.InvariantFactorPaths.G7 (Simeq)
open Formalism.L2.Th1.F (MulStable)
open Formalism.L2.Th1.E (Unif ptW inW px IntCurve OneUnit GaussOne)
open Polynomial

theorem norm_odd (T : ℤ) (hT : Odd T) : ‖(T : ℤ_[2])‖ = 1 := by
  refine le_antisymm (PadicInt.norm_le_one _) (not_lt.mp fun h => ?_)
  rw [PadicInt.norm_int_lt_one_iff_dvd] at h
  obtain ⟨k, hk⟩ := hT
  obtain ⟨m, hm⟩ := h
  push_cast at hm
  omega

theorem norm_even (N : ℤ) (hN : Even N) : ‖(N : ℤ_[2])‖ < 1 := by
  rw [PadicInt.norm_int_lt_one_iff_dvd]
  exact_mod_cast even_iff_two_dvd.mp hN

theorem quadratic_two_adic_holds : QuadTwoAdic := by
  intro T N hT hN
  let F : Polynomial ℤ_[2] := X ^ 2 - C (T : ℤ_[2]) * X + C (N : ℤ_[2])
  have hF0 : F.aeval (0 : ℤ_[2]) = (N : ℤ_[2]) := by simp [F]
  have hD0 : F.derivative.aeval (0 : ℤ_[2]) = -(T : ℤ_[2]) := by simp [F]
  have hnorm : ‖F.aeval (0 : ℤ_[2])‖ < ‖F.derivative.aeval (0 : ℤ_[2])‖ ^ 2 := by
    rw [hF0, hD0, norm_neg, norm_odd T hT]
    simpa using norm_even N hN
  obtain ⟨z, hz, hz1, -, -⟩ := hensels_lemma hnorm
  rw [hD0, norm_neg, norm_odd T hT, sub_zero] at hz1
  have hz' : z ^ 2 - (T : ℤ_[2]) * z + (N : ℤ_[2]) = 0 := by simpa [F] using hz
  refine ⟨(T : ℤ_[2]) - z, z, by ring, by linear_combination -hz', ?_, hz1⟩
  have h := PadicInt.norm_add_eq_max_of_ne (q := (T : ℤ_[2])) (r := -z)
    (by rw [norm_neg, norm_odd T hT]; exact hz1.ne')
  rw [sub_eq_add_neg, h, norm_neg, norm_odd T hT]
  exact max_eq_left hz1.le

theorem roots_two_adic_holds : RootsTwoAdic := by
  intro ι α T N hT hN hTo hNe
  obtain ⟨b, b', hs, hp, hb, hb'⟩ := quadratic_two_adic_holds T N hTo hNe
  let φ : ℤ_[2] →+* ℂ_[2] := UniformSpace.Completion.coeRingHom.comp
    ((algebraMap ℚ_[2] (PadicAlgCl 2)).comp PadicInt.Coe.ringHom)
  have hφ : ∀ x : ℤ_[2],
      φ x = ((algebraMap ℚ_[2] (PadicAlgCl 2) (x : ℚ_[2]) : PadicAlgCl 2) : ℂ_[2]) :=
    fun x => rfl
  refine ⟨b, b', hb, hb', ?_⟩
  simp only [← hφ]
  have hs' : φ b + φ b' = ι α + ι (conj α) := by
    rw [← map_add, ← map_add, hs, hT]
    simp
  have hp' : φ b * φ b' = ι α * ι (conj α) := by
    rw [← map_mul, ← map_mul, hp, hN]
    simp
  have key : (ι α - φ b) * (ι α - φ b') = 0 := by
    linear_combination (-(ι α)) * hs' + hp'
  rcases mul_eq_zero.mp key with h | h
  · have e : ι α = φ b := sub_eq_zero.mp h
    exact Or.inl ⟨e, by linear_combination -hs' - e⟩
  · have e : ι α = φ b' := sub_eq_zero.mp h
    exact Or.inr ⟨e, by linear_combination -hs' - e⟩

theorem mulStable_conj (L : PeriodPair) (α : ℂ) (T : ℤ) (h : MulStable L α)
    (hT : α + conj α = (T : ℂ)) : MulStable L (conj α) := by
  intro ω hω
  have h1 : conj α = (T : ℂ) - α := by rw [← hT]; ring
  rw [h1, sub_mul, ← zsmul_eq_mul]
  exact L.lattice.sub_mem (L.lattice.smul_mem T hω) (h ω hω)

theorem theta_zero_two_adic_trace : ThetaZeroTwoTrace := by
  have KI : KernelIntegral := KKer.KernelIntegral_of KNorm.two_torsion_kernel_unique_holds
    KNorm.torsion_norm_bound_holds KNorm.kappa_norm_holds KSum.kappa_sum_holds
  have hF : ThetaZeroAtTwo :=
    KFin.Th0TwoFinal_of (KFin.PointsTwoFinal_of KI (KFin.kernel_stable_of_integral_kernel KI) KNorm.two_torsion_kernel_unique_holds)
  intro L ι W hU hI ha α ω₀ T N hα hT hN hTo hNe hω h1 h2
  have hα0 : α ≠ 0 := by
    rintro rfl
    have h0 : (T : ℂ) = 0 := by rw [← hT]; simp
    have hT0 : T = 0 := by exact_mod_cast h0
    obtain ⟨k, hk⟩ := hTo
    omega
  obtain ⟨b, b', hb, hb', (⟨e1, e2⟩ | ⟨e1, e2⟩)⟩ := roots_two_adic_holds ι α T N hT hN hTo hNe
  · exact hF L ι W hU hI ha α ω₀ b b' hα0 hα e1 e2 hb hb' hω h2
  · have hc : conj (conj α) = α := Complex.conj_conj α
    have hs := mulStable_conj L α T hα hT
    exact hF L ι W hU hI ha (conj α) ω₀ b b' (by simpa using hα0) hs e2
      (by rw [hc]; exact e1) hb hb' hω (by rw [hc]; exact h1)

theorem conj_omegaK (d : ℕ) :
    conj (Formalism.L2.Th1.CM.omegaK d) = (1 - Complex.I * ((Real.sqrt d : ℝ) : ℂ)) / 2 := by
  simp only [Formalism.L2.Th1.CM.omegaK, map_div₀, map_add, map_one, map_mul, Complex.conj_I,
    Complex.conj_ofReal, map_ofNat]
  ring

theorem theta_zero_two_complex_mult : ThetaZeroTwoCM := by
  intro d L hd hCM ι W hU hI ha ω₀ hω h1 h2
  obtain ⟨k, hk⟩ : ∃ k, d = 8 * k + 7 := ⟨d / 8, by omega⟩
  have hs2 : ((Real.sqrt d : ℝ) : ℂ) ^ 2 = 8 * (k : ℂ) + 7 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _), hk]
    push_cast
    ring
  refine theta_zero_two_adic_trace L ι W hU hI ha (CM.omegaK d) ω₀ 1 (2 * (k : ℤ) + 2) hCM ?_ ?_ ?_ ?_
    hω h1 h2
  · rw [conj_omegaK]
    simp only [CM.omegaK]
    push_cast
    ring
  · rw [conj_omegaK]
    simp only [CM.omegaK]
    push_cast
    linear_combination (-(((Real.sqrt d : ℝ) : ℂ) ^ 2) / 4) * Complex.I_sq + (1 / 4) * hs2
  · exact odd_one
  · exact ⟨k + 1, by push_cast; ring⟩

end Formalism.L2.Th1.B.LCm
