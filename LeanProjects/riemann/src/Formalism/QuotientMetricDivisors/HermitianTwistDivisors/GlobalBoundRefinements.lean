import Mathlib
import Formalism.QuotientMetricDivisors.ScalarLiftLowerBoundFull
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.TheoremDivIneq
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ConjugateWeightLatticeOfGeneral
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.CommutingTwist
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.AuxStatement14
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ClassSumDualGeOfFamily
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.PlaceSumSquares
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.DescendedNorm
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.SecondComplementParameterBounds
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.WeightedPlaceLogSum

open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder InnerProductSpace

noncomputable section

namespace Formalism.DivisionValues

namespace DivisorInequalityBounds

theorem le_exp_half {x t : ℝ} (h : x ^ 2 ≤ Real.exp t) : x ≤ Real.exp (t / 2) := by
  have he : Real.exp t = Real.exp (t / 2) ^ 2 := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  by_contra hlt
  push_neg at hlt
  nlinarith [Real.exp_pos (t / 2)]

theorem log_exp_half_sq (t : ℝ) : Real.log (Real.exp (t / 2) ^ 2) = t := by
  rw [← Real.exp_nat_mul, Real.log_exp]; push_cast; ring

end DivisorInequalityBounds

namespace DivisorInequalityBounds

theorem eKaux (C0 f N La m L e : ℝ) (hC0 : 1 ≤ C0) (hf : 1 ≤ f) (hN : 1 ≤ N)
    (h : e ≤ C0 * (f * N ^ 2 * La + f * m ^ 3 * N ^ 2 * L)) :
    e ≤ C0 * (f * N ^ 2 * (La + 1) + f * m ^ 3 * N ^ 2 * L) := by
  refine le_trans h (mul_le_mul_of_nonneg_left ?_ (by linarith))
  have h0 : 0 ≤ f * N ^ 2 := by positivity
  have h1 : f * N ^ 2 * (La + 1) = f * N ^ 2 * La + f * N ^ 2 := by ring
  linarith

theorem recAux (X B0 Nc m C0 ce Eb lx2 A : ℝ) (hX : 0 < X) (hNc : 0 ≤ Nc)
    (hC0 : 1 ≤ C0) (hce : C0 ≤ ce) (hl : 0 ≤ lx2) (hEb : Eb ≤ ce * m * (X * B0 + lx2 * Nc)) :
    0 ≤ lx2 * Nc / X ∧ X ≤ ce / C0 * X ∧ Eb ≤ C0 * m * (ce / C0 * X) * (B0 + lx2 * Nc / X) ∧
    (50 * C0 + 10) * (A + m * (B0 + lx2 * Nc / X) * (ce / C0 * X)) =
      (50 * C0 + 10) * A + (50 * C0 + 10) * (ce / C0) * (m * (X * B0 + lx2 * Nc)) := by
  have hC : 0 < C0 := by linarith
  refine ⟨by positivity, ?_, ?_, ?_⟩
  · have : 1 ≤ ce / C0 := by rw [le_div_iff₀ hC]; linarith
    nlinarith
  · have : C0 * m * (ce / C0 * X) * (B0 + lx2 * Nc / X) = ce * m * (X * B0 + lx2 * Nc) := by
      field_simp
    rw [this]; exact hEb
  · field_simp

theorem constant_factor_le_sixty (C0 ce : ℝ) (hC0 : 1 ≤ C0) (hce : 0 ≤ ce) : (50 * C0 + 10) * (ce / C0) ≤ 60 * ce := by
  have hC : 0 < C0 := by linarith
  rw [mul_div_assoc', div_le_iff₀ hC]
  nlinarith [mul_nonneg hce (sub_nonneg.2 hC0)]

theorem divIneqRecord_of (H : TheoremDivIneq) : DivIneqRecord := by
  intro J Pl _ _ TT _ muC mu0 Fo hu hP mlam logT hK aT phν nν fa
    x eps L b a rd La B0 Nc m f k N S tt η w'' b' lam0 C0 ce Lpass Eb e6 eP logOm eK pq w eE δ
  intro s1 s2 s3 s4 s5 s6 s7 s8 z1 z2 z3 z4 z5 l1 l2 l3 l4 hB0 hNc c1 c2 c3 c4 r1 r2 r3 r4 r5 hw
    g1 g2 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 hC0 hce e1 e2 e3 e4 e5 e6' e7
  have hX : 0 < x ^ eps := Real.rpow_pos_of_pos (by linarith only [z1]) _
  have hb : 0 < b := by rw [z4]; exact Real.exp_pos _
  have hB0' : 0 ≤ B0 := by rw [hB0]; positivity
  obtain ⟨t0, t1, t2, t3⟩ := recAux (x ^ eps) B0 Nc m C0 ce Eb ((Real.log x) ^ 2) ((TT.card : ℝ) * a * La) hX hNc hC0 hce (sq_nonneg _) e2
  have hc : 0 < 50 * C0 + 10 := by linarith only [hC0]
  have hC00 : 0 ≤ C0 := by linarith only [hC0]
  have p2' : N ^ 2 * 1 ≤ b := by rw [mul_one]; exact p2
  have key := H J Pl TT muC mu0 Fo hu hP mlam logT hK aT phν nν fa
    x eps L b a rd La B0 ((Real.log x) ^ 2 * Nc / x ^ eps) (ce / C0 * x ^ eps) m f k N S tt η w'' b' 1 (m * lam0) C0
    Lpass Eb e6 eP logOm eK pq w eE δ
    s1 s2 s3 s4 s5 s6 s7 s8 z1 z2 z3 z4 z5 l1 l2 l3 l4 hB0 t0 t1 c1 c2 c3 c4 r1 r2 r3 r4 r5 le_rfl hw
    g1 g2 p1 p2' p3 p4 p5 p6 p7 p8 p9 p10 hC00 e1 t2
    (fun j => eKaux C0 f N La m L (eK j) hC0 c4 r2 (e3 j))
    e4 e5 e6' e7
  rw [t3] at key
  have hfac : (50 * C0 + 10) * (ce / C0) ≤ 60 * ce := constant_factor_le_sixty C0 ce hC0 (by linarith only [hC0, hce])
  have hnn : 0 ≤ m * (x ^ eps * B0 + (Real.log x) ^ 2 * Nc) :=
    mul_nonneg (by linarith only [c3]) (add_nonneg (mul_nonneg hX.le hB0') (mul_nonneg (sq_nonneg _) hNc))
  have hmul := mul_le_mul_of_nonneg_right hfac hnn
  linarith only [key, hmul]

end DivisorInequalityBounds

theorem divisor_inequality_explicit : DivIneqRecord := DivisorInequalityBounds.divIneqRecord_of divisor_inequality

section Rho

open Formalism.DivisionValues.RationalHermitianForm Formalism.DivisionValues.StepBAux Formalism.DivisionValues.ConjugateWeightGram

namespace DivisorInequalityBounds

section LocalW

variable {K : Type} [Field K] [NumberField K] [StarRing K]

end LocalW

end DivisorInequalityBounds

namespace DivisorInequalityBounds

theorem vw_pow' {K : Type} [Field K] [NumberField K] [StarRing K] (w : HeightOneSpectrum (𝓞 K)) (a : K)
    (ha : a ≠ 0) (n : ℕ) : vw w (a ^ n) = n * vw w a := by
  induction n with
  | zero => simpa using (valuation_basic_properties K w).2.2.2.2.1
  | succ n ih =>
    rw [pow_succ, ValuationRepresentative.vw_mul w _ _ (pow_ne_zero n ha) ha, ih]; push_cast; ring

end DivisorInequalityBounds

end Rho

namespace DivisorInequalityBounds

theorem image_eq {K Ω : Type} [Field K] [Field Ω] {n : ℕ} (j : K →+* Ω)
    (𝒯 : Set (Matrix (Fin n) (Fin n) K)) (e : Matrix (Fin n) (Fin n) K) (hee : e * e = e)
    (hcomm : ∀ T ∈ 𝒯, e * T = T * e) (χ : Matrix (Fin n) (Fin n) K → Ω) :
    (simEig j 𝒯 χ).map (e.map j).mulVecLin = simEig j 𝒯 χ ⊓ simEig j {e} (fun _ => 1) := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    refine ⟨?_, ?_⟩
    · intro T hT
      rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, ← Matrix.map_mul, ← hcomm T hT, Matrix.map_mul,
        ← Matrix.mulVec_mulVec, hx T hT, Matrix.mulVec_smul]
    · intro T hT
      rw [Set.mem_singleton_iff.mp hT, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, ← Matrix.map_mul,
        hee, one_smul]
  · rintro x ⟨hx, hx1⟩
    refine ⟨x, hx, ?_⟩
    rw [Matrix.mulVecLin_apply, hx1 e rfl, one_smul]

theorem goodFull {K Ω : Type} [Field K] [Field Ω] {n : ℕ} (j : K →+* Ω)
    (𝒯 : Set (Matrix (Fin n) (Fin n) K)) (e : Matrix (Fin n) (Fin n) K)
    (Z : Submodule K (Fin n → K)) (S : Set (Matrix (Fin n) (Fin n) K → Ω))
    (hZ : extSpan j Z = ⨆ χ ∈ S, (simEig j 𝒯 χ ⊓ simEig j {e} (fun _ => 1))) :
    IsFullEigSum j (𝒯 ∪ {e}) Z := by
  classical
  refine ⟨{χ' | χ' e = 1 ∧ ∃ χ ∈ S, ∀ T ∈ 𝒯, χ' T = χ T}, ?_⟩
  rw [hZ]
  apply le_antisymm
  · refine iSup₂_le fun χ hχ => ?_
    by_cases h : e ∈ 𝒯 ∧ χ e ≠ 1
    · rintro x ⟨hx, hx1⟩
      have h1 := hx e h.1
      rw [hx1 e rfl, one_smul] at h1
      have h2 : (1 - χ e) • x = 0 := by rw [sub_smul, one_smul, ← h1, sub_self]
      rcases smul_eq_zero.mp h2 with h3 | h3
      · exact absurd (sub_eq_zero.mp h3).symm h.2
      · rw [h3]; exact Submodule.zero_mem _
    · have hupd : ∀ T ∈ 𝒯, Function.update χ e 1 T = χ T := by
        intro T hT
        by_cases hTe : T = e
        · subst hTe
          rw [Function.update_self]
          by_contra hne
          exact h ⟨hT, fun h' => hne h'.symm⟩
        · rw [Function.update_of_ne hTe]
      have hmem : Function.update χ e 1 ∈ {χ' : Matrix (Fin n) (Fin n) K → Ω |
          χ' e = 1 ∧ ∃ χ ∈ S, ∀ T ∈ 𝒯, χ' T = χ T} :=
        ⟨Function.update_self _ _ _, χ, hχ, hupd⟩
      refine le_trans ?_ (le_iSup₂ (f := fun χ' _ => simEig j (𝒯 ∪ {e}) χ') _ hmem)
      rintro x ⟨hx, hx1⟩ T hT
      rcases hT with hT | hT
      · rw [hupd T hT]
        exact hx T hT
      · rw [Set.mem_singleton_iff.mp hT, Function.update_self]
        exact hx1 e rfl
  · refine iSup₂_le fun χ' hχ' => ?_
    obtain ⟨h1, χ, hχ, h2⟩ := hχ'
    refine le_trans ?_ (le_iSup₂ (f := fun χ _ => simEig j 𝒯 χ ⊓ simEig j {e} (fun _ => 1)) χ hχ)
    intro x hx
    refine ⟨fun T hT => ?_, fun T hT => ?_⟩
    · rw [← h2 T hT]; exact hx T (Or.inl hT)
    · rw [Set.mem_singleton_iff.mp hT, ← h1]; exact hx e (Or.inr rfl)

end DivisorInequalityBounds

open DivisorInequalityBounds in
theorem good_twisted_lattice : GoodTwist := by
  intro K _ _ _ K0 hK0 v0 hv0 n H hH hpos 𝒯 h0 hc ha e he0 hee hec hea Z Ω _ j S hZ σ
  exact eigen_twist K K0 hK0 v0 hv0 n H hH hpos (𝒯 ∪ {e})
    (by
      rintro T (hT | hT)
      · exact h0 T hT
      · rw [Set.mem_singleton_iff.mp hT]; exact he0)
    (by
      rintro T (hT | hT) T' (hT' | hT')
      · exact hc T hT T' hT'
      · rw [Set.mem_singleton_iff.mp hT']; exact (hec T hT).symm
      · rw [Set.mem_singleton_iff.mp hT]; exact hec T' hT'
      · rw [Set.mem_singleton_iff.mp hT, Set.mem_singleton_iff.mp hT'])
    (by
      rintro T (hT | hT)
      · obtain ⟨T', hT', h⟩ := ha T hT
        exact ⟨T', Or.inl hT', h⟩
      · rw [Set.mem_singleton_iff.mp hT]; exact ⟨e, Or.inr rfl, hea⟩)
    Z Ω j
    (by
      apply goodFull j 𝒯 e Z S
      rw [hZ]
      simp only [image_eq j 𝒯 e hee hec]) σ

namespace DivisorInequalityBounds

end DivisorInequalityBounds

namespace DivisorInequalityBounds

end DivisorInequalityBounds

namespace DivisorInequalityBounds

end DivisorInequalityBounds

namespace DivisorInequalityBounds

end DivisorInequalityBounds

end Formalism.DivisionValues
