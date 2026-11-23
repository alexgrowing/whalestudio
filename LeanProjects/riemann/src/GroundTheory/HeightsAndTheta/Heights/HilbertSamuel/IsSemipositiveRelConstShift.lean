import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsConstantShift
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

noncomputable section

section Shift

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

omit [∀ k, Fintype (ι k)] in

theorem constShift_a (A : HermLine ι) (η : ℝ) : (HermLine.constShift A η).a = A.a := by
  simp [HermLine.constShift, HermLine.tensor, HermLine.ofWeight]

omit [∀ k, Fintype (ι k)] in
theorem constShift_h (A : HermLine ι) (η : ℝ) (z : (Σ k, ι k) → ℂ) :
    (HermLine.constShift A η).h z = A.h z * Real.exp (-η) := rfl

theorem isSmoothHerm_constShift {A : HermLine ι} (hA : IsSmoothHerm A) (η : ℝ) :
    IsSmoothHerm (HermLine.constShift A η) := by
  have : (HermLine.constShift A η).h = fun z => A.h z * Real.exp (-η) := rfl
  unfold IsSmoothHerm at hA ⊢
  rw [this]
  exact hA.mul contDiffOn_const

omit [∀ k, Fintype (ι k)] in
theorem isConjInvariantH_constShift {A : HermLine ι} (hA : IsConjInvariantH A) (η : ℝ) :
    IsConjInvariantH (HermLine.constShift A η) := by
  intro z
  rw [constShift_h, constShift_h, hA z]

theorem leviForm_constShift (A : HermLine ι) (η : ℝ) {z : (Σ k, ι k) → ℂ}
    (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) (w : (Σ k, ι k) → ℂ) :
    leviForm (fun x => Real.log ((HermLine.constShift A η).h x)) z w =
      leviForm (fun x => Real.log (A.h x)) z w := by
  have hU : IsOpen {x : (Σ k, ι k) → ℂ | ∀ k, ∃ i, x ⟨k, i⟩ ≠ 0} := by
    have : {x : (Σ k, ι k) → ℂ | ∀ k, ∃ i, x ⟨k, i⟩ ≠ 0} = ⋂ k, ⋃ i, {x | x ⟨k, i⟩ ≠ 0} := by
      ext x
      simp
    rw [this]
    exact isOpen_iInter_of_finite fun k => isOpen_iUnion fun i =>
      isOpen_ne_fun (continuous_apply _) continuous_const
  have h1 : (fun x => Real.log ((HermLine.constShift A η).h x)) =ᶠ[𝓝 z]
      fun x => Real.log (A.h x) + (-η) := by
    filter_upwards [hU.mem_nhds hz] with x hx
    rw [constShift_h, Real.log_mul (A.pos x hx).ne' (Real.exp_pos _).ne', Real.log_exp]
  have h2 : fderiv ℝ (fun x => Real.log ((HermLine.constShift A η).h x)) =ᶠ[𝓝 z]
      fderiv ℝ (fun x => Real.log (A.h x)) := by
    filter_upwards [h1.eventuallyEq_nhds] with x hx
    rw [hx.fderiv_eq, fderiv_add_const]
  unfold leviForm
  rw [h2.fderiv_eq]

theorem isSemipositiveRel_constShift {P0 P : Ideal (MRing ι)} {A : HermLine ι}
    (hA : IsSemipositiveRel P0 P A) (η : ℝ) : IsSemipositiveRel P0 P (HermLine.constShift A η) := by
  refine ⟨isSmoothHerm_constShift hA.1 η, fun z hz w hw => ?_⟩
  rw [leviForm_constShift A η hz.1 w]
  exact hA.2 z hz w hw

end Shift

theorem exists_small_section_of_arithmeticVolume_pos {Ω : Type} [Field Ω] {Pr : ℕ → Ω → Prop} {La : ℕ → AddSubgroup Ω}
    {D : ℕ} (h : 0 < arVolP Pr La 1 D) : ∃ n, 1 ≤ n ∧ ∃ s ∈ La n, s ≠ 0 ∧ Pr n s := by
  by_contra hne
  push Not at hne
  have hzero : ∀ k, 1 ≤ k → smallSectionCount Pr La k = 0 := by
    intro k hk
    have hsub : Subsingleton {s : La k // Pr k (s : Ω)} := by
      constructor
      rintro ⟨a, ha⟩ ⟨b, hb⟩
      have ha0 : (a : Ω) = 0 := by
        by_contra h0
        exact hne k hk a a.2 h0 ha
      have hb0 : (b : Ω) = 0 := by
        by_contra h0
        exact hne k hk b b.2 h0 hb
      exact Subtype.ext (Subtype.ext (ha0.trans hb0.symm))
    have := hsub
    have hc : Nat.card {s : La k // Pr k (s : Ω)} ≤ 1 := Finite.card_le_one_iff_subsingleton.mpr hsub
    unfold smallSectionCount
    interval_cases Nat.card {s : La k // Pr k (s : Ω)} <;> simp
  have : arVolP Pr La 1 D = 0 := by
    unfold arVolP
    refine (limsup_congr ?_).trans (limsup_const 0)
    filter_upwards [eventually_ge_atTop 1] with k hk
    rw [one_mul, hzero k hk, zero_div]
  linarith

theorem G4.proof (hG6 : ArithmeticVolumeBig.Statement) (hCS : ConstantShift.Statement) : G4.Statement := by
  intro K _ ι _ Ω _ _ y D M P0 II hD hII har hb hM hpos
  obtain ⟨η, hη0, hηlt⟩ : ∃ η : ℝ, 0 < η ∧ ((D : ℝ) + 1) * η * geomDeg (mCoordIdeal y) M D <
      II K ι (mCoordIdeal y) (D + 1) (fun _ => M) := by
    set T := II K ι (mCoordIdeal y) (D + 1) (fun _ => M)
    set g := geomDeg (mCoordIdeal y) M D
    have hden : 0 < 2 * (((D : ℝ) + 1) * |g| + 1) := by positivity
    refine ⟨T / (2 * (((D : ℝ) + 1) * |g| + 1)), div_pos hpos hden, ?_⟩
    set η := T / (2 * (((D : ℝ) + 1) * |g| + 1))
    have hη0 : 0 < η := div_pos hpos hden
    have he : η * (2 * (((D : ℝ) + 1) * |g| + 1)) = T := div_mul_cancel₀ T hden.ne'
    have h1 : ((D : ℝ) + 1) * η * g ≤ ((D : ℝ) + 1) * η * |g| :=
      mul_le_mul_of_nonneg_left (le_abs_self g) (by positivity)
    have h3 : 0 ≤ ((D : ℝ) + 1) * η * |g| := by positivity
    nlinarith
  have hshift := hCS K ι (II K ι) (mCoordIdeal y) D M η (hII K ι) har hM.semipos.1
  have hpos' : 0 < II K ι (mCoordIdeal y) (D + 1) (fun _ => HermLine.constShift M η) := by
    rw [hshift]
    linarith
  have hvol := hG6 K ι Ω y D (HermLine.constShift M η) P0 II hD hII har hb hM.normalForm_baseLattice_le_dualSpan_sup_line
    (isSemipositiveRel_constShift hM.semipos η) (by rw [constShift_a]; exact hM.nef)
    (isConjInvariantH_constShift hM.conjInv η)
  obtain ⟨n, hn, s, hs, hs0, hsmall⟩ := exists_small_section_of_arithmeticVolume_pos (hpos'.trans_le hvol)
  have hn' : (0 : ℝ) < n * η := mul_pos (by exact_mod_cast hn) hη0
  refine ⟨n, s, hn, by rwa [constShift_a] at hs, hs0, Real.exp (-(n * η)), ?_, ?_⟩
  · rw [Real.exp_lt_one_iff]
    linarith
  · intro dg dh g h z hg hh hdeg heq hz
    have hle := hsmall dg dh g h z hg hh (by rw [constShift_a]; exact hdeg) heq hz
    have e : Real.exp (-(n * η)) = Real.exp (-η) ^ n := by
      rw [← Real.exp_nat_mul]
      ring_nf
    refine hle.trans (le_of_eq ?_)
    rw [constShift_h, mul_pow, e]
    ring

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
