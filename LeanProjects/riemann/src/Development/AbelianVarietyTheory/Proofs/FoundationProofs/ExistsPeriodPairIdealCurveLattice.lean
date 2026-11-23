import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LatticeDeterminedByInvariants

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.CurveLattice

theorem exists_periodPair_of_im_ne_zero {K : Type} [Field K] [NumberField K] (hK : Module.finrank ℚ K = 2)
    (σ : K →+* ℂ) (a : 𝓞 K) (ha : (σ (a : K)).im ≠ 0) {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) :
    ∃ L : PeriodPair, ∀ z, z ∈ L.lattice ↔ ∃ a ∈ I, z = σ (a : K) := by
  have hr : Module.finrank ℤ I = 2 :=
    (Ideal.finrank_eq_finrank (RingOfIntegers.basis K) I hI).trans ((RingOfIntegers.rank K).trans hK)
  let b : Module.Basis (Fin 2) ℤ I := Module.finBasisOfFinrankEq ℤ _ hr
  have hs : ∀ x : I, σ ((x : 𝓞 K) : K) =
      b.repr x 0 * σ ((b 0 : 𝓞 K) : K) + b.repr x 1 * σ ((b 1 : 𝓞 K) : K) := by
    intro x
    have := congrArg (fun x : I => σ ((x : 𝓞 K) : K)) (b.sum_repr x)
    rw [Fin.sum_univ_two] at this
    simpa using this.symm
  have hb0 : σ ((b 0 : 𝓞 K) : K) ≠ 0 := by
    rw [map_ne_zero]
    have : (b 0 : 𝓞 K) ≠ 0 := fun h => b.ne_zero 0 (Subtype.ext h)
    exact_mod_cast this
  have h0 : (σ ((b 1 : 𝓞 K) : K) * starRingEnd ℂ (σ ((b 0 : 𝓞 K) : K))).im ≠ 0 := by
    intro h0
    have e := hs ⟨a * b 0, I.mul_mem_left a (b 0).2⟩
    have e' := congrArg (fun z => (z * starRingEnd ℂ (σ ((b 0 : 𝓞 K) : K))).im) e
    simp only [RingOfIntegers.coe_eq_algebraMap, map_mul] at e' h0 ha hb0
    rw [add_mul, _root_.mul_assoc, _root_.mul_assoc, _root_.mul_assoc, Complex.mul_conj, Complex.add_im,
      Complex.mul_im, Complex.mul_im, Complex.mul_im, h0] at e'
    simp [ha, hb0] at e'
  refine ⟨⟨σ ((b 0 : 𝓞 K) : K), σ ((b 1 : 𝓞 K) : K), ?_⟩, fun z => ?_⟩
  · rw [LinearIndependent.pair_iff]
    intro x y e
    have e1 := congrArg Complex.re e
    have e2 := congrArg Complex.im e
    simp at e1 e2 h0
    constructor
    · refine mul_right_cancel₀ h0 ?_
      linear_combination (σ ((b 1 : 𝓞 K) : K)).im * e1 - (σ ((b 1 : 𝓞 K) : K)).re * e2
    · refine mul_right_cancel₀ h0 ?_
      linear_combination (σ ((b 0 : 𝓞 K) : K)).re * e2 - (σ ((b 0 : 𝓞 K) : K)).im * e1
  · rw [PeriodPair.mem_lattice]
    constructor
    · rintro ⟨m, n, rfl⟩
      exact ⟨_, (m • b 0 + n • b 1).2, by simp⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨_, _, (hs ⟨x, hx⟩).symm⟩

theorem eisG_eq_periodPair_G (Λ : AddSubgroup ℂ) (L : PeriodPair) (h : ∀ z, z ∈ Λ ↔ z ∈ L.lattice) {k : ℕ} (hk : k ≠ 0) :
    eisG Λ k = L.G (2 * k) := by
  have e1 := tsum_subtype {w : ℂ | w ∈ Λ ∧ w ≠ 0} (fun w : ℂ => 1 / w ^ (2 * k))
  have e2 := tsum_subtype (L.lattice : Set ℂ) (fun w : ℂ => (w ^ (2 * k))⁻¹)
  refine e1.trans (Eq.trans (tsum_congr fun w => ?_) e2.symm)
  by_cases hw : w = 0
  · subst hw
    simp [Set.indicator, hk]
  · simp [Set.indicator, hw, h]

theorem discr_ne_zero (Λ : AddSubgroup ℂ) (L : PeriodPair) (h : ∀ z, z ∈ Λ ↔ z ∈ L.lattice) : TaylorLogMetric.discr Λ ≠ 0 := by
  have := g₂_cube_sub_g₃_sq_ne_zero L
  rw [TaylorLogMetric.discr, g2, g3, eisG_eq_periodPair_G Λ L h two_ne_zero, eisG_eq_periodPair_G Λ L h three_ne_zero]
  exact this

theorem mem_lamOf_iff (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ z : ℂ) :
    z ∈ lamOf D cc δ ↔ ∃ c ∈ cc, z = δ * D.host.φ₀ (((c : D.host.K) : D.host.E)) := by
  constructor
  · intro hz
    induction hz using AddSubgroup.closure_induction with
    | mem x hx => exact hx
    | zero => exact ⟨0, cc.zero_mem, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨c, hc, rfl⟩ := hx
      obtain ⟨c', hc', rfl⟩ := hy
      exact ⟨c + c', cc.add_mem hc hc', by simp [mul_add]⟩
    | neg x _ hx =>
      obtain ⟨c, hc, rfl⟩ := hx
      exact ⟨-c, cc.neg_mem hc, by simp⟩
  · intro hz
    exact AddSubgroup.subset_closure hz

theorem exists_periodPair_one (D : D7) {cc : Ideal (𝓞 D.host.K)} (hc : cc ≠ ⊥) :
    ∃ L : PeriodPair, ∀ z : ℂ, z ∈ lamOf D cc 1 ↔ z ∈ L.lattice := by
  have hb : D.host.sqrtMinusD ^ 2 = -(D.host.d : D.host.E) := D.host.sqd_sq
  have hd : 0 < D.host.d := D.host.hyp.2.1.pos
  have hK : Module.finrank ℚ D.host.K = 2 := Formalism.FrobeniusOrbits.SplitK.finrank_K hd hb
  let s : D.host.K := ⟨D.host.sqrtMinusD, IntermediateField.mem_adjoin_simple_self ℚ _⟩
  have hs : s ^ 2 = -(D.host.d : D.host.K) := Subtype.ext (by simpa [s] using hb)
  have hint : IsIntegral ℤ s := by
    refine IsIntegral.of_pow (n := 2) two_pos ?_
    rw [hs]
    exact (isIntegral_natCast _).neg
  let σ : D.host.K →+* ℂ := D.host.φ₀.comp (algebraMap D.host.K D.host.E)
  have him : (σ (((⟨s, hint⟩ : 𝓞 D.host.K) : 𝓞 D.host.K) : D.host.K)).im ≠ 0 := by
    intro h0
    change (σ s).im = 0 at h0
    have e : σ s ^ 2 = -(D.host.d : ℂ) := by rw [← map_pow, hs]; simp
    have e' := congrArg Complex.re e
    simp only [pow_two, Complex.mul_re, h0, Complex.neg_re, Complex.natCast_re] at e'
    have : (0 : ℝ) < D.host.d := by exact_mod_cast hd
    nlinarith [mul_self_nonneg (σ s).re]
  obtain ⟨L, hL⟩ := exists_periodPair_of_im_ne_zero hK σ (⟨s, hint⟩ : 𝓞 D.host.K) him hc
  refine ⟨L, fun z => ?_⟩
  rw [hL, mem_lamOf_iff]
  simp only [one_mul]
  rfl

theorem exists_periodPair_lamOf : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ →
    ∃ L : PeriodPair, ∀ z : ℂ, z ∈ lamOf D cc δ ↔ z ∈ L.lattice := by
  intro D cc δ h
  obtain ⟨L, hL⟩ := exists_periodPair_one D h.1.1
  have hδ : δ ≠ 0 := by
    rintro rfl
    have e : (0 : ℂ) ^ 12 = TaylorLogMetric.discr (lamOf D cc 1) := h.2
    exact discr_ne_zero _ L hL (by rw [← e]; simp)
  have hind : LinearIndependent ℝ ![δ * L.ω₁, δ * L.ω₂] := by
    have h1 := LinearIndependent.pair_iff.1 L.indep
    rw [LinearIndependent.pair_iff]
    intro x y e
    refine h1 x y (mul_left_cancel₀ hδ ?_)
    simp only [Complex.real_smul] at e ⊢
    linear_combination e
  refine ⟨⟨δ * L.ω₁, δ * L.ω₂, hind⟩, fun z => ?_⟩
  rw [mem_lamOf_iff, PeriodPair.mem_lattice]
  constructor
  · rintro ⟨c, hc, rfl⟩
    obtain ⟨m, n, e⟩ := PeriodPair.mem_lattice.1 ((hL _).1 ((mem_lamOf_iff D cc 1 _).2 ⟨c, hc, rfl⟩))
    exact ⟨m, n, by linear_combination δ * e⟩
  · rintro ⟨m, n, rfl⟩
    obtain ⟨c, hc, e⟩ := (mem_lamOf_iff D cc 1 _).1 ((hL _).2 (PeriodPair.mem_lattice.2 ⟨m, n, rfl⟩))
    exact ⟨c, hc, by linear_combination δ * e⟩

end GlobalTheory.CurveLattice
