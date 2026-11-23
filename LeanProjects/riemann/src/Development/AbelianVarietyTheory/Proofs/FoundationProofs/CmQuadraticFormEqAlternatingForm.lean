import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPeriodPairIdealCurveLattice
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LatticeCovolumePosAndSelfDual
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIntegerMapEqHalfOneAddSqrt

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.Vacuum.Parity

theorem zmod_two : ∀ a b c f r s p q : ZMod 2, a * a + b * c = a → a * b + b * f = b → c * a + f * c = c →
    c * b + f * f = f → ¬ (r * a + s * c = 0 ∧ r * b + s * f = 0) →
    ¬ (r - (r * a + s * c) = 0 ∧ s - (r * b + s * f) = 0) →
    (((p * b + q * f) * p - (p * a + q * c) * q) + (q * r - p * s) = 0 ↔ p = 0 ∧ q = 0) := by
  decide

theorem int_two (a b c f r s p q n e : ℤ) (he : e * e = 1) (h1 : a * a + b * c = a - 2 * n) (h2 : a * b + b * f = b)
    (h3 : c * a + f * c = c) (h4 : c * b + f * f = f - 2 * n)
    (h5 : ¬ (Even (r * a + s * c) ∧ Even (r * b + s * f)))
    (h6 : ¬ (Even (r - (r * a + s * c)) ∧ Even (s - (r * b + s * f)))) :
    Even (e * ((p * b + q * f) * p - (p * a + q * c) * q) + e * (q * r - p * s)) ↔ Even p ∧ Even q := by
  have he' : ¬ Even e := by
    intro h
    have : Even (e * e) := h.mul_right e
    rw [he] at this
    exact Int.not_even_one this
  rw [← mul_add, Int.even_mul, or_iff_right he']
  simp only [← ZMod.intCast_eq_zero_iff_even] at h5 h6 ⊢
  have two : (2 : ZMod 2) = 0 := rfl
  have g1 := congrArg (Int.cast : ℤ → ZMod 2) h1
  have g2 := congrArg (Int.cast : ℤ → ZMod 2) h2
  have g3 := congrArg (Int.cast : ℤ → ZMod 2) h3
  have g4 := congrArg (Int.cast : ℤ → ZMod 2) h4
  push_cast at g1 g2 g3 g4 h5 h6 ⊢
  rw [two, zero_mul, sub_zero] at g1 g4
  exact zmod_two _ _ _ _ _ _ _ _ g1 g2 g3 g4 h5 h6

theorem coord_unique (L : PeriodPair) {p q p' q' : ℤ}
    (h : (p : ℂ) * L.ω₁ + q * L.ω₂ = p' * L.ω₁ + q' * L.ω₂) : p = p' ∧ q = q' := by
  have hi := LinearIndependent.pair_iff.1 L.indep ((p : ℝ) - p') ((q : ℝ) - q') (by
    simp only [Complex.real_smul]
    push_cast
    linear_combination h)
  exact ⟨by exact_mod_cast sub_eq_zero.1 hi.1, by exact_mod_cast sub_eq_zero.1 hi.2⟩

theorem half_mem_iff (L : PeriodPair) (p q : ℤ) :
    ((p : ℂ) * L.ω₁ + q * L.ω₂) / 2 ∈ L.lattice ↔ Even p ∧ Even q := by
  rw [PeriodPair.mem_lattice]
  constructor
  · rintro ⟨m, n, h⟩
    have := coord_unique L (p := p) (q := q) (p' := m + m) (q' := n + n) (by
      push_cast
      linear_combination -2 * h)
    exact ⟨⟨m, this.1⟩, ⟨n, this.2⟩⟩
  · rintro ⟨⟨m, rfl⟩, ⟨n, rfl⟩⟩
    exact ⟨m, n, by push_cast; ring⟩

theorem exists_sign (L : PeriodPair) (Λ : AddSubgroup ℂ) (h : ∀ z : ℂ, z ∈ Λ ↔ z ∈ L.lattice) :
    ∃ e : ℤ, e * e = 1 ∧ ∀ p q r s : ℤ,
      gl3FieldFirst Λ ((p : ℂ) * L.ω₁ + q * L.ω₂) ((r : ℂ) * L.ω₁ + s * L.ω₂) = ((e * (q * r - p * s) : ℤ) : ℝ) := by
  have hd := GlobalTheory.PlaneLattice.signedArea_ne_zero L
  have ha := GlobalTheory.PlaneLattice.area_eq L Λ h
  have hpos : 0 < area Λ := ha ▸ abs_pos.2 hd
  obtain ⟨e, he, he2⟩ : ∃ e : ℤ, area Λ = e * ((starRingEnd ℂ) L.ω₁ * L.ω₂).im ∧ e * e = 1 := by
    rcases abs_choice ((starRingEnd ℂ) L.ω₁ * L.ω₂).im with h' | h'
    · exact ⟨1, by rw [ha, h']; simp only [Int.cast_one, one_mul], by simp⟩
    · exact ⟨-1, by rw [ha, h']; simp only [Int.cast_neg, Int.cast_one, neg_mul, one_mul], by simp⟩
  refine ⟨e, he2, fun p q r s => ?_⟩
  have he3 : (e : ℝ) * e = 1 := by exact_mod_cast he2
  rw [gl3FieldFirst, div_eq_iff hpos.ne', he]
  simp
  linear_combination (-((q : ℝ) * r - p * s) * (L.ω₁.re * L.ω₂.im - L.ω₁.im * L.ω₂.re)) * he3

theorem cmQuadraticForm_eq_alternatingForm (D : D7) (Λ : AddSubgroup ℂ) (x : ℂ) : q1 D Λ x = gl3FieldFirst Λ (w0 D * x) x := by
  rw [q1, gl3FieldFirst, mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq, w0]
  simp [← Complex.ofReal_pow]
  ring

theorem cm_generator_sq_quadratic_eq (D : D7) : ∃ n : ℤ, w0 D * w0 D = w0 D - 2 * n := by
  have hd16 : D.host.d % 16 = 7 := D.host.hyp.2.2.2.1
  obtain ⟨n, hn⟩ : ∃ n : ℕ, D.host.d + 1 = 8 * n := ⟨(D.host.d + 1) / 8, by omega⟩
  have hn' : (D.host.d : ℂ) + 1 = 8 * n := by exact_mod_cast hn
  have hs : (Real.sqrt D.host.d : ℂ) ^ 2 = D.host.d := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
    simp
  refine ⟨n, ?_⟩
  rw [w0]
  push_cast
  linear_combination (Real.sqrt D.host.d : ℂ) ^ 2 / 4 * Complex.I_sq - 1 / 4 * hs - 1 / 4 * hn'

theorem lamOf_stable (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (a : 𝓞 D.host.K) :
    ∀ w ∈ lamOf D cc δ, D.host.φ₀ (((a : D.host.K) : D.host.E)) * w ∈ lamOf D cc δ := by
  intro w hw
  induction hw using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨c, hc, rfl⟩ := hx
    exact AddSubgroup.subset_closure ⟨a * c, cc.mul_mem_left a hc, by simp; ring⟩
  | zero => simp
  | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
  | neg x _ hx => rw [mul_neg]; exact neg_mem hx

theorem lamOf_eq_closure (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (hc : Crv D cc δ) :
    ∃ w₁ w₂ : ℂ, LinearIndependent ℝ ![w₁, w₂] ∧ lamOf D cc δ = AddSubgroup.closure {w₁, w₂} := by
  obtain ⟨L, hL⟩ := GlobalTheory.CurveLattice.exists_periodPair_lamOf D cc δ hc
  refine ⟨L.ω₁, L.ω₂, L.indep, AddSubgroup.ext fun z => ?_⟩
  rw [hL, AddSubgroup.mem_closure_pair, PeriodPair.mem_lattice]
  simp only [zsmul_eq_mul]

theorem even_im_hermitian_sub : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ t0, GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0 → t0 ∉ (lamOf D cc δ) ∧ ∀ ω ∈ (lamOf D cc δ), ∃ m k : ℤ, q1 D (lamOf D cc δ) ω = m ∧ gl3FieldFirst (lamOf D cc δ) ω (2 * t0) = k ∧ (Even (m + k) ↔ ω / 2 ∈ (lamOf D cc δ)) := by
  intro D _ cc δ hc t0 ht
  obtain ⟨L, hL⟩ := GlobalTheory.CurveLattice.exists_periodPair_lamOf D cc δ hc
  obtain ⟨α, hα⟩ := GlobalTheory.NormSum.exists_integer_map_eq_w0 D
  have hst : ∀ w ∈ lamOf D cc δ, w0 D * w ∈ lamOf D cc δ := fun w hw =>
    hα ▸ lamOf_stable D cc δ α w hw
  obtain ⟨ht1, ht2, ht3⟩ := ht
  refine ⟨fun h0 => ht2 (hst _ h0), fun ω hω => ?_⟩
  obtain ⟨e, he, hE⟩ := exists_sign L _ hL
  obtain ⟨n, hn⟩ := cm_generator_sq_quadratic_eq D
  obtain ⟨a, b, hab⟩ := PeriodPair.mem_lattice.1 ((hL _).1 (hst _ ((hL _).2 L.ω₁_mem_lattice)))
  obtain ⟨c, f, hcf⟩ := PeriodPair.mem_lattice.1 ((hL _).1 (hst _ ((hL _).2 L.ω₂_mem_lattice)))
  obtain ⟨r, s, hrs⟩ := PeriodPair.mem_lattice.1 ((hL _).1 ht1)
  obtain ⟨p, q, rfl⟩ := PeriodPair.mem_lattice.1 ((hL _).1 hω)
  have h12 := coord_unique L (p := a * a + b * c) (q := a * b + b * f) (p' := a - 2 * n) (q' := b) (by
    push_cast
    linear_combination (a + w0 D - 1) * hab + b * hcf + L.ω₁ * hn)
  have h34 := coord_unique L (p := c * a + f * c) (q := c * b + f * f) (p' := c) (q' := f - 2 * n) (by
    push_cast
    linear_combination c * hab + (f + w0 D - 1) * hcf + L.ω₂ * hn)
  have h5 : ¬ (Even (r * a + s * c) ∧ Even (r * b + s * f)) := by
    rw [← half_mem_iff L, ← hL]
    intro h
    apply ht2
    convert h using 1
    change w0 D * t0 = _
    push_cast
    linear_combination (-1 / 2 * r) * hab - 1 / 2 * s * hcf - 1 / 2 * w0 D * hrs
  have h6 : ¬ (Even (r - (r * a + s * c)) ∧ Even (s - (r * b + s * f))) := by
    rw [← half_mem_iff L, ← hL]
    intro h
    apply ht3
    convert h using 1
    have e1 : (1 - Complex.I * (Real.sqrt D.host.d : ℂ)) / 2 = 1 - w0 D := by rw [w0]; ring
    rw [e1]
    push_cast
    linear_combination (1 / 2 * r) * hab + 1 / 2 * s * hcf - 1 / 2 * (1 - w0 D) * hrs
  have hw : w0 D * ((p : ℂ) * L.ω₁ + q * L.ω₂) =
      ((p * a + q * c : ℤ) : ℂ) * L.ω₁ + ((p * b + q * f : ℤ) : ℂ) * L.ω₂ := by
    push_cast
    linear_combination -p * hab - q * hcf
  refine ⟨e * ((p * b + q * f) * p - (p * a + q * c) * q), e * (q * r - p * s), ?_, ?_, ?_⟩
  · rw [cmQuadraticForm_eq_alternatingForm, hw, hE]
  · rw [← hrs, hE]
  · rw [hL, half_mem_iff]
    exact int_two a b c f r s p q n e he h12.1 h12.2 h34.1 h34.2 h5 h6

end GlobalTheory.Vacuum.Parity
