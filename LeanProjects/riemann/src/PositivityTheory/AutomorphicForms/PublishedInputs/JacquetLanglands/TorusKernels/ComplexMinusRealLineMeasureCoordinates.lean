import Mathlib

noncomputable section

open MeasureTheory Matrix
open scoped ENNReal NNReal ComplexConjugate

namespace UpperTheory.Esk

def P : Type := {z : ℂ // z.im ≠ 0}

instance : TopologicalSpace P := inferInstanceAs (TopologicalSpace {z : ℂ // z.im ≠ 0})
instance : MeasurableSpace P := inferInstanceAs (MeasurableSpace {z : ℂ // z.im ≠ 0})
instance : BorelSpace P := inferInstanceAs (BorelSpace {z : ℂ // z.im ≠ 0})
instance : SecondCountableTopology P := inferInstanceAs (SecondCountableTopology {z : ℂ // z.im ≠ 0})
instance : T2Space P := inferInstanceAs (T2Space {z : ℂ // z.im ≠ 0})

instance : MeasureSpace P where
  volume := (Measure.comap (Subtype.val : {z : ℂ // z.im ≠ 0} → ℂ) volume).withDensity fun z => ENNReal.ofReal (1 / z.1.im ^ 2)

def iP : P := ⟨Complex.I, by simp⟩

def den (g : GL (Fin 2) ℝ) (z : ℂ) : ℂ := (g 1 0 : ℝ) * z + (g 1 1 : ℝ)

def num (g : GL (Fin 2) ℝ) (z : ℂ) : ℂ := (g 0 0 : ℝ) * z + (g 0 1 : ℝ)

theorem det_eq (g : GL (Fin 2) ℝ) : g.val.det = g 0 0 * g 1 1 - g 0 1 * g 1 0 := by
  exact Matrix.det_fin_two g.val

theorem den_ne (g : GL (Fin 2) ℝ) {z : ℂ} (hz : z.im ≠ 0) : den g z ≠ 0 := by
  intro h
  have h1 : (g 1 0 : ℝ) * z.im = 0 := by
    have him := congrArg Complex.im h
    simpa [den] using him
  have hc : (g 1 0 : ℝ) = 0 := by
    rcases mul_eq_zero.mp h1 with h2 | h2
    · exact h2
    · exact absurd h2 hz
  have hd : (g 1 1 : ℝ) = 0 := by
    have hre := congrArg Complex.re h
    simpa [den, hc] using hre
  apply g.det_ne_zero
  rw [det_eq, hc, hd]
  ring

theorem im_div (g : GL (Fin 2) ℝ) (z : ℂ) : (num g z / den g z).im = g.val.det * z.im / Complex.normSq (den g z) := by
  rw [Complex.div_im, det_eq]
  simp only [num, den, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im]
  ring

instance : MulAction (GL (Fin 2) ℝ) P where
  smul g z := ⟨num g z.1 / den g z.1, by
    rw [im_div]
    exact div_ne_zero (mul_ne_zero g.det_ne_zero z.2) (by simpa using den_ne g z.2)⟩
  one_smul z := Subtype.ext (by
    change num 1 z.1 / den 1 z.1 = z.1
    simp [num, den])
  mul_smul g h z := Subtype.ext (by
    change num (g * h) z.1 / den (g * h) z.1 = num g (num h z.1 / den h z.1) / den g (num h z.1 / den h z.1)
    have h0 := den_ne h z.2
    have e1 : num g (num h z.1 / den h z.1) = num (g * h) z.1 / den h z.1 := by
      rw [eq_div_iff h0, num, add_mul, mul_assoc, div_mul_cancel₀ _ h0]
      simp [num, den, Matrix.mul_apply, Fin.sum_univ_two]; ring
    have e2 : den g (num h z.1 / den h z.1) = den (g * h) z.1 / den h z.1 := by
      rw [eq_div_iff h0, den, add_mul, mul_assoc, div_mul_cancel₀ _ h0]
      simp [num, den, Matrix.mul_apply, Fin.sum_univ_two]; ring
    rw [e1, e2, div_div_div_cancel_right₀ h0])

theorem coe_smul (g : GL (Fin 2) ℝ) (z : P) : (g • z).1 = num g z.1 / den g z.1 := rfl

def j1 (k : ℕ) (g : GL (Fin 2) ℝ) (z : P) : ℂ := den g z.1 ^ k * ((|g.val.det| ^ (-(k : ℝ) / 2) : ℝ) : ℂ)

def q1 (k : ℕ) (z w : P) : ℂ :=
  if 0 < z.1.im * w.1.im then ((k : ℂ) - 1) / (4 * Real.pi) * ((w.1 - conj w.1) / (z.1 - conj w.1)) ^ k else 0

def kap (z w : P) : ℝ := if 0 < z.1.im * w.1.im then 4 * (z.1.im * w.1.im) / ‖z.1 - conj w.1‖ ^ 2 else 0

open Classical in

def ext1 (f : P → ℂ) (t : ℂ) : ℂ := if h : t.im ≠ 0 then f ⟨t, h⟩ else 0

def Hol1 (f : P → ℂ) : Prop := DifferentiableOn ℂ (ext1 f) {t | t.im ≠ 0}

def ch {R : Type*} [CommRing R] (t d : R) : ℕ → R
  | 0 => 0
  | 1 => 1
  | (n + 2) => t * ch t d (n + 1) - d * ch t d n

def pt (x y : ℝ) (hy : y ≠ 0) : P := ⟨y * (x + Complex.I), by simpa using hy⟩

def B1a : Prop := SigmaFinite (volume : Measure P) ∧ (volume : Measure P).IsOpenPosMeasure ∧
  ∀ g : GL (Fin 2) ℝ, Continuous (fun z : P => g • z) ∧ MeasurePreserving (fun z : P => g • z) volume volume

def B1b : Prop :=
  (∀ k g h z, j1 k (g * h) z = j1 k g (h • z) * j1 k h z) ∧ (∀ k g z, j1 k g z ≠ 0) ∧
  (∀ (k : ℕ) (g : GL (Fin 2) ℝ) (z w : P), q1 k (g • z) (g • w) * j1 k g w = j1 k g z * q1 k z w) ∧
  (∀ (g : GL (Fin 2) ℝ) (z w : P), kap (g • z) (g • w) = kap z w) ∧
  (∀ (k : ℕ) (g : GL (Fin 2) ℝ) (z : P), ‖j1 k g z‖ * |(g • z).1.im| ^ ((k : ℝ) / 2) = |z.1.im| ^ ((k : ℝ) / 2)) ∧
  (∀ (k : ℕ) (z w : P), 1 ≤ k → ‖q1 k z w‖ * |z.1.im| ^ ((k : ℝ) / 2) =
    ((k : ℝ) - 1) / (4 * Real.pi) * kap z w ^ ((k : ℝ) / 2) * |w.1.im| ^ ((k : ℝ) / 2)) ∧
  (∀ k g, Continuous (j1 k g)) ∧ (∀ k, Continuous fun p : P × P => q1 k p.1 p.2) ∧ (∀ k w, Hol1 fun z => q1 k z w)

def B1c : Prop :=
  (∀ z w, 0 ≤ kap z w ∧ kap z w ≤ 1 ∧ kap z w = kap w z) ∧ (∀ z, kap z z = 1) ∧ (∀ z w u, kap z w * kap w u ≤ 4 * kap z u) ∧
  (∀ z w : P, kap z w * |w.1.im| ≤ 4 * |z.1.im|) ∧ Continuous (fun p : P × P => kap p.1 p.2) ∧
  ∀ z : P, ∃ g : GL (Fin 2) ℝ, g 1 0 = 0 ∧ g 1 1 = 1 ∧ g • iP = z

def B2 : Prop :=
  ∀ h : P → ℂ, (∀ z : P, z.1.im < 0 → h z = 0) → Integrable h →
    IntegrableOn (fun p : ℝ × ℝ => ((4 * p.1 / (1 - p.1 ^ 2) ^ 2 : ℝ) : ℂ) *
      ext1 h (Complex.I * (1 + circleMap 0 p.1 p.2) / (1 - circleMap 0 p.1 p.2))) (Set.Ioo 0 1 ×ˢ Set.Ioo (-Real.pi) Real.pi) ∧
    ∫ z, h z = ∫ p in Set.Ioo (0 : ℝ) 1 ×ˢ Set.Ioo (-Real.pi) Real.pi, ((4 * p.1 / (1 - p.1 ^ 2) ^ 2 : ℝ) : ℂ) *
      ext1 h (Complex.I * (1 + circleMap 0 p.1 p.2) / (1 - circleMap 0 p.1 p.2))

def B6 : Prop :=
  ∀ k : ℕ, 4 ≤ k → ∃ C : ℝ≥0, ∀ z : P, ∫⁻ w, ENNReal.ofReal (kap z w ^ ((k : ℝ) / 2)) ≤ C ∧
    ∫⁻ w, ENNReal.ofReal (kap z w ^ ((k : ℝ) / 2) * (|z.1.im| / |w.1.im|) ^ ((1 : ℝ) / 2)) ≤ C

def B3 : Prop :=
  ∀ k : ℕ, 4 ≤ k → ∀ f : P → ℂ, Hol1 f → (∃ C, ∀ z, ‖f z‖ * |z.1.im| ^ ((k : ℝ) / 2) ≤ C) → ∀ z,
    Integrable (fun w => q1 k z w * f w) ∧ ∫ w, q1 k z w * f w = f z

def B4 : Prop :=
  ∀ k : ℕ, 4 ≤ k → ∀ g : GL (Fin 2) ℝ, g.val.trace ^ 2 < 4 * g.val.det →
    Integrable (fun z : P => q1 k z (g • z) * j1 k g z) ∧
    ∫ z : P, q1 k z (g • z) * j1 k g z = -((ch g.val.trace g.val.det (k - 1) * g.val.det ^ (1 - (k : ℝ) / 2) : ℝ) : ℂ)

def UpperHalfPlaneMeasureCoordinates : Prop :=
  MeasurePreserving (fun p : ℝ × {y : ℝ // y ≠ 0} => pt p.1 p.2.1 p.2.2)
    ((volume : Measure ℝ).prod ((Measure.comap Subtype.val volume).withDensity fun y => ENNReal.ofReal (1 / |y.1|))) volume ∧
  Function.Bijective (fun p : ℝ × {y : ℝ // y ≠ 0} => pt p.1 p.2.1 p.2.2) ∧
  Continuous (fun p : ℝ × {y : ℝ // y ≠ 0} => pt p.1 p.2.1 p.2.2)

def DiagonalIntegrandVanishes : Prop :=
  ∀ k : ℕ, 4 ≤ k → ∀ g : GL (Fin 2) ℝ, g 0 1 = 0 → g 1 0 = 0 → g 0 0 ≠ g 1 1 → ∃ φ : ℝ → ℂ, Continuous φ ∧
    (∀ x y hy, q1 k (pt x y hy) (g • pt x y hy) * j1 k g (pt x y hy) = φ x) ∧ Integrable φ ∧
    Integrable (fun x => (Real.log (1 + x ^ 2) : ℂ) * φ x) ∧ ∫ x, φ x = 0 ∧ (φ = 0 ∨ ∀ x, φ x ≠ 0)

structure IsCut (G : Type) [Group G] {Y : Type} [MeasurableSpace Y] [MulAction G Y] (b : Y → ℝ) : Prop where
  meas : Measurable b
  nonneg : ∀ y, 0 ≤ b y
  sum : ∀ y, HasSum (fun g : G => b (g • y)) 1

def Pres (G : Type) [Group G] {Y : Type} [MeasurableSpace Y] [MulAction G Y] (μ : Measure Y) : Prop :=
  ∀ g : G, MeasurePreserving (fun y : Y => g • y) μ μ

def C1 : Prop :=
  ∀ (G Y : Type) [Group G] [Countable G] [MeasurableSpace Y] [MulAction G Y] (μ : Measure Y), Pres G μ →
    ∀ b b' : Y → ℝ, IsCut G b → IsCut G b' →
    (∀ u : Y → ℝ≥0∞, Measurable u → (∀ (g : G) y, u (g • y) = u y) →
      ∫⁻ y, ENNReal.ofReal (b y) * u y ∂μ = ∫⁻ y, ENNReal.ofReal (b' y) * u y ∂μ) ∧
    ∀ u : Y → ℂ, Measurable u → (∀ (g : G) y, u (g • y) = u y) → Integrable (fun y => b y • u y) μ →
      Integrable (fun y => b' y • u y) μ ∧ ∫ y, b y • u y ∂μ = ∫ y, b' y • u y ∂μ

def C2 : Prop :=
  ∀ (G Y : Type) [Group G] [Countable G] [MeasurableSpace Y] [MulAction G Y],
    ((∀ g : G, Measurable fun y : Y => g • y) → ∀ u : Y → ℝ, Measurable u → (∀ y, 0 ≤ u y) → (∀ y, ∃ g : G, 0 < u (g • y)) →
      (∀ y, Summable fun g : G => u (g • y)) → ∃ b : Y → ℝ, IsCut G b) ∧
    ∀ μ : Measure Y, Pres G μ → ∀ b : Y → ℝ, IsCut G b → ∀ S : Set Y, MeasurableSet S → (∀ y : Y, ∃ g : G, g • y ∈ S) →
      ∫⁻ y, ENNReal.ofReal (b y) ∂μ ≤ μ S

def C3 : Prop :=
  ∀ (G Y : Type) [Group G] [Countable G] [MeasurableSpace Y] [MulAction G Y] (μ : Measure Y), Pres G μ →
    ∀ b : Y → ℝ, IsCut G b → ∀ f : Y → ℂ, Measurable f → Integrable f μ →
      Integrable (fun y => b y • ∑' g : G, f (g • y)) μ ∧ ∫ y, b y • ∑' g : G, f (g • y) ∂μ = ∫ y, f y ∂μ

def C4 : Prop :=
  ∀ (G Ω X : Type) [Group G] [Countable G] [Countable Ω] [MeasurableSpace Ω] [DiscreteMeasurableSpace Ω] [MeasurableSpace X]
    [MulAction G Ω] [MulAction G X] (μ : Measure X) [SigmaFinite μ], Pres G μ → ∀ b : Ω × X → ℝ, IsCut G b →
    ∀ u : Ω × X → ℂ, Measurable u → (∀ (g : G) y, u (g • y) = u y) → Integrable (fun y => b y • u y) (Measure.count.prod μ) →
    ∀ R : Set Ω, (∀ ω, ∃! r, r ∈ R ∧ r ∈ MulAction.orbit G ω) →
    ∀ β : Ω → X → ℝ, (∀ r ∈ R, IsCut (MulAction.stabilizer G r) (β r)) →
      (∀ r ∈ R, Integrable (fun x => β r x • u (r, x)) μ) ∧
      HasSum (fun r : R => ∫ x, β r x • u (r, x) ∂μ) (∫ y, b y • u y ∂(Measure.count.prod μ))

def LinTr : Prop :=
  ∀ (A Y : Type) [MeasurableSpace Y] (ν : Measure Y) [IsFiniteMeasure ν] (V : Submodule ℂ (A → ℂ)) [FiniteDimensional ℂ V]
    (T : V →ₗ[ℂ] V) (K : Y → V) (ev : Y → A) (n : Y → ℝ), Measurable n → (∀ y, 0 < n y) → (∀ a, Measurable fun y => (K y).1 a) →
    (∀ f : V, Measurable fun y => f.1 (ev y)) → (∀ a, ∃ C, ∀ y, ‖(K y).1 a‖ ≤ C * n y) → (∀ f : V, ∃ C, ∀ y, ‖f.1 (ev y)‖ * n y ≤ C) →
    (∀ (f : V) a, ∫ y, (K y).1 a * f.1 (ev y) ∂ν = f.1 a) →
    Measurable (fun y => (T (K y)).1 (ev y)) ∧ (∃ C, ∀ y, ‖(T (K y)).1 (ev y)‖ ≤ C) ∧
      LinearMap.trace ℂ V T = ∫ y, (T (K y)).1 (ev y) ∂ν

def Osg : Prop :=
  ∀ (I : Type) [Fintype I] [DecidableEq I] (U : Set (I → ℂ)), IsOpen U → ∀ f : (I → ℂ) → ℂ, ContinuousOn f U →
    (∀ z ∈ U, ∀ v, DifferentiableAt ℂ (fun t => f (Function.update z v t)) (z v)) → AnalyticOnNhd ℂ f U

def Fin0 : Prop :=
  ∀ (ν : Valuation ℂ ℝ≥0) (l : ℕ), l.Prime → ν l < 1 → ∀ (J V V' : Type) [DecidableEq J] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V'] (T : J → Module.End ℂ V) (T' : J → Module.End ℂ V'),
    (∀ i j, T i * T j = T j * T i) → (∀ i j, T' i * T' j = T' j * T' i) → ∀ (L : Finset J) (ε ρ : ℝ≥0), ρ < 1 →
    (∀ d : ℕ, 1 ≤ d → d ≤ Module.finrank ℂ V → ε < ν d) →
    (∀ (W : List J) (r : ℕ), 1 ≤ r → (∀ j ∈ L, r ≤ W.count j) →
      ν (LinearMap.trace ℂ V (W.map T).prod) ≤ 1 ∧ ν (LinearMap.trace ℂ V' (W.map T').prod) ≤ 1 ∧
      ν (LinearMap.trace ℂ V (W.map T).prod - LinearMap.trace ℂ V' (W.map T').prod) ≤ max ε (ρ ^ r)) →
    ∀ (f : V) (s : J → ℂ), f ≠ 0 → (∀ j, T j f = s j • f) → (∀ j ∈ L, ν (s j) = 1) →
    ∃ (f' : V') (s' : J → ℂ), f' ≠ 0 ∧ (∀ j, T' j f' = s' j • f') ∧ ∀ j, ν (s' j - s j) < 1

def Sys : Prop :=
  ∀ (J V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (T : J → Module.End ℂ V), (∀ i j, T i * T j = T j * T i) →
    ∃ (S : Finset (J → ℂ)) (m : (J → ℂ) → ℕ), (∀ s, s ∈ S ↔ ∃ f : V, f ≠ 0 ∧ ∀ j, T j f = s j • f) ∧ (∀ s ∈ S, 1 ≤ m s) ∧
      ∑ s ∈ S, m s = Module.finrank ℂ V ∧ ∀ W : List J, LinearMap.trace ℂ V (W.map T).prod = ∑ s ∈ S, (m s : ℂ) * (W.map s).prod

end UpperTheory.Esk
