import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.PlaceIntegralUnramified

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj

section Val

variable {R : Type} [CommRing R] [IsDedekindDomain R] {K : Type} [Field K] [Algebra R K] [IsFractionRing R K]
  {la : HeightOneSpectrum R} {V : Type} {K' : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  [Field K'] [Algebra V K'] [IsFractionRing V K']

theorem nval_nonneg_of_int (e : ℕ) {x : K'} (hx : x ∈ (algebraMap V K').range) : 0 ≤ nval V e x := by
  unfold nval
  split_ifs with h0
  · exact le_top
  · obtain ⟨y, rfl⟩ := hx
    unfold vV
    have hv : valV V ((algebraMap V K') y) ≤ 1 := by
      unfold valV
      exact HeightOneSpectrum.valuation_le_one _ y
    have hne : valV V ((algebraMap V K') y) ≠ 0 := (Valuation.ne_zero_iff _).mpr h0
    have hl : ((valV V) ((algebraMap V K') y)).log ≤ 0 := by
      first
      | exact (WithZero.log_le_log hne one_ne_zero).mpr hv |>.trans_eq WithZero.log_one
      | exact WithZero.log_nonpos hv
      | exact WithZero.log_le_zero_iff.mpr hv
      | simpa using WithZero.log_mono hne hv
    have h1 : (0:ℝ) ≤ ((-(valV V ((algebraMap V K') y)).log : ℤ) : ℝ) / (e : ℝ) :=
      div_nonneg (by exact_mod_cast (by omega : (0:ℤ) ≤ -(valV V ((algebraMap V K') y)).log)) (Nat.cast_nonneg _)
    exact EReal.coe_nonneg.mpr h1

theorem nval_pow_smul {ι : K →+* K'} {e : ℕ} (ho : OverLa la V ι e) {a : K} (ha : a ≠ 0) (n : ℕ) (x : K') :
    nval V e (ι a ^ n * x) = ((((n : ℤ) * vLa la a : ℤ) : ℝ) : EReal) + nval V e x := by
  obtain ⟨he, hv⟩ := ho
  have hιa : ι a ≠ 0 := (map_ne_zero ι).2 ha
  by_cases hx : x = 0
  · subst hx
    unfold nval
    rw [mul_zero, if_pos rfl]
    exact (EReal.coe_add_top _).symm
  · have hprod : ι a ^ n * x ≠ 0 := mul_ne_zero (pow_ne_zero _ hιa) hx
    have hva : valV V (ι a) ≠ 0 := (Valuation.ne_zero_iff _).mpr hιa
    have hvx : valV V x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx
    have hmul : vV V (ι a ^ n * x) = n * vV V (ι a) + vV V x := by
      unfold vV
      rw [map_mul, map_pow]
      first
      | (rw [WithZero.log_mul (pow_ne_zero _ hva) hvx, WithZero.log_pow]; ring)
      | (rw [WithZero.log_mul (pow_ne_zero _ hva) hvx, WithZero.log_pow]; push_cast; ring)
      | (simp [WithZero.log_mul, WithZero.log_pow, hva, hvx]; ring)
    unfold nval
    rw [if_neg hprod, if_neg hx, hmul, hv a, ← EReal.coe_add]
    have he' : (e : ℝ) ≠ 0 := by exact_mod_cast he.ne'
    congr 1
    push_cast
    field_simp

theorem neg_le_nval_of_mem {ι : K →+* K'} {e : ℕ} (ho : OverLa la V ι e) {a b : K} (ha : a ≠ 0) (hb : b ≠ 0)
    (p m : ℕ) (x : K') (hx : ι a ^ p * (ι b ^ m * x) ∈ (algebraMap V K').range) :
    (((-(((vLa la a : ℤ) : ℝ) * (p : ℝ) + ((vLa la b : ℤ) : ℝ) * (m : ℝ))) : ℝ) : EReal) ≤ nval V e x := by
  have h0 := nval_nonneg_of_int e hx
  rw [nval_pow_smul ho ha, nval_pow_smul ho hb] at h0
  by_cases hx0 : x = 0
  · subst hx0
    unfold nval
    simp
  · have hN : nval V e x = ((((vV V x : ℤ) : ℝ) / (e : ℝ) : ℝ) : EReal) := by
      unfold nval
      rw [if_neg hx0]
    rw [hN] at h0 ⊢
    rw [← EReal.coe_add, ← EReal.coe_add, EReal.coe_nonneg] at h0
    rw [EReal.coe_le_coe_iff]
    push_cast at h0 ⊢
    linarith

end Val

def NnIntCSt : Prop :=
  ∀ (D : D7) (T : Top D) (_h : LawsP T) (j : ℕ) (_hj : InR D j) (nab : NabV (T.Q.Xo j) T.Q.c),
    (∃ _ : StarRing (𝓞 D.host.E), IsNab (T.Q.Xo j) T.Q.c nab) → ∀ (w : WeightFamilies.Wt D j) (x : Fin w.n → (T.Q.Dw j).La)
    (P : MvPolynomial (LtN (T.Q.Dw j) w.n) T.Q.c.F), P ∈ harmA T.Q.c (wtA w) w.n →
    ∀ f : T.R j, IsThRule (T.Q.Xo j) T.Q.c nab x P f →
    ∀ (Tc : CDVR) (io : T.Q.c.F →+* Tc.Fr) (yI : IntFr (T.Q.Xo j) T.Q.c Tc io) (e : ℕ)
      (la : HeightOneSpectrum (𝓞 T.Q.c.F)), OverLa la Tc.V io e → yI.IsAlg →
    ∀ (i : Fin 2) (πE : 𝓞 D.host.E) (τ : D.host.E →+* ℂ),
      InPsi T.Q.H τ → πE * T.Q.H.bar πE = (D.host.g i : 𝓞 D.host.E) →
      T.Q.l.Mb ≤ Ideal.span {T.Q.H.bar πE} → ((D.host.g i : 𝓞 T.Q.c.F) ∈ la.asIdeal) → D.host.g i ≠ D.host.q →
      io (embK T.Q.c τ πE) ^ (∑ t, ∑ k, w.aP t k) *
        (io (embK T.Q.c τ (T.Q.H.bar πE)) ^ (∑ t, ∑ k, w.aM t k) * evI yI f) ∈ (algebraMap Tc.V Tc.Fr).range

theorem place_bound_split_of_integral (hI : NnIntCSt) : PlaceBoundSplitPrime := by
  intro D T h j hj nab hadm w x P hP f hf la y i πE τ hτ hπ hM hg hgq
  obtain ⟨Tc, io, e, ho, yI, hy, eta, heta, hq⟩ := y.2
  have hv : vAtV y f = nval Tc.V e (evI yI f) := by
    show y.1.1 f = _
    rw [hq]
    rfl
  rw [hv]
  have hgi : (D.host.g i : 𝓞 D.host.E) ≠ 0 := by
    intro h0
    have h1 := congrArg (algebraMap (𝓞 D.host.E) D.host.E) h0
    simp only [map_natCast, map_zero, Nat.cast_eq_zero] at h1
    exact (D.host.g_prime i).ne_zero h1
  have hπ0 : πE ≠ 0 := by
    rintro rfl
    exact hgi (by rw [← hπ, zero_mul])
  have hπb0 : T.Q.H.bar πE ≠ 0 := by
    intro h0
    exact hgi (by rw [← hπ, h0, mul_zero])
  have hemb : ∀ a : 𝓞 D.host.E, a ≠ 0 → embK T.Q.c τ a ≠ 0 := by
    intro a ha h0
    have h1 := embK_coe T.Q.c τ a
    rw [h0] at h1
    have h2 : τ (a : D.host.E) = 0 := by rw [← h1]; simp
    have h3 : (a : D.host.E) = 0 := (map_eq_zero τ).1 h2
    exact ha (RingOfIntegers.coe_injective (by simpa using h3))
  exact neg_le_nval_of_mem ho (hemb πE hπ0) (hemb _ hπb0) _ _ _
    (hI D T h j hj nab hadm w x P hP f hf Tc io yI e la ho hy i πE τ hτ hπ hM hg hgq)

end ReciprocityTheory.ChartRestriction.G.PullbackSections
