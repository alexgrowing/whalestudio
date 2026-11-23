import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.IntAllFree

noncomputable section

namespace GlobalTheory.IntegralFrameCheck

open Formalism.L2.Pj NumberField IsDedekindDomain
open scoped WithZero

section Dvr

variable {V K' : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K'] [Algebra V K']
  [IsFractionRing V K']

theorem vV_algebraMap_nonneg (a : V) : 0 ≤ vV V (algebraMap V K' a) := by
  by_cases ha : algebraMap V K' a = 0
  · rw [ha]; simp [vV]
  · have hv : valV V (algebraMap V K' a) ≤ 1 :=
      (IsDiscreteValuationRing.maximalIdeal V).valuation_le_one a
    have := (WithZero.log_le_log (valV_ne_zero (V := V) ha) one_ne_zero).2 hv
    simp only [WithZero.log_one] at this
    simp only [vV]; omega

theorem vV_one : vV V (1 : K') = 0 := by simp [vV]

theorem vV_pow {x : K'} (hx : x ≠ 0) (n : ℕ) : vV V (x ^ n) = n * vV V x := by
  induction n with
  | zero => simp [vV]
  | succ n ih => rw [pow_succ, vV_mul (pow_ne_zero n hx) hx, ih]; push_cast; ring

variable {V' K'' : Type} [CommRing V'] [IsDomain V'] [IsDiscreteValuationRing V'] [Field K''] [Algebra V' K'']
  [IsFractionRing V' K'']

theorem vV_map_unit (i : K' →+* K'') (hi : ∀ a : V, i (algebraMap V K' a) ∈ Set.range (algebraMap V' K''))
    (u : Vˣ) : vV V' (i (algebraMap V K' u)) = 0 := by
  have hne : ∀ w : Vˣ, i (algebraMap V K' w) ≠ 0 := fun w =>
    ((w.isUnit.map (algebraMap V K')).map i).ne_zero
  have h0 : ∀ w : Vˣ, 0 ≤ vV V' (i (algebraMap V K' w)) := fun w => by
    obtain ⟨b, hb⟩ := hi w
    rw [← hb]; exact vV_algebraMap_nonneg b
  have h1 := vV_mul (V := V') (hne u) (hne u⁻¹)
  rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one, vV_one] at h1
  have := h0 u
  have := h0 u⁻¹
  omega

theorem exists_vV_map (i : K' →+* K'') (hi : ∀ a : V, i (algebraMap V K' a) ∈ Set.range (algebraMap V' K'')) :
    ∃ r : ℕ, ∀ x, vV V' (i x) = (r : ℤ) * vV V x := by
  obtain ⟨p, hp⟩ := IsDiscreteValuationRing.exists_irreducible V
  have hp0 : algebraMap V K' p ≠ 0 := by
    simpa using hp.ne_zero
  have hr : 0 ≤ vV V' (i (algebraMap V K' p)) := by
    obtain ⟨b, hb⟩ := hi p
    rw [← hb]; exact vV_algebraMap_nonneg b
  have hp1 : vV V (algebraMap V K' p) = 1 := by
    have h : valV V (algebraMap V K' p) = WithZero.exp (-1 : ℤ) := by
      unfold valV
      rw [HeightOneSpectrum.valuation_of_algebraMap]
      refine HeightOneSpectrum.intValuation_singleton _ hp.ne_zero ?_
      exact hp.maximalIdeal_eq
    simp [vV, h]
  refine ⟨(vV V' (i (algebraMap V K' p))).toNat, ?_⟩
  rw [Int.toNat_of_nonneg hr]
  have key : ∀ a : V, a ≠ 0 → vV V' (i (algebraMap V K' a)) =
      vV V' (i (algebraMap V K' p)) * vV V (algebraMap V K' a) := by
    intro a ha
    obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hp
    have hu : algebraMap V K' u ≠ 0 := (u.isUnit.map (algebraMap V K')).ne_zero
    have hu0 : vV V (algebraMap V K' u) = 0 :=
      vV_map_unit (V' := V) (RingHom.id K') (fun a => ⟨a, rfl⟩) u
    rw [map_mul, map_pow, map_mul, map_pow,
      vV_mul ((map_ne_zero i).2 hu) (pow_ne_zero n ((map_ne_zero i).2 hp0)),
      vV_mul hu (pow_ne_zero n hp0), vV_pow ((map_ne_zero i).2 hp0), vV_pow hp0, vV_map_unit i hi u, hu0, hp1]
    ring
  intro x
  by_cases hx : x = 0
  · subst hx; simp [vV]
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := V) x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hb' : algebraMap V K' b ≠ 0 := by simpa using hb0
  have ha0 : a ≠ 0 := by rintro rfl; simp at hx
  have e : algebraMap V K' a / algebraMap V K' b * algebraMap V K' b = algebraMap V K' a :=
    div_mul_cancel₀ _ hb'
  have h1 := vV_mul (V := V) hx hb'
  have h2 := vV_mul (V := V') ((map_ne_zero i).2 hx) ((map_ne_zero i).2 hb')
  rw [← map_mul, e, key a ha0, key b hb0] at h2
  rw [e] at h1
  rw [h1] at h2
  linarith

end Dvr

theorem nval_map_of_overLa {K : Type} [Field K] [NumberField K] {la : HeightOneSpectrum (𝓞 K)}
    {T T' : CDVR} {io : K →+* T.Fr} {io' : K →+* T'.Fr} {e e' : ℕ}
    (ho : OverLa la T.V io e) (ho' : OverLa la T'.V io' e') (i : T.Fr →+* T'.Fr)
    (hc : ∀ a, i (io a) = io' a)
    (hi : ∀ a : T.V, i (algebraMap T.V T.Fr a) ∈ Set.range (algebraMap T'.V T'.Fr)) :
    ∃ r : ℕ, 0 < r ∧ e' = r * e ∧ (∀ x, vV T'.V (i x) = (r : ℤ) * vV T.V x) ∧
      ∀ x, nval T'.V e' (i x) = nval T.V e x := by
  obtain ⟨r, hr⟩ := exists_vV_map i hi
  obtain ⟨a, ha⟩ := la.valuation_exists_uniformizer K
  have h1 : vLa la a = 1 := by simp [vLa, ha]
  have h2 := hr (io a)
  rw [hc, ho'.2, ho.2, h1] at h2
  have he : e' = r * e := by
    have : (e' : ℤ) = (r * e : ℕ) := by push_cast; linarith
    exact_mod_cast this
  have hr0 : 0 < r := by
    rcases Nat.eq_zero_or_pos r with h | h
    · have := ho'.1; rw [he, h] at this; simp at this
    · exact h
  exact ⟨r, hr0, he, hr, fun x => he ▸ nval_bc i hr0 hr e x⟩

open ReciprocityTheory.ChartRestriction.G.Geo.Tor in

theorem intAll_ramified {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} (h : Formalism.L2.PjFree.IntAll Xo c)
    (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ) (ho : OverLa la T.V io e)
    (hf : T.FinRes) (y : letI := io.toAlgebra; FrPt Xo c T.Fr) :
    ∃ (T' : CDVR) (io' : c.F →+* T'.Fr) (r : ℕ) (y' : IntFr Xo c T' io'), 0 < r ∧ OverLa la T'.V io' (r * e) ∧
      T'.FinRes ∧
      letI := io.toAlgebra; letI := io'.toAlgebra
      ∃ (φ : T.Fr →ₐ[c.F] T'.Fr) (z : FrPt Xo c T'.Fr) (t : Ix Dw → T'.Frˣ),
        (∀ x, vV T'.V (φ x) = (r : ℤ) * vV T.V x) ∧ (∀ x, nval T'.V (r * e) (φ x) = nval T.V e x) ∧
        FrMap φ y z ∧ FrBor t z y'.1 := by
  obtain ⟨T', io', e', y', ho', hf', φ, z, t, hφ, hz, hb⟩ := h la T io e ho hf y
  let _ := io.toAlgebra
  let _ := io'.toAlgebra
  obtain ⟨r, hr, rfl, h1, h2⟩ := nval_map_of_overLa ho ho' φ.toRingHom (fun a => φ.commutes a) hφ
  exact ⟨T', io', r, y', hr, ho', hf', φ, z, t, h1, h2, hz, hb⟩

end GlobalTheory.IntegralFrameCheck
