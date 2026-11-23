import Mathlib
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.FinLocalCutAt
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FrameChangeComposeInvertBaseChangeTriangular
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FramedPointEvalNaturalWeightScaling
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArcLetterRingOverDVRPolynomialDenominators
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArcFramedPointUniqueAndBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArcFramedPointIntegralOpenDiscStatement
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IntegralOfFrChg
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsFactorOfMemRange

noncomputable section

namespace GlobalTheory.ArcQ.RecFr

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames

section Val

variable {V K' : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K'] [Algebra V K']
  [IsFractionRing V K']

theorem mem_of_vV_nonneg {x : K'} (h : 0 ≤ vV V x) : x ∈ Set.range (algebraMap V K') := by
  by_cases hx : x = 0
  · exact ⟨0, by simp [hx]⟩
  have h1 : valV V x ≤ 1 := by
    have := (WithZero.log_le_log (valV_ne_zero (V := V) hx) one_ne_zero).1 (by simp only [vV] at h; simp; omega)
    exact this
  exact IsDiscreteValuationRing.exists_lift_of_le_one h1

theorem mem_of_nval_nonneg {e : ℕ} (he : 0 < e) {x : K'} (h : 0 ≤ nval V e x) : x ∈ Set.range (algebraMap V K') := by
  by_cases hx : x = 0
  · exact ⟨0, by simp [hx]⟩
  rw [nval_of_ne hx, EReal.coe_nonneg] at h
  have he' : (0 : ℝ) < e := by exact_mod_cast he
  have : (0 : ℝ) ≤ vV V x := by
    by_contra hc
    exact absurd h (not_le.2 (div_neg_of_neg_of_pos (not_le.1 hc) he'))
  exact mem_of_vV_nonneg (by exact_mod_cast this)

theorem vV_one : vV V (1 : K') = 0 := by simp [vV]

theorem vV_unit (u : Vˣ) : vV V (algebraMap V K' u) = 0 := by
  have : valV V (algebraMap V K' u) = 1 := by
    rw [valV, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff]
    exact fun h => (IsLocalRing.mem_maximalIdeal _).1 h u.isUnit
  simp [vV, this]

theorem vV_pow {x : K'} (hx : x ≠ 0) (n : ℕ) : vV V (x ^ n) = n * vV V x := by
  simp [vV]

theorem vV_pos {a : V} (ha : a ≠ 0) (hu : ¬ IsUnit a) : 0 < vV V (algebraMap V K' a) := by
  have h0 : algebraMap V K' a ≠ 0 := by simpa using ha
  have : valV V (algebraMap V K' a) < 1 := by
    rw [valV, HeightOneSpectrum.valuation_lt_one_iff_mem]
    exact hu
  have := (WithZero.log_lt_log (valV_ne_zero (V := V) h0) one_ne_zero).2 this
  simp only [vV]; simp at this; omega

theorem vV_irr {a : V} (ha : Irreducible a) : vV V (algebraMap V K' a) = 1 := by
  have : valV V (algebraMap V K' a) = WithZero.exp (-1 : ℤ) := by
    rw [valV, HeightOneSpectrum.valuation_of_algebraMap]
    exact HeightOneSpectrum.intValuation_singleton _ ha.ne_zero ha.maximalIdeal_eq
  simp [vV, this]

theorem exists_index {V' K'' : Type} [CommRing V'] [IsDomain V'] [IsDiscreteValuationRing V'] [Field K'']
    [Algebra V' K''] [IsFractionRing V' K''] (j : V →+* V') [IsLocalHom j] (i : K' →+* K'')
    (hi : ∀ v, i (algebraMap V K' v) = algebraMap V' K'' (j v)) :
    ∃ r : ℕ, 0 < r ∧ ∀ x, vV V' (i x) = (r : ℤ) * vV V x := by
  obtain ⟨p, hp⟩ := IsDiscreteValuationRing.exists_irreducible V
  have inj : ∀ v, v ≠ 0 → algebraMap V' K'' (j v) ≠ 0 := fun v hv => by
    rw [← hi]; simpa using hv
  have pos : 0 < vV V' (algebraMap V' K'' (j p)) :=
    vV_pos (fun h => inj p hp.ne_zero (by simp [h])) (fun h => hp.not_isUnit (isUnit_of_map_unit j p h))
  obtain ⟨r, hr⟩ := Int.eq_ofNat_of_zero_le pos.le
  have key : ∀ v : V, v ≠ 0 → vV V' (i (algebraMap V K' v)) = (r : ℤ) * vV V (algebraMap V K' v) := by
    intro v hv
    obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hv hp
    have h1 : algebraMap V K' p ≠ 0 := by simpa using hp.ne_zero
    have h2 : algebraMap V K' u ≠ 0 := by simp
    rw [hi, map_mul, map_mul, map_mul, map_pow, map_pow, map_pow,
      vV_mul (inj _ u.ne_zero) (pow_ne_zero _ (inj p hp.ne_zero)), vV_mul h2 (pow_ne_zero _ h1),
      vV_pow (inj p hp.ne_zero), vV_pow h1, vV_unit, vV_irr hp, hr]
    have := vV_unit (K' := K'') (Units.map j.toMonoidHom u)
    simp only [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe] at this
    rw [this]; ring
  refine ⟨r, by omega, fun x => ?_⟩
  by_cases hx : x = 0
  · simp [hx, vV]
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := V) x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have ha0 : a ≠ 0 := by rintro rfl; simp at hx
  have hb1 : algebraMap V K' b ≠ 0 := by simpa using hb0
  have e : algebraMap V K' a / algebraMap V K' b * algebraMap V K' b = algebraMap V K' a := div_mul_cancel₀ _ hb1
  have e1 := vV_mul (V := V) hx hb1
  have e2 := vV_mul (V := V') ((map_ne_zero i).2 hx) ((map_ne_zero i).2 hb1)
  rw [← map_mul, e, key a ha0, key b hb0] at e2
  rw [e] at e1
  rw [e1] at e2
  linarith

end Val

theorem isUnit_of_norm {V K : Type} [CommRing V] [IsLocalRing V] [NormedField K] (f : V →+* K) (h : ∀ v, ‖f v‖ ≤ 1)
    (h' : ∀ x : K, ‖x‖ ≤ 1 → (∃ v, f v * x = 1) → ∃ v, f v = x) (hf : Function.Injective f) {v : V} (hv : ‖f v‖ = 1) :
    IsUnit v := by
  have h0 : f v ≠ 0 := fun h0 => by simp [h0] at hv
  obtain ⟨u, hu⟩ := h' (f v)⁻¹ (by rw [norm_inv, hv]; simp) ⟨v, mul_inv_cancel₀ h0⟩
  exact IsUnit.of_mul_eq_one u (hf (by rw [map_mul, hu, map_one, mul_inv_cancel₀ h0]))

end GlobalTheory.ArcQ.RecFr

namespace GlobalTheory.ArcQ

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames

set_option maxHeartbeats 1600000 in

theorem recordAt_of_isArcFr : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), GlobalTheory.Reg.EvLaws Xo c → ∀ (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra c.F K₁] (d : ArcDatum Xo c K₁) (w : HeightOneSpectrum (𝓞 K₁)) (Z : FinSite K₁ w) (Dv : DvrFrame d w Z) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (b : O →+* Dv.Tv.V) (aw : ArcIn Dw l β Dv.Tv.V b) (χ : Sp (PowerSeries Dv.Tv.V) ⟶ Y.X) (W : Wit Y aw χ) (ρ : (E →+* ℂ) → (𝓞 E →+* Dv.Tv.V)) (e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt aw.D₀ (epsR Dv.Tv.V)) (th : aw.D₀.P.L.Sec) (y₀ : FrPt Xo c (ArcSR Dw Dv.Tv.V Dv.ϖ)) (la : HeightOneSpectrum (𝓞 c.F)) (eL : ℕ), SiteAlg Z Dv.Tv Dv.ιT → OverLa la Dv.Tv.V (Dv.io.comp (algebraMap c.F K₁)) eL → (∀ τ x, algebraMap Dv.Tv.V Dv.Tv.Fr (ρ τ x) = Dv.io (algebraMap c.F K₁ (embK c τ x))) → (∀ (x : c.F) (v : Dv.Tv.V) (n : ℕ), (Dv.io.comp (algebraMap c.F K₁)) x * algebraMap Dv.Tv.V Dv.Tv.Fr Dv.ϖ ^ n = algebraMap Dv.Tv.V Dv.Tv.Fr v → algebraMap c.F (ArcSR Dw Dv.Tv.V Dv.ϖ) x * arcιR Dw Dv.Tv.V Dv.ϖ (PowerSeries.C (R := Dv.Tv.V) Dv.ϖ) ^ n = arcιR Dw Dv.Tv.V Dv.ϖ (PowerSeries.C (R := Dv.Tv.V) v)) → PushInvertible Y.t.G Y.t.PP.L → ArcBasis W ρ e → ThNZ th → Mono Y.j → IsArcFr W e th (arcιR Dw Dv.Tv.V Dv.ϖ) y₀ → FrChg (letMR Dw Dv.Tv.V Dv.ϖ) 1 y₀ Dv.yR → ∀ a n, RecordAt Dv (intAt Xo c a n la) := by
  intro hL hL2 E _ _ _ H Dw l Xo c hev K₁ _ _ _ d w Z Dv O _ β Y b aw χ W ρ e th y₀ la eL hS hO hρ hpin hP hB hth hmono hy hchg
    a n F hF t ht Yv hYv hdet ev hev1 hev2
  classical
  obtain ⟨T', j, i', hfin, hloc, hj, hnorm, hs⟩ := hS (insert t (Finset.univ.image Yv)) (by
    intro x hx
    rcases Finset.mem_insert.1 hx with rfl | hx
    · exact ⟨Or.inr ht, (Z.S_disc _ ht).2.le⟩
    · obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 hx
      exact ⟨Or.inl (hYv x).1, (hYv x).2⟩)
  obtain ⟨t', ht'⟩ := hs t (Finset.mem_insert_self _ _)
  choose Y' hY' using fun x => hs (Yv x) (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ x)))
  have hϖ : Dv.ϖ ≠ 0 := Dv.ϖ_irr.ne_zero
  obtain ⟨e₀, e₁, he₀, he₁, he₁X, hev'⟩ := GlobalTheory.ArcQ.eval_factors_through_cdvr E H Dw Dv.Tv T' Dv.ϖ Z.K Dv.ιT j i' hϖ hj hnorm t' Y' ev
    (ht' ▸ (Z.S_disc _ ht).2) (fun p => by rw [ht']; exact hev1 p) (fun x => by rw [hY']; exact hev2 x)
  have hinj : Function.Injective ((algebraMap T'.V T'.Fr).comp j) := by
    intro x y hxy
    have := congrArg i' hxy
    simp only [RingHom.comp_apply, hj] at this
    exact IsFractionRing.injective _ _ (Dv.ιT.injective this)
  let i : Dv.Tv.Fr →+* T'.Fr := IsFractionRing.lift hinj
  have hi : ∀ v, i (algebraMap Dv.Tv.V Dv.Tv.Fr v) = algebraMap T'.V T'.Fr (j v) := fun v =>
    IsFractionRing.lift_algebraMap hinj v
  obtain ⟨r, hr, hri⟩ := RecFr.exists_index j i hi
  let io' : c.F →+* T'.Fr := i.comp (Dv.io.comp (algebraMap c.F K₁))
  have hO' : OverLa la T'.V io' (r * eL) := hO.bc i hr hri
  letI := io'.toAlgebra
  have he₁C : ∀ v, e₁ (arcιR Dw Dv.Tv.V Dv.ϖ (PowerSeries.C (R := Dv.Tv.V) v)) = algebraMap T'.V T'.Fr (j v) :=
    fun v => (RingHom.congr_fun he₁ _).trans (congrArg (algebraMap T'.V T'.Fr) (RingHom.congr_fun he₀ v))
  have hcomm : ∀ x : c.F, e₁ (algebraMap c.F _ x) = io' x := by
    intro x
    obtain ⟨v, m, hv⟩ : ∃ (v : Dv.Tv.V) (m : ℕ), (Dv.io.comp (algebraMap c.F K₁)) x *
        algebraMap Dv.Tv.V Dv.Tv.Fr Dv.ϖ ^ m = algebraMap Dv.Tv.V Dv.Tv.Fr v := by
      obtain ⟨p, q, hq, hpq⟩ := IsFractionRing.div_surjective (A := Dv.Tv.V) ((Dv.io.comp (algebraMap c.F K₁)) x)
      obtain ⟨m, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (nonZeroDivisors.ne_zero hq) Dv.ϖ_irr
      refine ⟨p * ((u⁻¹ : Dv.Tv.Vˣ) : Dv.Tv.V), m, ?_⟩
      have h1 : algebraMap Dv.Tv.V Dv.Tv.Fr Dv.ϖ ≠ 0 := by simpa using hϖ
      have h2 : algebraMap Dv.Tv.V Dv.Tv.Fr u ≠ 0 := by simp
      rw [← hpq, map_mul, map_mul, map_pow, map_units_inv]
      field_simp
    have h1 := congrArg e₁ (hpin x v m hv)
    have h2 := congrArg i hv
    rw [map_mul, map_pow, he₁C, he₁C] at h1
    rw [map_mul, map_pow, hi, hi, ← h1] at h2
    have h3 : algebraMap T'.V T'.Fr (j Dv.ϖ) ≠ 0 := fun h => hϖ (hinj (h.trans (map_zero _).symm))
    exact (mul_right_cancel₀ (pow_ne_zero _ h3) h2).symm
  let φ : ArcSR Dw Dv.Tv.V Dv.ϖ →ₐ[c.F] T'.Fr := { e₁ with commutes' := hcomm }
  obtain ⟨z₀, hz₀⟩ := hev.bc _ _ φ y₀
  obtain ⟨z₁, hz₁⟩ := hev.bc _ _ φ Dv.yR
  have hA : IsArcFr W e th ((algebraMap T'.V T'.Fr).comp e₀) z₀ := by
    rw [← he₁]
    have key := (GlobalTheory.T.arcFramedPoint_unique_and_baseChange hL hL2 E H Dw l Xo c O β Y Dv.Tv.V b aw χ W e th hth _ _ y₀ hy).2
    first
      | exact key hmono _ φ z₀ hz₀
      | exact key _ φ z₀ hz₀
  have hI₀ : Integral T' io' z₀ := by
    have key := GlobalTheory.T.arc_framedPoint_integral_open_disc hL hL2 E H Dw l Xo c O β Y Dv.Tv.V b aw χ W ρ e th hB hth hP
    have h1 : Function.Injective (e₀.comp (PowerSeries.C (R := Dv.Tv.V))) := by
      rw [he₀]; exact Function.Injective.of_comp (f := algebraMap T'.V T'.Fr) hinj
    have h2 : ∀ τ x, io' (embK c τ x) = algebraMap T'.V T'.Fr (e₀ (PowerSeries.C (R := Dv.Tv.V) (ρ τ x))) :=
      fun τ x => by
        rw [show e₀ (PowerSeries.C (R := Dv.Tv.V) (ρ τ x)) = j (ρ τ x) from RingHom.congr_fun he₀ _, ← hi, hρ]
        rfl
    exact key T' io' e₀ h1 h2 z₀ hA
  have hc := ((GlobalTheory.Frames.frChg_calculus E H Dw l Xo c (ArcSR Dw Dv.Tv.V Dv.ϖ)).2.2.1 T'.Fr φ _ _ y₀ Dv.yR z₀ z₁ hchg hz₀).1 hz₁
  let f : T'.V →+* Z.K := i'.comp (algebraMap T'.V T'.Fr)
  have hf : ∀ v, ‖f v‖ ≤ 1 := fun v => (hnorm _).2 ⟨v, rfl⟩
  have finj : Function.Injective f := i'.injective.comp (IsFractionRing.injective _ _)
  let g : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) T'.V := fun τ => Matrix.of fun p q => Y' ⟨τ, p, q⟩
  have hg : IsUnit (∏ τ, (g τ).det) := by
    refine RecFr.isUnit_of_norm f hf ?_ finj ?_
    · rintro x hx ⟨v, hv⟩
      have hx' : x = i' (algebraMap T'.V T'.Fr v)⁻¹ := by
        rw [map_inv₀]; exact eq_inv_of_mul_eq_one_right hv
      obtain ⟨u, hu⟩ := (hnorm _).1 (hx' ▸ hx)
      exact ⟨u, by rw [hx', ← hu]; rfl⟩
    · rw [← hdet, map_prod]
      congr 2
      funext τ
      rw [RingHom.map_det]
      congr 1
      ext p q
      exact hY' _
  have hI₁ : Integral T' io' z₁ := by
    refine GlobalTheory.ArcQ.IntChg.integral_of_frChg E H Dw l Xo c T' io' g 1 (fun τ => ?_) isUnit_one z₀ z₁ ?_ hI₀
    · exact isUnit_of_dvd_unit (Finset.dvd_prod_of_mem (fun τ => (g τ).det) (Finset.mem_univ τ)) hg
    · have e1 : (fun τ => (g τ).map (algebraMap T'.V T'.Fr)) = fun τ => (letMR Dw Dv.Tv.V Dv.ϖ τ).map φ := by
        funext τ
        ext p q
        exact (he₁X ⟨τ, p, q⟩).symm
      rw [e1, map_one]
      rwa [map_one] at hc
  let yI : IntFr Xo c T' io' := ⟨z₁, hev.test _ z₁, hI₁⟩
  have h0 : 0 ≤ nval T'.V (r * eL) (evI yI F) :=
    hF.2 _ ⟨PtV.mk (cls := Formalism.L2.PjFree.algCls Xo c) (lies := fun _ _ _ _ => True) la hO' yI hfin () trivial, rfl⟩
  haveI := (GlobalTheory.LetterDenom.main E H Dw Dv.Tv Dv.ϖ hϖ).1
  have hnat := (GlobalTheory.ArcQ.evR_natural_weight_scaling E H Dw l Xo c hev a n F hF.1 (ArcSR Dw Dv.Tv.V Dv.ϖ)).1 T'.Fr φ Dv.yR z₁ hz₁
  rw [← hev']
  have := (hnorm _).2 (RecFr.mem_of_nval_nonneg hO'.1 h0)
  rw [show evI yI F = e₁ (evR Xo c F Dv.yR) from hnat] at this
  exact this

end GlobalTheory.ArcQ
