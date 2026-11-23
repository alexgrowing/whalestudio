import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PolyBetween
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LocalValuationColumns
import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ThetaGeneratorsLeastValueOverLevelPrime
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsProductDataCopiesTrivialisationValuation
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.HodgeTateInclusionChartCharacters
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsIsNabUncond
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.StarRingExtOfStar
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.NumericalConsequencesOfPins
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExtensionUniformisedChartScaleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsShortPeriodLatticeBasisBalancedSlopeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaRuleBoundedBelow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormClearDenominatorsAwayFromPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaRulesExistAndCusp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelHalfSplit
open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.PGsh
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1
open GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth GlobalTheory.PtTie GlobalTheory.PlaceInt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.RefLevel

theorem lattice_terms_le {κ R s N d g' V r φ cst : ℝ} (hκ : 0 ≤ κ) (hR : 0 ≤ R) (hs : 0 ≤ s) (hsN : s ≤ N) (hV : 0 < V)
    (hr : 0 < r) (hφ : 0 ≤ φ) (hg' : 0 < g') (hc : κ * N ^ 3 * (R * N / 4 + 2 * d ^ 2) / g' ≤ cst) :
    (R * s * (κ * s ^ 3 * (r * φ)) / (4 * g') + 2 * d ^ 2 * (κ * s ^ 3 * (r * φ)) / g') / (r * V) ≤ cst * φ / V := by
  have hN : 0 ≤ N := hs.trans hsN
  calc (R * s * (κ * s ^ 3 * (r * φ)) / (4 * g') + 2 * d ^ 2 * (κ * s ^ 3 * (r * φ)) / g') / (r * V)
      = κ * s ^ 3 * (R * s / 4 + 2 * d ^ 2) / g' * φ / V := by field_simp
    _ ≤ κ * N ^ 3 * (R * N / 4 + 2 * d ^ 2) / g' * φ / V := by gcongr
    _ ≤ cst * φ / V := by gcongr

theorem not_isUnit_of_vV_ne_zero (S : CDVR) (N : ℕ) (h : vV S.V ((N : ℕ) : S.Fr) ≠ 0) : ¬ IsUnit ((N : ℕ) : S.V) := by
  intro hu
  apply h
  have h2 : valV S.V (algebraMap S.V S.Fr ((N : ℕ) : S.V)) = 1 := by
    unfold valV
    rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff]
    exact fun h => (mem_nonunits_iff.1 h) hu
  rw [map_natCast] at h2
  unfold vV
  rw [h2]
  simp

theorem vV_pos {K : Type} [Field K] [NumberField K] {p : ℕ} (hp : p ≠ 0) {la : HeightOneSpectrum (𝓞 K)}
    (hla : (p : 𝓞 K) ∈ la.asIdeal) {T : CDVR} {io : K →+* T.Fr} {k : ℕ} (ho : OverLa la T.V io k) :
    0 < vV T.V (p : T.Fr) := by
  have h := ho.2 (p : K)
  rw [map_natCast] at h
  rw [h]
  refine mul_pos (by exact_mod_cast ho.1) ?_
  have h1 : la.valuation K (p : K) < 1 := by
    have := (la.valuation_lt_one_iff_mem (K := K) (p : 𝓞 K)).2 hla
    have e : ((p : 𝓞 K) : K) = (p : K) := map_natCast (algebraMap (𝓞 K) K) p
    rw [← e]
    exact this
  have h0 : la.valuation K (p : K) ≠ 0 := (Valuation.ne_zero_iff _).2 (Nat.cast_ne_zero.2 hp)
  have := (WithZero.log_lt_log h0 one_ne_zero).2 h1
  rw [WithZero.log_one] at this
  unfold vLa
  omega

theorem coprime_level (D : D7) (k : Fin 2) : Nat.Coprime (D.host.g k) (D.host.QS * D.host.q * D.host.d) := by
  have hc : D.host.g k % (D.host.QS * D.host.q * D.host.d) = 1 := D.ntypes.g_cond k
  rw [Nat.Coprime, Nat.gcd_comm, Nat.gcd_rec, hc]
  simp

theorem refExp_le_of_halfSplit (D : D7) (T : Core D) (hM : LawsM T) (j : ℕ) (hj : InR D j)
    (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) (cst : ℝ) (hDom : Dom a n) (hLast : LastPos (T.Q.Dw j) a)
    (hrn : 2 * D.R.r ≤ n) (g g' : ℕ) (ρ ρ' : 𝓞 D.host.E) (hH : HalfSplit T.Q.l g g' ρ ρ')
    (hcop : Nat.Coprime (g * g') (D.host.QS * D.host.q * D.host.d)) (hg : 4 * DF (T.Q.Dw j) a + 4 ≤ g)
    (hg' : 4 * DF (T.Q.Dw j) a + 4 ≤ g') (hM0 : (DF (T.Q.Dw j) a : ℝ) * (2 * Real.sqrt (2 * D.R.f * D.R.m)) < g')
    (hc : rr0 D * (2 * D.R.f * D.R.m : ℝ) ^ 3 *
      ((D.R.r : ℝ) * (2 * D.R.f * D.R.m) / 4 + 2 * (DF (T.Q.Dw j) a : ℝ) ^ 2) / g' ≤ cst) :
    refExp_vp (T.U j) cst (wtZ a n) g ≤ ((1 : ℝ) : EReal) := by
  rw [refExp_vp_le_iff]
  intro la S io e ho y hy φ hφ
  obtain ⟨st, nab, hn⟩ :=
    GlobalTheory.CanonConn.exists_isNab_uncond D.host.E T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c
  have hst := GlobalTheory.PowGerm.starSt _ T.Q.H st hn.1
  subst hst
  letI := T.Q.H.starRing
  obtain ⟨-, -, -, -, -, hE, hnum⟩ := GlobalTheory.PinNum.numerics_of_pins D T.Q hM.pins
  obtain ⟨hpq, hr1, -⟩ := hnum j hj
  have hq : (T.Q.Dw j).q = D.R.m - j := (hM.pins.2.2.2 j hj).2.1
  obtain ⟨hTot, hcusp⟩ := GlobalTheory.thetaRules_exist_and_cusp D.host.E T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c D.R.r (T.U j) hr1
    (hM.unf j hj) nab hn
  obtain ⟨S', io', y', r, C, P, hy', hr, hFT, hTI, hφ', hOv, hvv, hnv⟩ :=
    GlobalTheory.T.exists_finiteExtension_uniformisedChart_scale D.host.E T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c S io y hy φ hφ
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible S'.V
  obtain ⟨⟨Q, hQ⟩, -⟩ :=
    GlobalTheory.PowData.exists_powData D.host.E T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c S' io' y' C P ϖ hϖ
  obtain ⟨s, hs, hΦ, b, hb1, hb2⟩ :=
    GlobalTheory.T.exists_short_periodLattice_basis_balanced_slope D.host.E T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c S' io' y' _ hφ' C P ϖ hϖ Q hQ
  obtain ⟨m, hmfin, hmle, hmeq⟩ :=
    GlobalTheory.ThetaLow.thetaRule_bounded_below D T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c nab hn g g' ρ ρ' hH hcop a n
  obtain ⟨hgp, hgp', hne, hMl, hρ, hρ', hMb, hsp, -⟩ := hH
  have hρs : ρ * star ρ = (g : 𝓞 D.host.E) := hρ
  have hρs' : ρ' * star ρ' = (g' : 𝓞 D.host.E) := hρ'
  have hV : 0 < vV S.V (g : S.Fr) := vV_pos hgp.ne_zero la.2 ho
  have hV' := hvv g hgp.ne_zero
  have hrZ : (0 : ℤ) < r := by exact_mod_cast hr
  have hsN : (s : ℝ) ≤ 2 * D.R.f * D.R.m := by
    rw [hE, hq] at hs
    exact_mod_cast hs.trans (Nat.mul_le_mul_left _ (Nat.sub_le _ _))
  obtain ⟨e₀, he₀⟩ : ∃ e₀ : ℕ, vV S.V (g : S.Fr) = e₀ := ⟨_, (Int.toNat_of_nonneg hV.le).symm⟩
  have he₀0 : 0 < e₀ := by omega
  have hA := GlobalTheory.LevelPrimePoint.least_value_le GlobalTheory.ChF.hodgeTate_inclusion_chart D.host.E T.Q.H (T.Q.Dw j) T.Q.l
    (T.Q.Xo j) T.Q.c nab hn hTot S' io' y' C hFT P hTI hy' ϖ hϖ Q hQ _ _ s b hΦ hb1 hb2 g g' hgp hgp' hne hMl ρ ρ'
    hρs hρs' hMb hsp.1 hsp.2 (not_isUnit_of_vV_ne_zero S' g (by rw [hV']; exact (mul_pos hrZ hV).ne')) a n (r * e₀)
    hDom.1 (by rw [hpq]; exact hrn) (by omega) (Nat.mul_pos hr he₀0) (by omega) hg'
    (lt_of_le_of_lt (by gcongr) hM0)
  have hν : (∏ τ : D.host.E →+* ℂ, (io' (embK T.Q.c τ (star ρ * star ρ'))) ^ (∑ i : Fin ((T.Q.Dw j).mult τ), a (τ, i))) =
      io' (nrm (T.Q.Dw j) T.Q.c a (star ρ * star ρ')) := by
    unfold nrm
    simp only [map_prod, map_pow]
  have hν0 : nrm (T.Q.Dw j) T.Q.c a (star ρ * star ρ') ≠ 0 := by
    refine Finset.prod_ne_zero_iff.2 fun τ _ => pow_ne_zero _ fun h0 => ?_
    have h1 : (star ρ * star ρ') * (ρ * ρ') = ((g * g' : ℕ) : 𝓞 D.host.E) := by
      rw [Nat.cast_mul, ← hρs, ← hρs']; ring
    have h2 := congrArg (embK T.Q.c τ) h1
    rw [map_mul, h0, zero_mul, map_natCast] at h2
    exact (Nat.cast_ne_zero.2 (Nat.mul_ne_zero hgp.ne_zero hgp'.ne_zero)) h2.symm
  rw [hν, hpq, hV', he₀, nval_of_ne ((map_ne_zero io').2 hν0)] at hA
  generalize nrm (T.Q.Dw j) T.Q.c a (star ρ * star ρ') = ν at hA hν0 hmeq
  generalize hN : ((vV S'.V (io' ν) : ℝ) / ((r * e₀ : ℕ) : ℝ) : ℝ) = N at hA
  have hlt : (⨅ f ∈ thGen (T.Q.Xo j) T.Q.c nab a n, nval S'.V (r * e₀) (evI y' f)) <
      ((1 + cst * φ / e₀ - N : ℝ) : EReal) := by
    rw [← EReal.le_sub_iff_add_le (Or.inl (EReal.coe_ne_bot _)) (Or.inl (EReal.coe_ne_top _)), ← EReal.coe_sub] at hA
    refine hA.trans_lt (EReal.coe_lt_coe_iff.2 (sub_lt_sub_right ?_ _))
    have hrR : (0 : ℝ) < r := by exact_mod_cast hr
    have heR : (0 : ℝ) < e₀ := by exact_mod_cast he₀0
    have hgR : (4 : ℝ) * DF (T.Q.Dw j) a + 4 ≤ g := by exact_mod_cast hg
    have hd0 : (0 : ℝ) ≤ DF (T.Q.Dw j) a := Nat.cast_nonneg _
    rw [add_assoc, add_div]
    push_cast
    refine add_lt_add_of_lt_of_le ?_ (lattice_terms_le (by positivity) (Nat.cast_nonneg _) (Nat.cast_nonneg _) hsN heR hrR
      hφ.nonneg (by exact_mod_cast hgp'.pos) hc)
    rw [mul_div_assoc, mul_div_cancel_left₀ _ (mul_pos hrR heR).ne', div_lt_one (by linarith)]
    linarith
  simp only [iInf_lt_iff] at hlt
  obtain ⟨f, hf, hlt⟩ := hlt
  obtain ⟨t, ht0, htv, w, hw, hwe⟩ := GlobalTheory.T.cuspForm_clear_denominators_away_from_place D.host.E T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c D.R.r (T.U j)
    (wtZ a n) ⟨f, hcusp a n hDom hLast f hf⟩ m hmfin (hmle f hf) la.1 (-vLa la.1 ν) fun v hv => by
      have h := hmle f hf la.1 v hv
      rw [hmeq la.1 (Or.inl la.2)] at h
      rw [Int.cast_neg]
      exact h
  have ho' := hOv la.1 e ho
  refine (iInf₂_le w hw).trans ?_
  show nval S.V (vV S.V (g : S.Fr)).toNat (evI y (w : Rul (T.Q.Xo j) T.Q.c)) ≤ _
  rw [hwe, evI_smul, he₀, Int.toNat_natCast, ← hnv nab hn a n e₀ t f hf, nval_mul, nval_of_ne ((map_ne_zero io').2 ht0),
    ho'.2 t, htv, neg_neg, ← ho'.2 ν, hN]
  refine (add_le_add le_rfl hlt.le).trans (le_of_eq ?_)
  rw [← EReal.coe_add, ← EReal.coe_add]
  congr 1
  push_cast
  ring

theorem refExp_level_le_one : ∀ (D : D7) (T : Core D), LawsM T → ∀ (_ : ErrX D) (j : ℕ), InR D j → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) (cst : ℝ), Dom a n → LastPos (T.Q.Dw j) a → ∑ f : Lt1 (T.Q.Dw j), 2 * rk f ≤ n → 2 * D.R.r ≤ n → JetNum D (DF (T.Q.Dw j) a) cst → ∀ k : Fin 2, refExp_vp (T.U j) cst (wtZ a n) (D.host.g k) ≤ ((1 : ℝ) : EReal) := by
  intro D T hM EX j hj a n cst hDom hLast _ hrn hJ k
  obtain ⟨π, π', hH⟩ := GlobalTheory.SplitLevel.level_halfSplit D T hM EX
  obtain ⟨k', ρ, ρ', hk⟩ : ∃ (k' : Fin 2) (ρ ρ' : 𝓞 D.host.E), HalfSplit T.Q.l (D.host.g k) (D.host.g k') ρ ρ' := by
    fin_cases k
    · exact ⟨1, π, π', hH⟩
    · exact ⟨0, π', π, hH.symm⟩
  exact refExp_le_of_halfSplit D T hM j hj a n cst hDom hLast hrn _ _ ρ ρ' hk
    (Nat.Coprime.mul_left (coprime_level D k) (coprime_level D k')) (hJ k).1 (hJ k').1 (hJ k').2.1 (hJ k').2.2

end GlobalTheory.RefLevel
