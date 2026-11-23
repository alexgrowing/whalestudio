import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ESmall
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsFlagCharactersLeadingMinorsColength
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntProdRename
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartCharacterIsLogarithmStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
open NumberField IsDedekindDomain Formalism.L2.Pj ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.RefSum
open GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes (IsIntHom IsOrbit FrobOnType embX primeBelow SplitInK InertInK)
open GlobalTheory.IndefiniteRowSideFullHecke.BigBlockCharacters (HasChars)
open GlobalTheory.IndefiniteRowSideFullHecke.FactorDepthInertBounds (boundAll boundInert boundFine)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RefSum

open GlobalTheory.IndefiniteRowSideFullHecke.BigBlockCharacters (pairDet hasChars_iff)

theorem hasChars_frame_of_hasAF : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (p : ℕ) [Fact p.Prime] (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (Ch : IntegralChartA3 Xo c T io y) (X : ValExt T p), ∀ (f : Lt1 Dw) (xs : NNReal) (r : ℝ), ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF.HasAF X.v (fun i => MvPowerSeries.map X.ι (Ch.FT i)) (fun (i : Fin (Dw.mult f.1)) j => X.ι (Ch.uvecT ⟨f.1, i⟩ j)) xs → (X.v (p : X.C) : ℝ) ^ r ≤ xs → HasChars (fgl Ch X) (frame Ch X f) (r : EReal) ∧ ∀ k : ℕ, nuFac p y f k ≤ ((k * r : ℝ) : EReal) := by
  intro E _ _ _ H Dw l Xo c
  letI := H.starRing
  intro p _ T io y Ch X f xs r hAF hr
  have hp0 : (0 : ℝ) < (X.v (p : X.C) : ℝ) := by
    have : X.v (p : X.C) ≠ 0 := by simpa using (Fact.out : p.Prime).ne_zero
    exact_mod_cast pos_iff_ne_zero.2 this
  have hxs0 : (0 : ℝ) < (xs : ℝ) := lt_of_lt_of_le (Real.rpow_pos_of_pos hp0 r) hr
  have hxs : xs ≠ 0 := fun h => by rw [h] at hxs0; simp at hxs0
  obtain ⟨-, χ, hχ, hmin⟩ := exists_flag_characters X.C X.v X.O X.ints _ _ _ _ xs hAF hxs
  let lf : Fin (rk f) → Fin (chD Ch.ch) → X.C := fun b j =>
    algebraMap X.O X.C (ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF.dl (χ (Fin.castLE (rk_le f) b)) j)
  have hl : ∀ b, IsCharLog (fgl Ch X) (lf b) := fun b =>
    GlobalTheory.T.chart_character_is_logarithm E H Dw l Xo c p T io y Ch X _ (hχ _)
  have hdet : pairDet lf (frame Ch X f) = algebraMap X.O X.C (Matrix.of fun a b : Fin (f.2.val + 1) =>
      ∑ j, X.ι (Ch.uvecT ⟨f.1, Fin.castLE f.2.isLt a⟩ j) *
        ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF.dl (χ (Fin.castLE f.2.isLt b)) j).det := by
    rw [RingHom.map_det]
    unfold pairDet
    congr 1
    ext a b
    simp only [Matrix.of_apply, RingHom.mapMatrix_apply, Matrix.map_apply, map_sum, map_mul, frame, lieVec, jX,
      RingHom.comp_apply, X.comp, lf]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have hm := hmin f.2
  rw [← hdet] at hm
  set D := pairDet lf (frame Ch X f) with hD
  have hDpos : (0 : ℝ) < (X.v D : ℝ) := lt_of_lt_of_le hxs0 (by exact_mod_cast hm)
  have hD0 : D ≠ 0 := fun h => by rw [h, map_zero] at hDpos; simp at hDpos
  have hlog := log_v_p_neg X
  have hval : ((Real.log (X.v (p : X.C) : ℝ))⁻¹ * Real.log (X.v D : ℝ)) ≤ r := by
    have h1 : r * Real.log (X.v (p : X.C) : ℝ) ≤ Real.log (X.v D : ℝ) := by
      rw [← Real.log_rpow hp0]
      exact Real.log_le_log (Real.rpow_pos_of_pos hp0 r) (hr.trans (by exact_mod_cast hm))
    have h2 := mul_le_mul_of_nonpos_left h1 (inv_lt_zero.2 hlog).le
    rwa [← mul_assoc, mul_comm _ r, mul_assoc, inv_mul_cancel₀ hlog.ne, mul_one] at h2
  have hvD : vX_vp X D = (((Real.log (X.v (p : X.C) : ℝ))⁻¹ * Real.log (X.v D : ℝ) : ℝ) : WithTop ℝ) :=
    vX_vp_apply X hD0
  refine ⟨(hasChars_iff (isSatFrame_frame Ch X f) _).2 ⟨lf, hl, ?_⟩, fun k => ?_⟩
  · rw [← hD, hvD]
    exact EReal.coe_le_coe_iff.2 hval
  · refine (nuFac_le Ch X f k).trans ?_
    refine (GlobalTheory.FGDepth.CharBound.detDepth_le_char X.C (vX_vp X) (rk f) _ k (fgl Ch X) (frame Ch X f) lf hl).trans ?_
    have e : Matrix.det (Matrix.of fun a b => ∑ e, lf b e * frame Ch X f a e) = D := rfl
    rw [e, AddValuation.map_pow, hvD, ← WithTop.coe_nsmul, nsmul_eq_mul]
    show ((k * ((Real.log (X.v (p : X.C) : ℝ))⁻¹ * Real.log (X.v D : ℝ)) : ℝ) : EReal) ≤ _
    exact EReal.coe_le_coe_iff.2 (mul_le_mul_of_nonneg_left hval (Nat.cast_nonneg k))

end GlobalTheory.RefSum
