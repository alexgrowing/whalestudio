import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PolyBetween
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LocalValuationColumns
import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarmonicValueGeLocalDepthPrimeToPStatement
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ThetaGeneratorPlaceValuationBound
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ShortBoundOfTrivAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.EigRamHelp
open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.PGsh
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1
open GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth GlobalTheory.PtTie GlobalTheory.PlaceInt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

open GlobalTheory.ThetaBound
open Limits MonoidalCategory CartesianMonoidalCategory MonObj

namespace GlobalTheory.RefSum.LowP

set_option maxHeartbeats 1000000 in

theorem thRule_lower : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (nab : NabV Xo c), IsNab Xo c nab → ∀ (p : ℕ), p.Prime → ¬ p ∣ l.M → ∀ (la : PointsOfFlagModel.abelian₂ p c) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ P₁ ∈ harmA (Dw := Dw) c a n, ∀ A B : ℝ, PolyBetween Xo la P₁ A B → ∀ (x : Fin n → Dw.La) (f : Rul Xo c), IsThRule Xo c nab x P₁ f → ∀ (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ), OverLa la.1 T.V io e → ∀ y : IntFr Xo c T io, y.IsAlg → (A : EReal) ≤ nval T.V (vV T.V (p : T.Fr)).toNat (evI y f) := by
  intro E _ _ _ H Dw l Xo c
  letI := H.starRing
  intro nab hnab p hp hpM la a n P₁ hP₁ A B hPB x f hf T io e ho y hy
  have hM0 : 0 < l.M := lt_of_lt_of_le (by norm_num) l.three_le
  obtain ⟨T', iT, r, y', C', ⟨hr, hiT, φ, hφ, hmap⟩, hfin, hgood, hrat⟩ :=
    Prep.exists_good_chart_allRat E H Dw l Xo c hnab.1 T io y hy (l.M ^ 2) (pow_pos hM0 2)
  have ho' := ho.bc iT hr hiT
  have hvp : 0 < vV T.V (p : T.Fr) := by
    have h1 := ho.2 (p : c.F)
    rw [map_natCast] at h1
    rw [h1]
    exact mul_pos (by exact_mod_cast ho.1) (ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.ERam.vLa_pos la.1 p hp.ne_zero la.2)
  have hvp' : vV T'.V (p : T'.Fr) = (r : ℤ) * vV T.V (p : T.Fr) := by
    rw [← map_natCast iT p, hiT]
  obtain ⟨k₀, hk₀⟩ := Int.eq_ofNat_of_zero_le hvp.le
  have he' : (vV T'.V (p : T'.Fr)).toNat = r * (vV T.V (p : T.Fr)).toNat := by
    rw [hvp', hk₀, ← Nat.cast_mul, Int.toNat_natCast, Int.toNat_natCast]
  have hk0 : 0 < k₀ := by omega
  have he'pos : 0 < (vV T'.V (p : T'.Fr)).toNat := by
    rw [he', hk₀, Int.toNat_natCast]; exact Nat.mul_pos hr hk0
  have hu : IsUnit (l.M : T'.V) := by
    refine GlobalTheory.PlaceInt.ShortTriv.isUnit_of_coprime T' (ℓ := p)
      (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).2 hpM)) fun h => ?_
    have h2 := GlobalTheory.PlaceInt.ShortTriv.vV_natCast T' h
    rw [hvp', hk₀] at h2
    have : (0 : ℤ) < (r : ℤ) * (k₀ : ℤ) := by positivity
    omega
  rw [← nval_bc iT hr hiT ((vV T.V (p : T.Fr)).toNat), ← he']
  obtain ⟨n', j, -, -, a3⟩ := (GlobalTheory.TorsFac.factorisation E H Dw l Xo l.M p l.odd dvd_rfl hp).1 hpM
  letI := (iT.comp io).toAlgebra
  choose F hF using fun b : Fin n =>
    (RatData.exists_thetaVal_data E H Dw l Xo c T'.Fr y'.1).1 hrat (x b)
  have hev : iT (evI y f) = thExpr Xo c nab y'.1 P₁ F := by
    letI : Algebra T.Fr T'.Fr := iT.toAlgebra
    exact GlobalTheory.T.thetaRule_value_integral_framed_point_extension_field E H Dw l Xo c nab hnab T io y T'.Fr φ hφ y'.1 hmap a n x P₁ hP₁ F hF f hf
  have ht : ∀ b, ∃ t' : ptO Xo (xOf y') ⟶ Xo.univ.t.G, t' ^ (l.M ^ 2) = 1 ∧
      IsUUOver Xo.univ.t.G Xo.univ.t.PP l.M (sOf1 y') 1 t' (F b) := by
    intro b
    have h1 : levPt Xo y'.1.x (x b) ^ l.M = 1 := by
      obtain ⟨t', -, -, -, -, b1, b2, -⟩ := hF b
      rw [← b1, ← pow_mul, ← pow_two]
      exact (a3 _ t' (killed_pow Xo t' b2) ⟨2, b2⟩).1
    obtain ⟨t', -, b2, b3⟩ :=
      (uu_through_moves E H Dw l Xo T'.Fr (xOf y') l.M l.odd (sOf1 y')).2 _ _ (F b) h1 (hF b)
    exact ⟨t', (a3 _ t' (killed_pow Xo t' b2) ⟨2, b2⟩).1, b3⟩
  choose t' ht1 ht2 using ht
  have hρ : ∀ k, (A : EReal) ≤ nuLocOf C' (vV T'.V (p : T'.Fr)).toNat k (MvPolynomial.map (iT.comp io) P₁) :=
    fun k => (hPB T' (iT.comp io) (r * e) ho' y' hfin C' k).1
  have hb := GlobalTheory.T.harmonic_value_ge_local_depth_prime_to_p E H Dw l Xo c T' (iT.comp io) y' C' hgood nab hnab _ A a n he'pos P₁ hP₁ hρ l.M l.odd hu
    t' F (fun b => ⟨ht1 b, ht2 b⟩)
  have hh := (hv_linear E H Dw l Xo c hnab.1 nab hnab T'.Fr y'.1 n P₁).2.2 l.M F
  rw [← hh] at hb
  rw [hev, thExpr, map_inv₀, map_pow, map_natCast, GlobalTheory.PlaceInt.TermBound.nval_inv_pow_mul T' _ _ _ hu]
  exact hb

end GlobalTheory.RefSum.LowP
