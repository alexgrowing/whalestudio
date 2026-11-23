import Mathlib
import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IntegralChartFormalBiext
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IntegralChartDirectionsAreEigenvectors

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt

namespace GlobalTheory.ChartBiext

theorem constantCoeff_gauge {R K O : Type} [CommRing R] [CommRing K] [Algebra ℚ K] [Algebra R K] [CommRing O] [StarRing O]
    {d : ℕ} (B : FB R d O) {h : PS K 2 d} (hh : B.IsCanonGauge K h) : MvPowerSeries.constantCoeff h = 0 := by
  have hz : ∀ p : Fin 2 × Fin d,
      MvPowerSeries.constantCoeff ((![0, pt K d 0] : Fin 2 → Pt K 1 d) p.1 p.2) = 0 := by
    rintro ⟨i, j⟩
    fin_cases i <;> simp [pt]
  have hsub := MvPowerSeries.hasSubst_of_constantCoeff_zero hz
  set c := MvPowerSeries.constantCoeff h with hc
  have hdec : h = MvPowerSeries.C c + (h - MvPowerSeries.C c) := by ring
  have hrest : MvPowerSeries.constantCoeff (h - MvPowerSeries.C c) = 0 := by simp [hc]
  have key := congrArg MvPowerSeries.constantCoeff hh.ax0
  rw [ev, hdec, MvPowerSeries.subst_add hsub, map_add,
    MvPowerSeries.constantCoeff_subst_eq_zero hsub hz hrest] at key
  simpa using key

theorem toK_self {K : Type} [CommRing K] {σ : Type} (f : MvPowerSeries σ K) :
    MvPowerSeries.map (algebraMap K K) f = f := by
  ext m
  simp

theorem nabValN_congr {R R' K O : Type} [CommRing R] [CommRing R'] [CommRing K] [Algebra ℚ K] [Algebra R K] [Algebra R' K]
    [CommRing O] [StarRing O] {d : ℕ} (B : FB R d O) (B' : FB R' d O) (hF : B.FK K = B'.FK K)
    (hA : ∀ a, B.actK K a = B'.actK K a) (h : PS K 2 d) (w0 : O) (m : ℕ) {n : ℕ} (f : PS K n d) {Ix : Type} [Fintype Ix]
    (cp : Ix → Fin n) (u : Ix → Fin d → K) (P : MvPolynomial Ix K) :
    nabValN B K h w0 m f cp u P = nabValN B' K h w0 m f cp u P := by
  simp only [nabValN, FB.hL, hF, hA]

end GlobalTheory.ChartBiext

open GlobalTheory.ChartBiext in

theorem GlobalTheory.PlaceInt.integralBiext_gauge_eig_bound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y), ∃ B : FB T.V (chD C.ch) (𝓞 E), IsBT C B ∧ ∀ B : FB T.V (chD C.ch) (𝓞 E), IsBT C B → B.IsCanonGauge T.Fr (gaugeOf C) ∧ MvPowerSeries.constantCoeff (gaugeOf C) = 0 ∧ (letI := io.toAlgebra; (∀ (ℓ : Lt1 Dw) (a : 𝓞 E), (dAct T.Fr B a).mulVec (C.ch.uvec ℓ) = io (embK c ℓ.1 a) • C.ch.uvec ℓ) ∧ ∀ (e : ℕ) (ρ : ℝ) (w : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ChBound C e ρ w n → ∀ (k : ℕ) (P : MvPolynomial (LtN Dw n) T.Fr), P ∈ FFV (Dw := Dw) T w n → ∀ g : PS T.V n (chD C.ch), ((-ρ : ℝ) : EReal) ≤ nval T.V e (nabValN B T.Fr (gaugeOf C) H.w0 k (FB.toK T.Fr g) (fun ℓ : LtN Dw n => ℓ.2.2) (fun ℓ => C.ch.uvec ⟨ℓ.1, ℓ.2.1⟩) P)) := by
  intro E _ _ _ H Dw l Xo c inst hstar T io y C

  have hinst : inst = H.starRing := by
    cases inst with
    | @mk toStarMul star_add =>
      cases toStarMul with
      | @mk toInvolutiveStar star_mul =>
        cases toInvolutiveStar with
        | @mk toStar star_involutive =>
          cases toStar with
          | @mk s =>
            have hs : s = fun a => H.bar a := funext hstar
            subst hs
            rfl
  subst hinst
  letI : StarRing (𝓞 E) := H.starRing
  obtain ⟨BT, hF, hA, h1, h2, hs, had, hK⟩ := GlobalTheory.integralChart_formalBiext E H Dw l Xo c T io y C
  obtain ⟨hFK, hAK, hG, hC⟩ := hK T.Fr
  refine ⟨BT, ⟨hF, hA, h1, h2, hs, had⟩, ?_⟩
  intro B hB
  obtain ⟨hBF, hBA, hB1, hB2, hBs, hBa⟩ := hB

  have eFK : B.FK T.Fr = BT.FK T.Fr := by
    funext i
    show MvPowerSeries.map _ (B.G.F i) = MvPowerSeries.map _ (BT.G.F i)
    rw [hBF, hF]
  have eAK : ∀ a, B.actK T.Fr a = BT.actK T.Fr a := by
    intro a
    funext i
    show MvPowerSeries.map _ (B.A.act a i) = MvPowerSeries.map _ (BT.A.act a i)
    rw [hBA, hA]
  have hgB : B.IsCanonGauge T.Fr (gaugeOf C) ↔ BT.IsCanonGauge T.Fr (gaugeOf C) :=
    GlobalTheory.FBDescent.gauge_iff B BT T.Fr eFK eAK (by rw [hB1, h1]) (by rw [hB2, h2]) (by rw [hBs, hs])
      (fun a => by rw [hBa, had]) (gaugeOf C)
  have hgT : BT.IsCanonGauge T.Fr (gaugeOf C) := by
    rw [GlobalTheory.ChartBiext.toK_self] at hC
    exact (hG _).2 hC
  have hgauge : B.IsCanonGauge T.Fr (gaugeOf C) := hgB.2 hgT
  refine ⟨hgauge, GlobalTheory.ChartBiext.constantCoeff_gauge B hgauge, ?_⟩
  letI := io.toAlgebra
  have eFK' : B.FK T.Fr = C.ch.B.FK T.Fr := eFK.trans hFK
  have eAK' : ∀ a, B.actK T.Fr a = C.ch.B.actK T.Fr a := fun a => (eAK a).trans (hAK a)
  refine ⟨fun ℓ a => ?_, ?_⟩
  ·
    have hd : dAct T.Fr B a = dAct T.Fr C.ch.B a := by
      unfold dAct
      rw [eAK' a]
    rw [hd]
    exact GlobalTheory.PowGerm.eigDirSt E H Dw l Xo c T io y C a ℓ
  · intro e ρ w n hb k P hP g
    have hint : IsIntPS T (FB.toK T.Fr g) := fun m =>
      ⟨MvPowerSeries.coeff m g, by simp [FB.toK, MvPowerSeries.coeff_map]⟩
    have hle : nuLocC C e k w n ≤ nval T.V e (nabValN C.ch.B T.Fr C.ch.h H.w0 k (FB.toK T.Fr g)
        (fun ℓ : LtN Dw n => ℓ.2.2) (fun ℓ => C.ch.uvec ⟨ℓ.1, ℓ.2.1⟩) P) := by
      unfold nuLocC
      exact iInf₂_le_of_le P hP (iInf₂_le (FB.toK T.Fr g) hint)
    rw [GlobalTheory.ChartBiext.nabValN_congr B C.ch.B eFK' eAK']
    exact (hb k).trans hle
