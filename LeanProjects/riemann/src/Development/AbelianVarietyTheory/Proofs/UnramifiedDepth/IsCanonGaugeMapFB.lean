import Mathlib
import Formalism.LocalToGlobal.CharacterGerms.HostTraceIdentity
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.EqZeroOrSingleOfDegreeLeOne
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.VVAlgebraMapNonnegDvr
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsFormalBiextMap
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.CanonGaugeNabValBaseChange

open scoped BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj Formalism.L2.FormalSeriesBounds NumberField

namespace GlobalTheory.ChartBaseChange

theorem isCanonGauge_mapFB {R k : Type} [CommRing R] [Algebra ℚ R] [CommRing k] [Algebra ℚ k]
    (f : R →+* k) {d : ℕ} {O : Type} [CommRing O] [StarRing O] (B : FB R d O) {h : PS R 2 d}
    (hg : B.IsCanonGauge R h) :
    (GlobalTheory.FBMap.mapFB f B).IsCanonGauge k (MvPowerSeries.map f h) := by
  letI : Algebra R k := f.toAlgebra
  have h1 : B.IsCanonGauge k (MvPowerSeries.map f h) :=
    GlobalTheory.GaugeBaseChange.isCanonGauge_map B (Algebra.ofId R k) hg
  have hid : ∀ {σ : Type} (g : MvPowerSeries σ k), MvPowerSeries.map (algebraMap k k) g = g := by
    intro σ g
    ext m
    simp [MvPowerSeries.coeff_map]
  have hF : (GlobalTheory.FBMap.mapFB f B).FK k = B.FK k := funext fun i => hid _
  have hA : ∀ a, (GlobalTheory.FBMap.mapFB f B).actK k a = B.actK k a := fun a => funext fun i => hid _
  refine ⟨h1.ax0, h1.ax1, ?_, ?_, ?_, fun a => ?_⟩
  · rw [hF, ← h1.ph1]; exact hid _
  · rw [hF, ← h1.ph2]; exact hid _
  · rw [← h1.sy]; exact hid _
  · rw [hA, hA, ← h1.ad a]; exact hid _

theorem intS_map {T : CDVR} {C : Type} [Field C] {V : VF C} {ι : T.Fr →+* C} (hι : EmbOK T V ι)
    {σ : Type} {g : MvPowerSeries σ T.Fr} {g0 : MvPowerSeries σ T.V}
    (hg : g = MvPowerSeries.map (algebraMap T.V T.Fr) g0) : IntS V (MvPowerSeries.map ι g) := by
  intro m
  rw [hg, MvPowerSeries.coeff_map, MvPowerSeries.coeff_map]
  exact (GlobalTheory.nval_eq_of_extension T C V.v V.l V.l_prime.ne_zero V.v_l ι hι).1 _

theorem exists_baseChange :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], Formalism.L2.FormalSeriesBounds.BCExSt Xo c := by
  intro E _ _ _ H Dw l Xo c _ T io y C3 C _ _ V ι hι hac hcpl hl hw k hk
  obtain ⟨gF, gA, g1, g2, gs, ga, -⟩ := C3.gen.1
  have hg : (a3B C3).IsCanonGauge T.Fr (a3h C3) := by
    letI := io.toAlgebra
    exact C3.ch.gauge
  obtain ⟨lg, ex, hlin, hadd, hc, hle, hel⟩ :=
    GlobalTheory.FormalLog.exists_log_exp C (chD C3.ch) (GlobalTheory.FBMap.mapFB ι (a3B C3)).G
  exact ⟨{ algClosed := hac
           cpl := hcpl
           l_odd := hl
           B := GlobalTheory.FBMap.mapFB ι (a3B C3)
           h := MvPowerSeries.map ι (a3h C3)
           gauge := isCanonGauge_mapFB ι (a3B C3) hg
           intF := fun i => intS_map hι (gF i)
           intAct := fun a i => intS_map hι (gA a i)
           intPh1 := intS_map hι g1
           intPh2 := intS_map hι g2
           intSy := intS_map hι gs
           intAd := fun a => intS_map hι (ga a)
           lg := lg
           lg_lin := hlin
           lg_add := hadd
           ex := ex
           ex_const := hc
           lg_ex := hle
           ex_lg := hel
           w0 := H.w0
           halfIntegralGenerator_add_conj_eq_one := hw
           k := k
           k_unit := hk },
    ⟨fun _ => rfl, fun _ _ => rfl, rfl, rfl, rfl, fun _ => rfl, rfl, rfl, rfl⟩⟩

end GlobalTheory.ChartBaseChange
