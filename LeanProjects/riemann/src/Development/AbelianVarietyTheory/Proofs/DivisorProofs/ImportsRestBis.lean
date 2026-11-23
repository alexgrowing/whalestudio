import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsFiniteExtPelUnif
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsFormalGroupJetsChart
import Formalism.LocalToGlobal.CharacterGerms.RowTieUpFBrFin

open NumberField IsLocalRing Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF

attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory

namespace GlobalTheory.IntegralChartCover

theorem cover : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (lv : Level H) (Xo : Moduli Dw lv) (c : Coeff lv) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C3 : IntChart T io y), ∃ (T' : CDVR) (φ : T.V →+* T'.V) (t' : SAB H (Sp T'.V)), Function.Injective φ ∧ φ.Finite ∧ UpFBr.GeoJ T'.V t'.G (𝓞 E) (fun a => t'.act.act a) (chD C3.ch) (fun i => MvPowerSeries.map φ (C3.FT i)) (fun a i => MvPowerSeries.map φ (C3.actT a i)) := by
  intro E _ _ _ H Dw lv Xo c inst hstar T io y C3
  obtain rfl : inst = H.starRing := GlobalTheory.PowGerm.starRing_ext_of_star inst H.starRing hstar
  letI := H.starRing
  letI := io.toAlgebra
  obtain ⟨T', φ, t', m, hi, hf, ⟨P⟩⟩ := GlobalTheory.ChartCharacters.exists_finite_ext_pelUnif Xo T C3.I.G C3.I.t' C3.I.m2 _ C3.I.m1
  obtain ⟨F', x', act', hF, hA, hx, ha⟩ := GlobalTheory.integralChart_baseChange E H Dw lv Xo c T io y C3 T' φ t' m
  exact ⟨T', φ, t', hi, hf, P.D, P.A, P.U.toUnifPre, F', x', _, t'.act.toRingAct, P.oD, P.oA, act', hF, funext hA, fun _ => rfl, hx, P.lin, ha⟩

end GlobalTheory.IntegralChartCover
