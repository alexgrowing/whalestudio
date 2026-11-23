import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PolyBetween
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LocalValuationColumns
import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralGermOnColumnsSameValueStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralGermOnCopiesSameValueStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsotropicFactorDepthEqSumFactorDepthsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalDepthOverDvrEqOverClosedFieldStatement
open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.PGsh
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1
open GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth GlobalTheory.PtTie GlobalTheory.PlaceInt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ColDepth

open GlobalTheory.FGDepth

section Ultra

variable {C : Type} [Field C] (v : AddValuation C (WithTop ℝ))

theorem val_eq_of_lt_sub (x y : C) (h : v x < v (x - y)) : v y = v x := by
  have h1 : min (v x) (v (x - y)) ≤ v (x - (x - y)) := AddValuation.map_sub v _ _
  rw [sub_sub_cancel, min_eq_left h.le] at h1
  have h2 : min (v y) (v (x - y)) ≤ v (y + (x - y)) := AddValuation.map_add v _ _
  rw [add_sub_cancel] at h2
  rcases le_total (v y) (v (x - y)) with h3 | h3
  · rw [min_eq_left h3] at h2
    exact le_antisymm h2 h1
  · rw [min_eq_right h3] at h2
    exact absurd (lt_of_le_of_lt h2 h) (lt_irrefl _)

theorem iInf_le_of_approx {S U : Type} (a : S → C) (b : U → C)
    (h : ∀ (s : S) (N : ℕ), ∃ t, ((N : ℝ) : WithTop ℝ) ≤ v (a s - b t)) :
    ⨅ t, toE (v (b t)) ≤ ⨅ s, toE (v (a s)) := by
  refine le_iInf fun s => ?_
  by_cases hs : v (a s) = ⊤
  · rw [hs]
    exact le_top
  · obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.1 hs
    obtain ⟨N, hN⟩ := exists_nat_gt r
    obtain ⟨t, ht⟩ := h s N
    have hlt : v (a s) < v (a s - b t) :=
      lt_of_lt_of_le (by rw [← hr]; exact WithTop.coe_lt_coe.2 hN) ht
    rw [← val_eq_of_lt_sub v _ _ hlt]
    exact iInf_le _ t

theorem iInf_eq_of_approx {S U : Type} (a : S → C) (b : U → C)
    (h1 : ∀ (s : S) (N : ℕ), ∃ t, ((N : ℝ) : WithTop ℝ) ≤ v (a s - b t))
    (h2 : ∀ (t : U) (N : ℕ), ∃ s, ((N : ℝ) : WithTop ℝ) ≤ v (a s - b t)) :
    ⨅ s, toE (v (a s)) = ⨅ t, toE (v (b t)) := by
  refine le_antisymm ?_ (iInf_le_of_approx v a b h1)
  refine iInf_le_of_approx v b a fun t N => ?_
  obtain ⟨s, hs⟩ := h2 t N
  exact ⟨s, by rwa [AddValuation.map_sub_swap]⟩

end Ultra

theorem nuLocOf_eq_nuP : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (p : ℕ) [Fact p.Prime] (la : PointsOfFlagModel.abelian₂ p c) (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ), OverLa la.1 T.V io e → ∀ (y : IntFr Xo c T io) (Ch : IntegralChartA3 Xo c T io y) (cx : Lt1 Dw → ℕ) (n : ℕ) (B : ∀ f : Lt1 Dw, Fin (rk f) → Fin n → T.V), IsCols c T io p cx B → ∀ k : ℕ, nuLocOf Ch (vV T.V (p : T.Fr)).toNat k (polyT B cx) = nuP p y cx := by
  intro E _ _ _ H Dw l Xo c p _ la T io e ho y Ch cx n B hB k
  letI := H.starRing
  obtain ⟨X⟩ := nonempty_valExt_of_overLa la ho
  have hmid : GlobalTheory.IndefiniteRowSideFullHecke.LocalValuationColumns.nuLocX_vp Ch X cx B k = GlobalTheory.IndefiniteRowSideFullHecke.LocalValuationColumns.nuH_vp Ch X cx := by
    unfold GlobalTheory.IndefiniteRowSideFullHecke.LocalValuationColumns.nuLocX_vp GlobalTheory.IndefiniteRowSideFullHecke.LocalValuationColumns.nuH_vp depth
    refine iInf_eq_of_approx (vX_vp X)
      (fun g : {g : PS X.C n (chD Ch.ch) // MvIsInt (vX_vp X) g} => GlobalTheory.IndefiniteRowSideFullHecke.LocalValuationColumns.nabX Ch X cx B k g.1)
      (fun f : {f : MvPowerSeries (Σ _ : GlobalTheory.IndefiniteRowSideFullHecke.LocalValuationColumns.Col cx, Fin (chD Ch.ch)) X.C // MvIsInt (vX_vp X) f} =>
        derivAt0 (GlobalTheory.IndefiniteRowSideFullHecke.LocalValuationColumns.polyH X.C cx) (MvPowerSeries.subst (GlobalTheory.IndefiniteRowSideFullHecke.LocalValuationColumns.expH Ch X cx) f.1))
      (fun g N => ?_) (fun f N => ?_)
    · obtain ⟨f, hf, hN⟩ := GlobalTheory.T.exists_integral_germ_on_columns_same_value E H Dw l Xo c p la T io e ho y Ch X cx n B hB N k g.1 g.2
      exact ⟨⟨f, hf⟩, hN⟩
    · obtain ⟨g, hg, hN⟩ := GlobalTheory.T.exists_integral_germ_on_copies_same_value E H Dw l Xo c p la T io e ho y Ch X cx n B hB N k f.1 f.2
      exact ⟨⟨g, hg⟩, hN⟩
  exact (GlobalTheory.T.localDepth_over_dvr_eq_over_closed_field E H Dw l Xo c p la T io e ho y Ch X cx n B k).trans
    (hmid.trans (GlobalTheory.T.isotropicFactor_depth_eq_sum_factor_depths E H Dw l Xo c p T io y Ch X cx).1)

end GlobalTheory.ColDepth
