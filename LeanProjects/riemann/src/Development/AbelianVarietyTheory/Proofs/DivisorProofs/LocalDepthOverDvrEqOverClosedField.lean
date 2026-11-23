import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.NabValNEqSumCoeff
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsCombinationIntegers
import Development.AbelianVarietyTheory.Definitions.Divisors.PolyBetween
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LocalValuationColumns
import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.PGsh
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1
open GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth GlobalTheory.PtTie GlobalTheory.PlaceInt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.DepthDescent

open GlobalTheory.IndefiniteRowSideFullHecke.LocalValuationColumns

theorem nuLocOf_eq_nuLocX_vp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (p : ℕ) [Fact p.Prime] (la : PointsOfFlagModel.abelian₂ p c) (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ), OverLa la.1 T.V io e → ∀ (y : IntFr Xo c T io) (Ch : IntegralChartA3 Xo c T io y) (X : ValExt T p) (cx : Lt1 Dw → ℕ) (n : ℕ) (B : ∀ f : Lt1 Dw, Fin (rk f) → Fin n → T.V), ∀ k : ℕ, nuLocOf Ch (vV T.V (p : T.Fr)).toNat k (polyT B cx) = GlobalTheory.IndefiniteRowSideFullHecke.LocalValuationColumns.nuLocX_vp Ch X cx B k := by
  intro E _ _ _ H Dw l Xo c
  letI := H.starRing
  intro p _ la T io e ho y Ch X cx n B k
  have hp0 : 0 ≤ vV T.V (p : T.Fr) := by
    have := GlobalTheory.vV_algebraMap_nonneg_dvr T (p : T.V)
    rwa [map_natCast] at this
  have he : vV T.V (p : T.Fr) = (((vV T.V (p : T.Fr)).toNat : ℕ) : ℤ) := (Int.toNat_of_nonneg hp0).symm
  letI := io.toAlgebra
  letI : Algebra T.Fr X.C := X.ιF.toAlgebra
  have hh : MvPowerSeries.constantCoeff Ch.ch.h = 0 :=
    ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.coeff_eq_zero_of_vanish_first_axis _ Ch.ch.gauge.ax0 0 fun _ => rfl
  have hu : (fun (ℓ : LtN Dw n) => lieVec Ch X ⟨ℓ.1, ℓ.2.1⟩) =
      fun ℓ j => X.ιF (Ch.ch.uvec ⟨ℓ.1, ℓ.2.1⟩ j) := by
    funext ℓ j
    simp only [lieVec, jX, RingHom.comp_apply]
    rw [Ch.gen.1.2.2.2.2.2.2]
  have himg : ∀ f : PS T.Fr n (chD Ch.ch), nabX Ch X cx B k (MvPowerSeries.map X.ιF f) =
      X.ιF (nabValN Ch.ch.B T.Fr Ch.ch.h H.w0 k f (fun ℓ : LtN Dw n => ℓ.2.2)
        (fun ℓ => Ch.ch.uvec ⟨ℓ.1, ℓ.2.1⟩) (polyT B cx)) := by
    intro f
    unfold nabX
    rw [hu]
    exact GlobalTheory.ThetaLeast.nabValN_algebraMap T.Fr X.C _ _ Ch.ch.B Ch.ch.h hh H.w0 k n f _ _ _ _
  have hB : ∀ g : PS X.C n (chD Ch.ch), nabX Ch X cx B k g =
      nabValN (GlobalTheory.FBMap.mapFB X.ιF Ch.ch.B) X.C (MvPowerSeries.map X.ιF Ch.ch.h) H.w0 k g
        (fun ℓ : LtN Dw n => ℓ.2.2) (fun ℓ => lieVec Ch X ⟨ℓ.1, ℓ.2.1⟩)
        (MvPolynomial.map X.ιF (polyT B cx)) := by
    intro g
    have h1 : (GlobalTheory.FBMap.mapFB X.ιF Ch.ch.B).FK X.C = Ch.ch.B.FK X.C := by
      funext i
      ext μ
      simp [FB.FK, FGLaw.mapF, GlobalTheory.FBMap.mapFB, GlobalTheory.FBMap.mapLaw, GlobalTheory.FBMap.mapPt, RingHom.algebraMap_toAlgebra]
    have h2 : ∀ b, (GlobalTheory.FBMap.mapFB X.ιF Ch.ch.B).actK X.C b = Ch.ch.B.actK X.C b := by
      intro b
      funext i
      ext μ
      simp [FB.actK, GlobalTheory.FBMap.mapFB, GlobalTheory.FBMap.mapAct, GlobalTheory.FBMap.mapPt, RingHom.algebraMap_toAlgebra]
    unfold nabX nabValN FB.hL
    rw [h1, h2]
  apply le_antisymm
  · unfold nuLocX_vp
    refine le_iInf fun g => ?_
    obtain ⟨S, hS⟩ := GlobalTheory.nabValN_eq_sum_coeff X.C _ _ (GlobalTheory.FBMap.mapFB X.ιF Ch.ch.B)
      (MvPowerSeries.map X.ιF Ch.ch.h) H.w0 k n (LtN Dw n) (fun ℓ : LtN Dw n => ℓ.2.2)
      (fun ℓ => lieVec Ch X ⟨ℓ.1, ℓ.2.1⟩) (MvPolynomial.map X.ιF (polyT B cx))
    have hμ : ∀ μ, nuLocOf Ch (vV T.V (p : T.Fr)).toNat k (polyT B cx) ≤
        toE (vX_vp X (nabX Ch X cx B k (MvPowerSeries.monomial μ (1 : X.C)))) := by
      intro μ
      have hmon : (MvPowerSeries.monomial μ (1 : X.C) : PS X.C n (chD Ch.ch))
          = MvPowerSeries.map X.ιF (MvPowerSeries.monomial μ (1 : T.Fr) : PS T.Fr n (chD Ch.ch)) := by
        rw [MvPowerSeries.map_monomial, map_one X.ιF]
      rw [hmon, himg, toE_vX_vp_ιF X he]
      unfold nuLocOf
      refine iInf₂_le_of_le (MvPowerSeries.monomial μ (1 : T.Fr)) (fun ρ => ?_) le_rfl
      classical
      rw [MvPowerSeries.coeff_monomial]
      split_ifs
      · exact Subring.one_mem _
      · exact Subring.zero_mem _
    rw [hB, hS g.1]
    simp only [← hB]
    generalize nuLocOf Ch (vV T.V (p : T.Fr)).toNat k (polyT B cx) = ν at hμ ⊢
    induction ν using WithBot.recBotCoe with
    | bot => exact bot_le
    | coe w =>
      refine WithBot.coe_le_coe.2 ?_
      refine (vX_vp X).map_le_sum fun μ _ => ?_
      rw [(vX_vp X).map_mul]
      exact le_trans (WithBot.coe_le_coe.1 (hμ μ)) (le_add_of_nonneg_left (g.2 μ))
  · unfold nuLocOf nuLocX_vp
    refine le_iInf₂ fun f hf => ?_
    refine iInf_le_of_le ⟨MvPowerSeries.map X.ιF f, fun α => ?_⟩ (le_of_eq ?_)
    · obtain ⟨t, ht⟩ := hf α
      rw [MvPowerSeries.coeff_map, ← ht]
      exact isIntV_jX X t
    · rw [himg, toE_vX_vp_ιF X he]

end GlobalTheory.DepthDescent
