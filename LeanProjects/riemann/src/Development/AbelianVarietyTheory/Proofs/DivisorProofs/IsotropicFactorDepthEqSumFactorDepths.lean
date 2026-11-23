import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PolyBetween
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LocalValuationColumns
import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetFactorDepthEqChartValueAndSumStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetProductDepthInChartEqSumFactorDepths
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentialOperatorDepthRestrictColumns
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupDeterminantPowDepthBoundsStatement
open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.PGsh
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1
open GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth GlobalTheory.PtTie GlobalTheory.PlaceInt
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.IsoFactorDepth

open GlobalTheory.IndefiniteRowSideFullHecke.LocalValuationColumns in

def colEmb {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
    (cx : Lt1 Dw → ℕ) : Col cx ↪ (Σ f : Lt1 Dw, Fin (rk f)) where
  toFun b := ⟨b.1.1, b.2⟩
  inj' := by
    rintro ⟨⟨f, hf⟩, a⟩ ⟨⟨g, hg⟩, b⟩ h
    simp only [Sigma.mk.inj_iff] at h
    obtain ⟨rfl, h⟩ := h
    cases h
    rfl

open GlobalTheory.IndefiniteRowSideFullHecke.LocalValuationColumns in

theorem prodP_eq_rename_polyH {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} (C : Type) [Field C] (cx : Lt1 Dw → ℕ) :
    prodP C cx = MvPolynomial.rename (fun x : Let cx =>
      (⟨colEmb cx x.1, x.2⟩ : Σ b : (Σ f : Lt1 Dw, Fin (rk f)), Fin (rk b.1))) (polyH C cx) := by
  classical
  unfold prodP polyH
  rw [map_prod]
  simp_rw [MvPolynomial.rename_rename]
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun f : Lt1 Dw => cx f ≠ 0)]
  have h1 : ∏ f : {f : Lt1 Dw // ¬ cx f ≠ 0}, MvPolynomial.rename (fun ℓ : (Σ _ : Fin (rk f.1), Fin (rk f.1)) =>
      (⟨⟨f.1, ℓ.1⟩, ℓ.2⟩ : Σ b : (Σ f : Lt1 Dw, Fin (rk f)), Fin (rk b.1))) (GlobalTheory.FGDepth.detPow C (rk f.1) (cx f.1)) = 1 := by
    refine Finset.prod_eq_one fun f _ => ?_
    have h0 : cx f.1 = 0 := not_not.1 f.2
    rw [GlobalTheory.FGDepth.detPow, h0, pow_zero, map_one]
  rw [h1, mul_one]
  rfl

theorem nuH_vp_eq_nuP : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (p : ℕ) [Fact p.Prime] (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (Ch : IntegralChartA3 Xo c T io y) (X : ValExt T p) (cx : Lt1 Dw → ℕ), GlobalTheory.IndefiniteRowSideFullHecke.LocalValuationColumns.nuH_vp Ch X cx = nuP p y cx ∧ 0 ≤ nuP p y cx ∧ nuP p y cx ≠ ⊤ := by
  intro E _ _ _ H Dw l Xo c
  classical
  letI := H.starRing
  intro p _ T io y Ch X cx
  have hfac := (GlobalTheory.T.detFactorDepth_eq_chart_value_and_sum E H Dw l Xo c p T io y Ch X).1
  have hsum : nuP p y cx = ∑ f, nuFacC Ch X f (cx f) :=
    Finset.sum_congr rfl fun f _ => hfac f (cx f)
  have hbd : ∀ f, 0 ≤ nuFacC Ch X f (cx f) ∧
      nuFacC Ch X f (cx f) ≤ ((((rk f * cx f : ℕ) : ℝ) / (p - 1) : ℝ) : EReal) := fun f => by
    have h := GlobalTheory.T.formalGroupDeterminantPowDepth_bounds X.C (vX_vp X) p Fact.out (vX_vp_p X) (rk f) (chD Ch.ch) (cx f) (fgl Ch X)
      (frame Ch X f) (isSatFrame_frame Ch X f)
    refine ⟨h.1, h.2.2.trans (le_of_eq ?_)⟩
    push_cast; rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [hsum, ← GlobalTheory.FactorDepthProd.nuProdC_eq_sum]
    unfold nuProdC GlobalTheory.IndefiniteRowSideFullHecke.LocalValuationColumns.nuH_vp
    rw [prodP_eq_rename_polyH]
    exact (GlobalTheory.FGDepth.depth_restrict X.C (vX_vp X) (Σ f : Lt1 Dw, Fin (rk f)) (fun _ => chD Ch.ch)
      (fun _ => fgl Ch X) (fun b => Fin (rk b.1)) (fun b => frame Ch X b.1) (GlobalTheory.IndefiniteRowSideFullHecke.LocalValuationColumns.Col cx)
      (colEmb cx) (GlobalTheory.IndefiniteRowSideFullHecke.LocalValuationColumns.polyH X.C cx)).symm
  · rw [hsum]
    exact Finset.sum_nonneg fun f _ => (hbd f).1
  · rw [hsum]
    have hreal : ∃ r : ℝ, ∑ f, nuFacC Ch X f (cx f) = (r : EReal) := by
      refine Finset.sum_induction _ (fun x : EReal => ∃ r : ℝ, x = r) ?_ ⟨0, rfl⟩ ?_
      · rintro a b ⟨r, rfl⟩ ⟨s, rfl⟩
        exact ⟨r + s, (EReal.coe_add r s).symm⟩
      · intro f _
        have h0 := (hbd f).1
        have h1 := (hbd f).2
        refine ⟨(nuFacC Ch X f (cx f)).toReal, (EReal.coe_toReal ?_ ?_).symm⟩
        · exact ne_top_of_le_ne_top (EReal.coe_ne_top _) h1
        · exact ne_bot_of_le_ne_bot (by simp) h0
    obtain ⟨r, hr⟩ := hreal
    rw [hr]
    exact EReal.coe_ne_top r

end GlobalTheory.IsoFactorDepth
