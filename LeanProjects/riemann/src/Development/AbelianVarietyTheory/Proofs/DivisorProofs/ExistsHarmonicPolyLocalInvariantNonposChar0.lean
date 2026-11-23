import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PhiAt
import Development.AbelianVarietyTheory.Definitions.Divisors.PolyBetween
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaExponentsDominantLastEntryOneDegree
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaRulesExistAndCusp
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsIsNabUncond
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.StarRingExtOfStar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExtensionUniformisedChartScale
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExtensionDvrFlagLift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IInfThRuleLeNuLocOf
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.HarmonicValueTranslateAny
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.HarmonicValueTranslateEqUnitMulNormaliserThetaVa
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.PointStatementsOnCopiesHoldStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsShortPeriodLatticeBasisBalancedSlope
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsProductDataCopiesTrivialisationValuation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseLocusExponentLeOscillationNonTypePrime
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightAntitoneBoundary
import Development.AbelianVarietyTheory.Definitions.Divisors.EightDvdNCol
import Formalism.LocalToGlobal.ProjectiveLattices.ConjNeSelfOfCM
import Formalism.LocalToGlobal.ProjectiveLattices.SatLeaves
import Formalism.LocalToGlobal.ProjectiveLattices.DepRun
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open IsLocalRing Formalism.MainNotions.ModuliIntegralCharts.H1 ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth

namespace GlobalTheory.ResZeroDepth

theorem exists_harmA_nuLocOf_nonpos : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), (∀ τ, Antitone fun i => a (τ, i)) → ∑ f : Lt1 Dw, 2 * rk f ≤ n → ∃ P₁ ∈ harmA (Dw := Dw) c a n, ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y), CharZero (IsLocalRing.ResidueField T.V) → ∀ e k : ℕ, 0 < e → GlobalTheory.FactorDepth.nuLocOf C e k (MvPolynomial.map io P₁) ≤ 0 := by
  intro E _ _ _ H Dw l Xo c
  letI := H.starRing
  intro a n ha hn
  classical
  have hcard : Fintype.card (Lt1 Dw) ≤ n := by
    refine le_trans ?_ hn
    rw [Fintype.card_eq_sum_ones]
    exact Finset.sum_le_sum fun f _ => by unfold rk; omega
  have hdom : Formalism.L2.Pj.DomW Dw a := fun τ i j hij => ha τ hij
  have hinj : Function.Injective (Formalism.L2.Pj.colP Dw hcard) := fun p q h =>
    (Fintype.equivFin _).injective (Fin.castLE_injective hcard h)
  refine ⟨MvPolynomial.map (Int.castRingHom c.F)
      (Formalism.L2.Pj.Crude.Pmin Dw.mult n (Formalism.L2.Pj.colP Dw hcard) fun τ i => a (τ, i)),
    Formalism.L2.Pj.Crude.Pmin_mem Dw.mult n c.F _ _ _ _ _ (fun τ _ => Formalism.L2.Pj.conj_ne_self_of_CM τ) hinj hdom, ?_⟩
  intro T io y C hres e k _
  letI := io.toAlgebra
  have hmap : MvPolynomial.map io (MvPolynomial.map (Int.castRingHom c.F)
      (Formalism.L2.Pj.Crude.Pmin Dw.mult n (Formalism.L2.Pj.colP Dw hcard) fun τ i => a (τ, i))) =
      Formalism.L2.Pj.P1 Dw T a hcard := by
    rw [MvPolynomial.map_map, RingHom.ext_int (io.comp _) (Int.castRingHom T.Fr)]
    rfl
  obtain ⟨-, f, hf, -, hv⟩ := Formalism.L2.Pj.crude_val C.ch.B C.ch.h C.ch.gauge H.w0 k C.ch.uvec
    (Formalism.L2.Pj.satDir_of Formalism.L2.Pj.chart_saturated C) a n hdom hcard
  rw [hmap]
  refine le_trans (iInf_le_of_le f (iInf_le_of_le hf (le_of_eq (congrArg (Formalism.L2.Pj.nval T.V e) hv)))) ?_
  set N := Formalism.L2.Pj.fact1 Dw a hcard with hN
  have hN0 : N ≠ 0 := by
    rw [hN]; unfold Formalism.L2.Pj.fact1
    exact Finset.prod_ne_zero_iff.2 fun _ _ => Nat.factorial_ne_zero _
  have hu : IsUnit ((N : ℕ) : T.V) := by
    refine (IsLocalRing.residue_ne_zero_iff_isUnit _).1 ?_
    rw [map_natCast]
    exact Nat.cast_ne_zero.2 hN0
  have hne : ((N : ℕ) : T.Fr) ≠ 0 := by
    rw [← map_natCast (algebraMap T.V T.Fr)]
    exact (map_ne_zero_iff _ (IsFractionRing.injective T.V T.Fr)).2 hu.ne_zero
  have hv0 : Formalism.L2.Pj.vV T.V ((N : ℕ) : T.Fr) = 0 := by
    rw [← map_natCast (algebraMap T.V T.Fr)]
    exact GlobalTheory.RefSum.GlobalPoly.vV_of_isUnit T hu
  rw [Formalism.L2.Pj.nval_of_ne hne, hv0]
  simp

end GlobalTheory.ResZeroDepth
