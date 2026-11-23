import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelSt
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DemaillyRegularisation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.MatrixLemma
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuasiPlurisubharmonic
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LieAlgebraMaps
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiFibrationLieLatticeFullStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StepLatZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinPart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiFibLieLatticeFull
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartierLogHeightFormula
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticePadicGradingDetStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullLatticePrimeToPBasisStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PAdicProductFormulaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumPadicValNatLogEqLogStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IoOfLeOneIff
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdmissibleRepresentationFactorisation
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HodgeMetricUniformisationSmoothOnInterior
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearLiftPreservingAppellHumbertForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexFibreIsoUniversalGroupFramedPoint

noncomputable section

section SlopeTestRemainingChoices

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Limits MonoidalCategory CartesianMonoidalCategory MonObj

namespace GlobalTheory.HodgeFibIso

theorem exists_hom {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
    (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β) (p : Sp ℂ ⟶ Xo.XF c) (x : Sp ℂ ⟶ Xo.X) (hbase : x = p ≫ pullback.fst _ _)
    (Q : ReciprocityTheory.ChartRestriction.G.Out.PolAV (Sp ℂ)) (χ : Q.A.left ⟶ Z.t.G.left)
    (hcomp : IsGrpPullback Q.A Z.t.G (p ≫ Z.jQ ≫ pullback.fst _ _) χ) (hL : LBIso (Z.t.PP.L.pull χ) Q.L)
    (T : GlobalTheory.CM.PAT H (Sp ℂ)) (m : SABMap T.t Xo.univ.t x) :
    ∃ f : Q.A ⟶ T.pol.A, IsMonHom f ∧ LBIso (lbPow (T.pol.L.pull f.left) 1) (lbPow Q.L 1) ∧
      ∀ (a : epsR ℂ ⟶ Q.A) (w : Sp (DualNumber ℂ) ⟶ Z.oF.t.G.left) (w' : epsR ℂ ⟶ T.pol.A),
        w ≫ Z.oF.t.G.hom = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ p → w ≫ Z.m.φ = a.left ≫ χ →
        w'.left ≫ m.φ = w ≫ Z.m0.toSABMap.φ → a ≫ f = w' := by
  have w0 : χ ≫ Z.t.G.hom = (Q.A.hom ≫ p) ≫ Z.jQ ≫ pullback.fst _ _ := by
    rw [hcomp.1.w, Category.assoc]
  let χ₀ : Q.A.left ⟶ Z.oF.t.G.left := Z.m.cart.1.lift χ (Q.A.hom ≫ p) w0
  have hχ₀2 : χ₀ ≫ Z.m.φ = χ := Z.m.cart.1.lift_fst _ _ w0
  have hχ₀b : χ₀ ≫ Z.oF.t.G.hom = Q.A.hom ≫ p := Z.m.cart.1.lift_snd _ _ w0
  have hχ₀ : IsGrpPullback Q.A Z.oF.t.G p χ₀ :=
    Z.m.cart.cancel (by rw [show χ₀ ≫ Z.m.cm.F = χ from hχ₀2]; exact hcomp) hχ₀b
  let m1 := Z.m0.toSABMap
  have hχ := hχ₀.comp m1.cart
  have w1 : (χ₀ ≫ m1.φ) ≫ Xo.univ.t.G.hom = Q.A.hom ≫ x := by rw [hbase]; exact hχ.1.w
  let fl : Q.A.left ⟶ T.t.G.left := m.cart.1.lift (χ₀ ≫ m1.φ) Q.A.hom w1
  have hfl : fl ≫ m.φ = χ₀ ≫ m1.φ := m.cart.1.lift_fst _ _ w1
  have hflb : fl ≫ T.t.G.hom = Q.A.hom := m.cart.1.lift_snd _ _ w1
  let f : Q.A ⟶ T.pol.A := Over.homMk fl hflb
  refine ⟨f, ?_, ?_, ?_⟩
  · refine GlobalTheory.DivisibleHom.isMonHom_of_mul_points f fun S x y => ?_
    apply Over.OverMorphism.ext
    apply m.cart.1.hom_ext
    · have e1 := hχ.2 S x y (pushPt hχ.1.w x) (pushPt hχ.1.w y) rfl rfl
      have e2 := m.cart.2 S (x ≫ f) (y ≫ f) (pushPt m.cart.1.w (x ≫ f)) (pushPt m.cart.1.w (y ≫ f)) rfl rfl
      rw [Over.comp_left, Category.assoc]
      change _ ≫ fl ≫ m.φ = _
      rw [hfl, ← e1, ← e2]
      refine mul_left_congr (by rw [hbase]) _ _ _ _ ?_ ?_
      · show x.left ≫ χ₀ ≫ m1.φ = (x.left ≫ fl) ≫ m.φ
        rw [Category.assoc, hfl]
      · show y.left ≫ χ₀ ≫ m1.φ = (y.left ≫ fl) ≫ m.φ
        rw [Category.assoc, hfl]
    · exact (Over.w ((x * y) ≫ f)).trans (Over.w ((x ≫ f) * (y ≫ f))).symm
  · obtain ⟨wT, hwT, -⟩ := m.lin
    obtain ⟨w1', hw1', -⟩ := m1.lin
    obtain ⟨w2', hw2', -⟩ := Z.m.lin
    have hT : LBIso T.t.PP.L (Xo.univ.t.PP.L.pull m.φ) := ⟨wT, hwT⟩
    have h1 : LBIso Z.oF.t.PP.L (Xo.univ.t.PP.L.pull m1.φ) := ⟨w1', hw1'⟩
    have h2 : LBIso Z.oF.t.PP.L (Z.t.PP.L.pull Z.m.φ) := ⟨w2', hw2'⟩
    have hT2 := GlobalTheory.CM.EllComp.lbIso_pull_comp hT.symm fl
    rw [hfl] at hT2
    have h3 := GlobalTheory.CM.EllComp.lbIso_pull_comp h1.symm χ₀
    have h4 := GlobalTheory.CM.EllComp.lbIso_pull_comp h2.symm χ₀
    rw [hχ₀2] at h4
    have e345 := LBIso.trans (pull_isLB Z.oF.t.PP.isLB χ₀) (pull_isLB Z.t.PP.isLB _) Q.isLB h4.symm hL
    have e2345 := LBIso.trans (pull_isLB Xo.univ.t.PP.isLB _) (pull_isLB Z.oF.t.PP.isLB χ₀) Q.isLB h3 e345
    have main : LBIso (T.t.PP.L.pull fl) Q.L :=
      LBIso.trans (pull_isLB T.t.PP.isLB fl) (pull_isLB Xo.univ.t.PP.isLB _) Q.isLB hT2.symm e2345
    exact GlobalTheory.lbIso_lbPow main 1
  · intro a w w' hwb hwm hw'
    have key : a.left ≫ χ₀ = w := by
      apply Z.m.cart.1.hom_ext
      · rw [Category.assoc]
        exact (congrArg (a.left ≫ ·) hχ₀2).trans hwm.symm
      · rw [Category.assoc, hχ₀b, hwb, ← Category.assoc, Over.w a]
        rfl
    apply Over.OverMorphism.ext
    apply m.cart.1.hom_ext
    · refine Eq.trans ?_ hw'.symm
      change (a.left ≫ fl) ≫ m.φ = _
      rw [Category.assoc, hfl, ← Category.assoc, key]
    · exact (Over.w (a ≫ f)).trans (Over.w w').symm

theorem isCombAt_unique {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {S : Type} [CommRing S] {x : Sp S ⟶ Xo.X} {n : ℕ}
    {v : Fin n → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)} {C : Fin n → S}
    {w w' : Sp (DualNumber S) ⟶ Xo.univ.t.G.left} (h : Formalism.L2.Pj.IsCombAt x v C w) (h' : Formalism.L2.Pj.IsCombAt x v C w') :
    w = w' := by
  obtain ⟨a, ha, rfl⟩ := h
  obtain ⟨b, hb, rfl⟩ := h'
  have hab : a = b := funext fun k => Over.OverMorphism.ext ((ha k).trans (hb k).symm)
  rw [hab]

end GlobalTheory.HodgeFibIso

end SlopeTestRemainingChoices

open NumberField Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.LieHt GlobalTheory.HeightParts
open GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LieRead
open AlgebraicGeometry CategoryTheory IsDedekindDomain GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.Cartier
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal

end
