import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagInduces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DimEqDimGrAdd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLieBase
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagInducesOfLieBase
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleExistsArithmeticVarietyAltBis
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagBaseEx

theorem exists_base_flagInduces : Hypotheses2 → HypothesesH → RegularAlteration → ScholzeWeinsteinB →
  ∀ (D : D7) (O : Setup D), O.Core → ∀ B : ℝ, 2 ≤ B → ∀ R : ℝ, 2 ≤ R → ∀ c : O.s.Comp,
  ∃ (Bs : Scheme.{0}) (_ : IsIntegral Bs) (q : Bs ⟶ Sp (𝓞 D.what₂.LL)) (_ : IsArithVar q (dimGr D.what₂.Tau O.N O.j))
    (_ : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Bs) (E : D.what₂.Tau × Bool → Bs.Modules)
    (h : ∀ a, VMetric q (E a) (rkB D.what₂.Tau O.N O.j a)) (H : ∀ a, (h a).IsCInf)
    (Y₀ : Scheme.{0}) (_ : IsIntegral Y₀) (π₀ : Y₀ ⟶ Bs)
    (fl₀ : ∀ a, Vert.Flag ((Scheme.Modules.pullback π₀).obj (E a)) (rkB D.what₂.Tau O.N O.j a))
    (_ : IsFlagBundle π₀ E (rkB D.what₂.Tau O.N O.j) fl₀) (ar₀ : IsArithVar (π₀ ≫ q) (O.var c).dim)
    (n₀ : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Y₀),
    GlobalTheory.FlagInd.FlagInduces (O.var c) q E (rkB D.what₂.Tau O.N O.j) h H
      (fun a i => adlOf (O.Φ.C c) (O.met.hm c)
        (rootSym O.S.Dw (ArIn.ind (setB O.Y B)) (some R) (DV.tauEmb D a.1) (cond a.2 0 O.j + i))) Y₀ π₀ fl₀ ar₀ n₀ := by
  intro p1 p2 p3 p4 D O hO B hB R hR c
  obtain ⟨Bs, iB, q, aq, nB, E, h, H, hL⟩ := GlobalTheory.ArLieBase.exists_lieBase D O hO B R hR c
  obtain ⟨Y, iY, π, fl, hfb, ar, nY⟩ := GlobalTheory.T.exists_normal_isFlagBundle_isArithVar (𝓞 D.what₂.LL) Bs q _ aq nB (D.what₂.Tau × Bool) E
    (rkB D.what₂.Tau O.N O.j) (fun a => (h a).isVB)
  have ar' : IsArithVar (π ≫ q) (O.var c).dim := by
    rw [← GlobalTheory.FlagBlockDim.dim_eq_dimGr_add O c]
    convert ar
  exact ⟨Bs, iB, q, aq, nB, E, h, H, Y, iY, π, fl, hfb, ar', nY,
    GlobalTheory.FlagCov.flagInduces_of_lieBase p1 p2 p3 p4 D O hO B hB R hR c Bs q aq nB E h H hL Y π fl hfb ar' nY⟩

end GlobalTheory.FlagBaseEx

end
