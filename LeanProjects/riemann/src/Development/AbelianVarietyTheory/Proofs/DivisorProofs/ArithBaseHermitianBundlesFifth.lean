import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieBaseIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieBaseAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightWeightRootChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedFramePartitionFormulaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalFunctionValueCompatibleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieGenericEigenMetricSetupStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieGenericEigenMetricBoundStatement
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ArLieBase
open GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.BcReadCx

theorem frameSec_norm_cx : Hypotheses2 → HypothesesH → RegularAlteration →
  ∀ (D : D7) (O : Setup D) (hO : O.Core) (P : Finset ℕ) (R : ℝ) (hR : 2 ≤ R) (c : O.s.Comp)
    (Bs : Scheme.{0}) [IsIntegral Bs] (q : Bs ⟶ Sp (𝓞 D.what₂.LL)) (arq : IsArithVar q (dimGr D.what₂.Tau O.N O.j))
    (nBs : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Bs) (E : D.what₂.Tau × Bool → Bs.Modules)
    (h : ∀ a, VMetric q (E a) (rkB D.what₂.Tau O.N O.j a)) (H : ∀ a, (h a).IsCInf)
    (Bg : Scheme.{0}) (jB : Bg ⟶ Bs) (πB : Bg ⟶ gen O.s.T.Z)
    (u : ∀ a, FrAssign O.s.T.Z (E a) (rkB D.what₂.Tau O.N O.j a) jB)
    (hG : GlobalTheory.BcRead.LieGen O c q E jB πB u) (hF : GlobalTheory.BcRead.LieFin O P E jB πB u)
    (hI : GlobalTheory.BcRead.LieInf O R c q E h jB πB u)
    (Y₀ : Scheme.{0}) [IsIntegral Y₀] (π₀ : Y₀ ⟶ Bs)
    (fl₀ : ∀ a, Vert.Flag ((Scheme.Modules.pullback π₀).obj (E a)) (rkB D.what₂.Tau O.N O.j a))
    (hfb : IsFlagBundle π₀ E (rkB D.what₂.Tau O.N O.j) fl₀) (ar₀ : IsArithVar (π₀ ≫ q) (O.var c).dim)
    (n₀ : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Y₀) (G : Scheme.{0}) [IsIntegral G] (j : G ⟶ Y₀) (πG : G ⟶ (O.var c).X)
    (pb : IsPullback j (πG ≫ (O.var c).str) (π₀ ≫ q) (spMap (algebraMap (𝓞 D.what₂.LL) D.what₂.LL)))
    [IsFinite πG] [Surjective πG] (φ : (O.var c).Fn →+* G.functionField)
    (φs : G.fromSpecStalk (genericPoint G) ≫ πG = spMap φ ≫ (O.var c).X.fromSpecStalk (genericPoint (O.var c).X))
    (jG : G ⟶ Bg) (r : ∀ a i, (((fl₀ a).root i).pull j).ι → G.functionFieldˣ)
    (hc : GlobalTheory.FlagCov.FlagCover (fun a => (h a).isVB) jB πB u π₀ fl₀ j πG φ jG r)
    (a : D.what₂.Tau × Bool) (i : Fin (rkB D.what₂.Tau O.N O.j a))
    (σ : D.what₂.LL →+* ℂ) (z : CxPts (πG ≫ (O.var c).str) σ) (y : Pts (O.var c) σ)
    (y' : CxPts (π₀ ≫ q) (σ.comp (algebraMap (𝓞 D.what₂.LL) D.what₂.LL))) (ch : ((VMetric.grLB (fl₀ a) i ((H a).pull π₀ rfl)).B.pull j).ι),
    y.1 = z.1 ≫ πG → y'.1 = z.1 ≫ j → under z ∈ ((VMetric.grLB (fl₀ a) i ((H a).pull π₀ rfl)).B.pull j).U ch →
      (Real.exp (-(2 * ((adlOf (O.Φ.C c) (O.met.hm c) (rootSym O.S.Dw (ArIn.ind P) (some R) (DV.tauEmb D a.1) (cond a.2 0 O.j + i))).n : ℕ) * (adlOf (O.Φ.C c) (O.met.hm c) (rootSym O.S.Dw (ArIn.ind P) (some R) (DV.tauEmb D a.1) (cond a.2 0 O.j + i))).ci (InfinitePlace.mk σ))) *
          (cxSt D.what₂.LL).pn (O.var c) σ (adlOf (O.Φ.C c) (O.met.hm c) (rootSym O.S.Dw (ArIn.ind P) (some R) (DV.tauEmb D a.1) (cond a.2 0 O.j + i))).D ((adlOf (O.Φ.C c) (O.met.hm c) (rootSym O.S.Dw (ArIn.ind P) (some R) (DV.tauEmb D a.1) (cond a.2 0 O.j + i))).m σ) ((cxSt D.what₂.LL).cx (O.var c) σ (genAt (adlOf (O.Φ.C c) (O.met.hm c) (rootSym O.S.Dw (ArIn.ind P) (some R) (DV.tauEmb D a.1) (cond a.2 0 O.j + i))).D (under y))) y) ^ 1 =
        ‖ratVal (φ (genAt (adlOf (O.Φ.C c) (O.met.hm c) (rootSym O.S.Dw (ArIn.ind P) (some R) (DV.tauEmb D a.1) (cond a.2 0 O.j + i))).D (under y)) ^ 1 * (r a i ch : G.functionField)) z‖ ^ 2 * Real.exp (-((VMetric.grLB (fl₀ a) i ((H a).pull π₀ rfl)).φ _).φ (ch PUnit.unit) y') := by
  intro P1 P2 P3 D O hO P R hR c Bs _ q arq nBs E h H Bg jB πB u hG hF hI Y₀ _ π₀ fl₀ hfb ar₀ n₀ G _ j πG pb _ _ φ φs jG r hc a i σ z y y' ch hy hy' hz
  obtain ⟨Gm, hmet, hLM⟩ := hI
  obtain ⟨⟨t, g⟩, -, hadp⟩ := (O.Φ.C c).exists_adapted y
  rw [GlobalTheory.T.adapted_frame_partition_formula D O c R Gm hmet _ (GlobalTheory.Mean4O.parOf_rootSym _ _ _ _) σ y t g hadp,
    expo_rootSym O.S.Dw (ArIn.ind P) (some R) (DV.tauEmb D a.1) (cond a.2 0 O.j + i)]
  have hB : UnitAt (under z) ((((r a i ch)⁻¹ : G.functionFieldˣ) : G.functionField) *
        φ ((prodPow t (rootEx O.S.Dw (DV.tauEmb D a.1) (cond a.2 0 O.j + i)) : (O.var c).Fnˣ) : (O.var c).Fn)) ∧
      Real.exp (-((VMetric.grLB (fl₀ a) i ((H a).pull π₀ rfl)).φ (σ.comp (algebraMap (𝓞 D.what₂.LL) D.what₂.LL))).φ
          (ch PUnit.unit) y') =
        ‖ratVal ((((r a i ch)⁻¹ : G.functionFieldˣ) : G.functionField) *
          φ ((prodPow t (rootEx O.S.Dw (DV.tauEmb D a.1) (cond a.2 0 O.j + i)) : (O.var c).Fnˣ) : (O.var c).Fn)) z‖ ^ 2 *
          (O.Φ.C c).genSq (Gm (embOf O.κ.e σ)) (rootEx O.S.Dw (DV.tauEmb D a.1) (cond a.2 0 O.j + i)) g := by
    rcases Bool.eq_false_or_eq_true a.2 with ha | ha
    · exact GlobalTheory.T.lie_generic_eigen_metric_setup D O c Bs q E h H Bg jB πB u hG Gm hLM Y₀ π₀ fl₀ hfb G j πG pb φ φs jG r hc a ha i σ z y y' ch t g
        hadp hy hy' hz
    · exact GlobalTheory.T.lie_generic_eigen_metric_bound D O c Bs q E h H Bg jB πB u hG Gm hLM Y₀ π₀ fl₀ hfb G j πG pb φ φs jG r hc a ha i σ z y y' ch t g
        hadp hy hy' hz
  obtain ⟨hU, hW⟩ := hB
  erw [hW]
  set Pf : (O.var c).Fn := ((prodPow t (rootEx O.S.Dw (DV.tauEmb D a.1) (cond a.2 0 O.j + i)) : (O.var c).Fnˣ) :
    (O.var c).Fn) with hPf
  set s : (O.var c).Fn := genAt (adlOf (O.Φ.C c) (O.met.hm c)
    (rootSym O.S.Dw (ArIn.ind P) (some R) (DV.tauEmb D a.1) (cond a.2 0 O.j + i))).D (under y) with hs
  set X0 : G.functionField := (((r a i ch)⁻¹ : G.functionFieldˣ) : G.functionField) * φ Pf with hX0
  have hsP : UnitAt (under y) (s * Pf) := by
    have h1 := FlagCpt.prodPow_mem (rootEx O.S.Dw (DV.tauEmb D a.1) (cond a.2 0 O.j + i)) hadp.mem_eqnSet
    have eD : (adlOf (O.Φ.C c) (O.met.hm c)
        (rootSym O.S.Dw (ArIn.ind P) (some R) (DV.tauEmb D a.1) (cond a.2 0 O.j + i))).D =
        divOf (O.Φ.C c) (rootEx O.S.Dw (DV.tauEmb D a.1) (cond a.2 0 O.j + i)) :=
      congrArg (divOf (O.Φ.C c)) (expo_rootSym _ _ _ _ _)
    have h2 : CartierDiv.IsEqn (divOf (O.Φ.C c) (rootEx O.S.Dw (DV.tauEmb D a.1) (cond a.2 0 O.j + i))) (Var.base y)
        (eqn (adlOf (O.Φ.C c) (O.met.hm c)
          (rootSym O.S.Dw (ArIn.ind P) (some R) (DV.tauEmb D a.1) (cond a.2 0 O.j + i))).D (under y)) := by
      rw [← eD]; exact GlobalTheory.TrueGeo.Base.isEqn_eqn _ _
    have h3 := (CartierDiv.IsEqn.iff_unitAt h2).1 h1
    have e : s * Pf = Pf / ((eqn (adlOf (O.Φ.C c) (O.met.hm c)
      (rootSym O.S.Dw (ArIn.ind P) (some R) (DV.tauEmb D a.1) (cond a.2 0 O.j + i))).D (under y) : (O.var c).Fnˣ) :
        (O.var c).Fn) := by
      rw [hs, genAt, Units.val_inv_eq_inv_val, div_eq_mul_inv, mul_comm]
    rw [e]
    exact h3
  obtain ⟨hv, hu⟩ := GlobalTheory.T.rational_function_value_compatible (O.var c).str πG φ ‹_› σ z y hy (s * Pf)
  have hUz := hu hsP
  have hreg : RegAt (under z) (φ s * (r a i ch : G.functionField)) := by
    obtain ⟨b, hb, hbX⟩ := hU
    obtain ⟨b', -, hb'X⟩ := hUz
    refine ⟨b' * ↑hb.unit⁻¹, ?_⟩
    have hP0 : φ Pf ≠ 0 := (map_ne_zero φ).2 (Units.ne_zero _)
    have hr0 : (r a i ch : G.functionField) ≠ 0 := Units.ne_zero _
    have hb0 : algebraMap _ G.functionField b ≠ 0 := by
      rw [hbX, hX0]; exact mul_ne_zero (Units.ne_zero _) hP0
    rw [map_mul, hb'X]
    have : algebraMap _ G.functionField (↑hb.unit⁻¹ : G.presheaf.stalk (under z)) = (algebraMap _ G.functionField b)⁻¹ := by
      exact eq_inv_of_mul_eq_one_left (by rw [← map_mul, IsUnit.val_inv_mul, map_one])
    rw [this, hbX, hX0, map_mul, Units.val_inv_eq_inv_val, mul_inv, inv_inv]
    field_simp
  have hfac : φ (s * Pf) = (φ s * (r a i ch : G.functionField)) * X0 := by
    rw [hX0, map_mul, mul_assoc, Units.mul_inv_cancel_left]
  have hrv := (hv hsP.regAt).2
  rw [hfac, ratVal_mul hreg (hU.regAt)] at hrv
  rw [← hrv, pow_one]
  simp only [norm_mul, mul_pow]
  ring

end GlobalTheory.BcReadCx

end
