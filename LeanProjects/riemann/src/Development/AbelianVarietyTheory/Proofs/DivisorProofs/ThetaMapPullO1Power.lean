import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SymTupOne
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.MinSt2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelSemiAbelianRelDimCotangentVectorBundleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoOfIsoOnRationalModelComponentsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetInvariantDiffIsoHodgeLineBundleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaMapPullO1PowerHodgeStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.ThetaPullback

theorem theta_pull_O1_pow : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (o : Type) [CommRing o] (m n : ℕ) (f : Xo.XF c ⟶ PSpace o n), Odd m → 3 ≤ m → IsUnit (m : o) → n + 1 = m ^ (4 * (Module.finrank ℚ E / 2 * (Dw.p + Dw.q))) → ThMap Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig m (pullback.fst _ _ : Xo.XF c ⟶ Xo.X) f → ∀ (Y : Model Xo c (RingHom.id c.F)) (g : Y.X ⟶ PSpace o n), Y.j ≫ g = f → (GlobalTheory.FlagMod.detOm Y).IsLB → LBIso (lbPow ((ProjSpace.O1 o n).pull g) (8 * (n + 1).factorial)) (lbPow (GlobalTheory.FlagMod.detOm Y) (4 * (n + 1).factorial * (n + 1).factorial)) := by
  intro E _ _ _ H Dw l Xo c o _ m n f hodd hm hunit hn hth Y g hg hdet
  obtain ⟨N, i, hi, hs⟩ := Y.proj
  haveI := ReciprocityTheory.ChartRestriction.G.Geo.Tor.isProper_str (↥c.F) N
  haveI : IsProper Y.s := by rw [← hs]; infer_instance
  have hvb := (GlobalTheory.T.modelSemiAbelian_relDim_cotangent_vectorBundle E H Dw l Xo c Y).2
  have hO : ((ProjSpace.O1 o n).pull g).IsLB := LB.isLB_pull (ProjSpace.O1_isLB o n) g
  have hA : (lbPow ((ProjSpace.O1 o n).pull g) (8 * (n + 1).factorial)).IsLB := LB.isLB_linComb hO _ _
  have hB : (lbPow (GlobalTheory.SiegelTor.hodge Y.t.G (Module.finrank ℚ E / 2 * (Dw.p + Dw.q)))
      (4 * (n + 1).factorial * (n + 1).factorial)).IsLB := LB.isLB_linComb hvb.isLB_det _ _
  have hC : (lbPow (GlobalTheory.FlagMod.detOm Y) (4 * (n + 1).factorial * (n + 1).factorial)).IsLB :=
    LB.isLB_linComb hdet _ _
  have hAB := GlobalTheory.T.lineBundleIso_of_iso_on_rational_model_components (↥c.F) Y.X Y.s _ _ Y.normal inferInstance inferInstance inferInstance hA hB
    (fun Ω _ _ M io hio hio' => GlobalTheory.T.theta_map_pull_O1_power_hodge E H Dw l Xo c o m n f hodd hm hunit hn hth Y g hg Ω M io hio hio')
  have hCB : LBIso (lbPow (GlobalTheory.FlagMod.detOm Y) (4 * (n + 1).factorial * (n + 1).factorial))
      (lbPow (GlobalTheory.SiegelTor.hodge Y.t.G (Module.finrank ℚ E / 2 * (Dw.p + Dw.q)))
        (4 * (n + 1).factorial * (n + 1).factorial)) :=
    GlobalTheory.PowPrimitive.lbIso_linComb (GlobalTheory.T.detInvariantDiff_iso_hodgeLineBundle E H Dw l Xo c Y hdet) _ _
  exact LBIso.trans hA hB hC hAB hCB.symm

end GlobalTheory.ThetaPullback
