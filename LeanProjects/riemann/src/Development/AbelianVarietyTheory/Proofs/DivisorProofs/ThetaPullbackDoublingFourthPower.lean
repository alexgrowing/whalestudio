import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsTateZero
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
open CategoryTheory AlgebraicGeometry Set Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.ArInt GlobalTheory.TorsionForm GlobalTheory.ThetaRR
open GlobalTheory.LB (toMod)
open GlobalTheory.LieVB (omega)
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe (Fl Pt stdLat symMat tauU siegel symPart ChernIsFlat IsMetric InducesPolarisation cov)
open ReciprocityTheory.L2DbarEstimates (V)
open Filter Topology
open scoped ContDiff

set_option autoImplicit false

namespace GlobalTheory.ThetaRR

theorem exists_iso_dbl_pull_pow_four : ∀ (k : Type) [CommRing k] (S : Scheme.{0}) (p : S ⟶ Sp k), IsRegSurf p → ∀ (P : PPAS S) (L : HermLB (P.A.hom ≫ p)), IsTheta P L.B → ∃ (w : LB.Iso (L.pull (dbl P) (dbl_comp P p)).B (L.pow 4).B), w.IsGen := by
  intro k _ S p hS P L hT
  haveI : IsLocallyNoetherian S := hS.toIsArithVar.isLocallyNoetherian
  obtain ⟨α, hα⟩ := GlobalTheory.abelianSchemeLaws_all.1.mulPull S hT.polAV 2
  have hL : L.B.IsLB := hT.1
  have hα' : ∃ t : LB.Gen (LB.LinComb L.B (K := Fin 2) ![𝟙 P.A.left, dbl P] ![4, -1]), t.IsGen := by
    refine ⟨α, ?_⟩
    exact hα
  have h0 := (CechPic.cls_eq_zero_iff (LB.isLB_linComb hL _ _)).2 hα'
  rw [CechPic.cls_linComb hL] at h0
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, CechPic.pull_id] at h0
  refine (CechPic.cls_eq_iff (pull_isLB hL _) (isLB_lbPow hL 4)).1 ?_
  rw [CechPic.cls_pull hL, CechPic.cls_lbPow hL]
  rw [neg_smul, one_smul, ← sub_eq_add_neg, sub_eq_zero] at h0
  rw [← h0]
  exact natCast_zsmul (CechPic.cls L.B hL) 4

end GlobalTheory.ThetaRR
