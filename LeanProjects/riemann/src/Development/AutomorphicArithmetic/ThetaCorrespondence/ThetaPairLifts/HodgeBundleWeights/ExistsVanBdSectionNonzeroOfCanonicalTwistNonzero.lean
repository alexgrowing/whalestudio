import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.TamagawaNumberSpecialUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalSectionModificationWeight
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Hypotheses2
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.LogCanonicalCriterionBoundary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalSectionModificationWeightStatement

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
namespace GlobalTheory.CuspNonvanishing
theorem exists_vanBd_section_nonzero_of_canonical_twist_nonzero : _root_.GlobalTheory.CovTop.Hypotheses'' → GlobalTheory.Published.GrothendieckDeformation → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), FnAlgClosed Xo c → ∀ (M : Modif (str₀ TF.X Z) (U₀ TF.X Z) (dimFlag Dw)) (ω : CanId M) (la : AllWt.Weight Dw) (g : H0 M.str (tens M.K.bundle ((L₀ TF.X Z (la - FlagTan.kap Dw)).pull M.σ)) ⊤) (z : M.X), z ∈ M.off → z ∈ nonzeroLocus (toSec g) → ∃ s ∈ vanBd TF.X Z la, M.σ z ∈ nonzeroLocus (toSec s) := by
  intro hP hG E _ _ _ H Dw l Xo c TF Z hF M ω la g z hz hg
  have hs : FlagTan.kap Dw + (la - FlagTan.kap Dw) = la := by abel
  set C := ((common₀ TF.X Z).pull M.σ).canChart M.K.isLB hs
  obtain ⟨m, hm⟩ := (M.bijective_pullOff (isLB_L₀ TF.X Z la)).2 ((C.mulEquiv ω.unit).symm (H0.restr le_top g))
  have hm' : C.mul ω.ω (M.pullOff m) = H0.restr le_top g := by
    rw [hm, ← ProdChart.mulEquiv_apply C ω.unit, LinearEquiv.apply_symm_apply]
  obtain ⟨s, hsv, hsr⟩ := (_root_.GlobalTheory.T.log_canonical_criterion_boundary hP hG E H Dw l Xo c TF Z hF M ω (la - FlagTan.kap Dw) la hs m).2 ⟨g, hm'.symm⟩
  refine ⟨s, hsv, ?_⟩
  obtain ⟨t, ha, hb, hc⟩ := C.cover z
  have e := C.germ_mul ω.ω (M.pullOff m) t z hz ha hb hc
  rw [hm', H0.germ_restr] at e
  have hu : IsUnit (H0.germ (C.c t) z (memTop z) hc g) := by
    rw [← ger_toSec]; exact (isUnit_ger_iff _ hc).2 hg
  rw [e] at hu
  have hu2 := isUnit_of_mul_isUnit_right hu
  have e2 := H0.germ_pull M.σ M.off_eq.le (C.b t) z hz hb m
  change IsUnit (H0.germ (C.b t) z hz hb (H0.pull M.σ M.off_eq.le m)) at hu2
  rw [e2] at hu2
  have hu3 := (isUnit_map_iff (M.σ.stalkMap z).hom _).1 hu2
  rw [← hsr] at hu3
  erw [H0.germ_restr] at hu3
  rw [← ger_toSec] at hu3
  exact (isUnit_ger_iff _ _).1 hu3
end GlobalTheory.CuspNonvanishing
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_form_nonvanishing_at_cusp : _root_.GlobalTheory.CovTop.Hypotheses'' → GlobalTheory.Published.GrothendieckDeformation → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), FnAlgClosed Xo c → ∀ (M : Modif (str₀ TF.X Z) (U₀ TF.X Z) (dimFlag Dw)) (ω : CanId M) (la : AllWt.Weight Dw) (g : H0 M.str (tens M.K.bundle ((L₀ TF.X Z (la - FlagTan.kap Dw)).pull M.σ)) ⊤) (z : M.X), z ∈ M.off → z ∈ nonzeroLocus (toSec g) → ∃ s ∈ vanBd TF.X Z la, M.σ z ∈ nonzeroLocus (toSec s) := by
  first | exact @_root_.GlobalTheory.CuspNonvanishing.exists_vanBd_section_nonzero_of_canonical_twist_nonzero | exact _root_.GlobalTheory.CuspNonvanishing.exists_vanBd_section_nonzero_of_canonical_twist_nonzero | (intros; apply _root_.GlobalTheory.CuspNonvanishing.exists_vanBd_section_nonzero_of_canonical_twist_nonzero <;> assumption)
end
