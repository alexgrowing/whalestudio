import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemSmulLk
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianSeenPrimeConditionHermitianSideStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DualModClassLatticeEquivQuotientStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MiddleStepOneLevelProjectionEqChartProjectionStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StabiliserMapHyperplaneEqConjClassMapStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianUpMoveAtLevelPrimePlaceStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHermitianDownMoveAtLevelPrimePlaceStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DiamondOperatorHermitianSideLevelPrimeStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianSideClassesEqFormClassesStatement

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.HAt Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

set_option maxHeartbeats 4000000 in
theorem GlobalTheory.Mem.Col2.TC.hermitian_data_at_level_prime : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)), (∀ u, I.StdF l Z u (F u) ∧ I.StdLvC l Z u (F u)) → CarH H F → ∃ A, CarT H F A ∧ Formalism.L2.Herm.SymmetricAdelicCompatibility (I.rec7 l Z) H A ∧ Formalism.L2.Herm.SymmetricStabilizerMapCompatibility (I.rec7 l Z) H A := by
  intro B X I hI hP l Z H F hS hC
  have hseen := GlobalTheory.T.hermitianSeenPrimeCondition_hermitianSide I hI hP l Z H F hS hC
  have hdisc := GlobalTheory.T.dual_mod_class_lattice_equiv_quotient I hI hP l Z H F hS hC
  have hlvc := GlobalTheory.T.middleStep_oneLevel_projection_eq_chart_projection I hI hP l Z H F hS hC
  have hstab := GlobalTheory.T.stabiliserMap_hyperplane_eq_conj_classMap I hI hP l Z H F hS hC
  choose upG hup using GlobalTheory.T.hermitianUpMove_at_levelPrime_place I hI hP l Z H F hS hC
  choose dnG hdn using GlobalTheory.T.exists_hermitianDownMove_at_levelPrime_place I hI hP l Z H F hS hC
  choose dilG hdil using GlobalTheory.T.diamondOperator_hermitian_side_levelPrime I hI hP l Z H F hS hC
  choose lattice₂ levP clsP hcar hlat using GlobalTheory.T.hermitianSide_classes_eq_formClasses I hI hP l Z H F hS hC
  let A : ∀ u, Formalism.L2.Herm.AtT (I.rec7 l Z) u (H.vT u) (H.Fv u) := fun u =>
    mkAtT (F u).atT (F u).lv (hC.eV u) (hC.fv u) (hseen u) (hdisc u) (upG u) (fun i hi v c y h => (hup u i v c y hi h).1)
      (dnG u) (fun i hi v c g h => (hdn u i v c g hi h).1) (dilG u) (fun i hi v a c => (hdil u i v a c hi).1)
      (lattice₂ u) (levP u) (clsP u) (F u).til (hlat u)
  have hT : CarT H F A := by
    refine ⟨fun _ => rfl, fun _ => rfl, hcar, hlat, ?_, ?_, ?_, ?_, ?_⟩
    · intro u i hi v c z z' h
      exact (congrArg _ (Subtype.ext h)).trans (prH_eq (F u).atT (F u).lv hi v c z).symm
    · intro u i hi v c z z' h
      exact (congrArg _ (Subtype.ext h)).trans (prkH_eq (F u).atT (F u).lv hi v c z).symm
    · intro u i h1 h2 v c z z' h
      refine ((hlvc u i h1 h2 v c).1 (toLd i (le_of_succ_m h2) c z) z' h).trans (prH_eq (F u).atT (F u).lv (le_of_succ_m h2) v c z).symm
    · intro u
      exact ((crdN (I.rec7 l Z) _ le_rfl).apply_symm_apply _).symm
    · intro u c
      exact (reGL_lin _ (rankN (I.rec7 l Z) _ le_rfl) _).symm
  refine ⟨A, hT, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, hstab A hT⟩
  · intro u v c y h
    exact (hup u 0 v c y (Nat.zero_le _) h).2
  · intro u i h1 hm v c y h
    cases i with
    | zero => omega
    | succ i => exact (hup u (i + 1) v c y hm h).2 hm
  · intro u v c g h
    exact (hdn u 0 v c g (Nat.zero_le _) h).2
  · intro u i h1 hm v c g h
    cases i with
    | zero => omega
    | succ i => exact (hdn u (i + 1) v c g hm h).2 hm
  · intro u v a c
    exact (hdil u 0 v a c (Nat.zero_le _)).2
  · intro u i h1 hm v a c
    cases i with
    | zero => omega
    | succ i => exact (hdil u (i + 1) v a c hm).2 hm
