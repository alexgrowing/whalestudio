import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClassLatticeSupPrimeDualLocalizationEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlESymmApply
open Formalism.BasicNotions Formalism.L2.Forms Formalism.UG Formalism.L2.GlobalTheoryTheory.LocalLatticeBases NumberField IsDedekindDomain Matrix GlobalTheory.LevelHecke
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.classLattice_sup_primeDual_localization_eq : ∀ (D : D7) (u : D.what₂.Word) (A : AtTTied u) (i : ℕ) (hi : i ≤ D.R.m) (K : ClsTied u i hi) (v : (D.mem u).A.vT) (c : (D.mem u).C.cls i), loc (A.res v) (Lk A i hi v c) = loc (A.res v) (clsCrd D u i hi c) := by
  first | exact @GlobalTheory.LevelHecke.loc_lk_eq_loc_cls | exact GlobalTheory.LevelHecke.loc_lk_eq_loc_cls | (intros; apply GlobalTheory.LevelHecke.loc_lk_eq_loc_cls <;> assumption)
