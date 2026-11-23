import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RationalNormOneClassEqFiniteAdelicDetClass
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormOneFiniteAdeleDetClassOfIsDetLift
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevOkTwists
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.FullDt ReciprocityTheory.Neutral.Bridge.HCFR Neutral.B1
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rationalNormOne_class_eq_finiteAdelic_det_class : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (SQ : Finset (HeightOneSpectrum (𝓞 H.E))) (z : unitary H.E) (x : Formalism.L2.Herm.unitaryOneFiniteAdeles (host_cmData R H)), Matrix.GeneralLinearGroup.det x.1 = Formalism.L2.Herm.unitaryOneRationalAdele H.F z → e1Q H SQ z = u1Dt H SQ x := by
  first | exact @GlobalTheory.Mem.Col2.FullDt.e1Q_eq_u1Dt_of_det_eq | exact GlobalTheory.Mem.Col2.FullDt.e1Q_eq_u1Dt_of_det_eq | (intros; apply GlobalTheory.Mem.Col2.FullDt.e1Q_eq_u1Dt_of_det_eq <;> assumption)
