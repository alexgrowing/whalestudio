import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.SecondLevelOfNorm
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.LubinTateLogIsArtinHasse
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.ComplexMultiplicationFieldData
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.BiextensionRelationOfExpSpec
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.GramMatrixExists

namespace Formalism.L2.Th1.D

theorem ltLogIsLgF : LtLogIsLgF := lubin_tate_log_is_artin_hasse
theorem thetaHom : ThetaHom := theta_homomorphism
theorem phCompare : PhCompare := phi_comparison
theorem first_level_on_curve : CurveExponentCoboundaryCocycle := first_level_curve_holds
theorem bHypCurve : BHypCurve := biextension_hypotheses_curve
theorem fieldDataCM : FieldDataCM := complex_multiplication_field_data
theorem thmAEntryCM : ThmAEntryCM := ThmAEntryCM_of first_level_on_curve
theorem thmAGaussCM : ThmAGaussCM := ThmAGaussCM_of first_level_on_curve
theorem oneLetterGaussCM : OneLetterGaussCM := OneLetterGaussCM_of first_level_on_curve
theorem kernelCM : KernelCM := KernelCM_of first_level_on_curve
theorem relative_theta_factorization : RelativeThetaFactorization := biextension_relation_holds
theorem eigenOdd : EigenOdd := odd_eigenspace
theorem gramExists : GramExists := gram_matrix_exists

end Formalism.L2.Th1.D
