import Development.EtaleCohomology.KummerTheory.StalkPf
import Development.EtaleCohomology.KummerTheory.ResNegZero
import Development.EtaleCohomology.KummerTheory.PrimIsPrimitiveRoot
import Development.EtaleCohomology.KummerTheory.EtaleNormalizedFreeChainsDifferentialOneZeroEqZe
import Development.EtaleCohomology.KummerTheory.PrimTorsPf
import Development.EtaleCohomology.KummerTheory.SecSHPf
import Development.EtaleCohomology.KummerTheory.ShSectPf

theorem LateralTheory.Fix.Stalk.intersectionNumber_baseChange : LateralTheory.KummerTheory.Stalk := by
  have hT : LateralTheory.KummerTheory.TwSec :=
    LateralTheory.KummerTheory.TwSec_of LateralTheory.KummerTheory.PrimTors_of
      (LateralTheory.KummerTheory.SecSH_of LateralTheory.KummerTheory.ShSectPf.ShSect_of)
  exact LateralTheory.KummerTheory.Stalk_of
    (LateralTheory.KummerTheory.etale_kummer_degree_zero_cohomology_of_twist_section_class_and_root_ex hT (LateralTheory.KummerTheory.Cls0_of hT)
      (LateralTheory.KummerTheory.OneEx_of hT LateralTheory.KummerTheory.TwRes0_of LateralTheory.KummerTheory.Sec0Ex_of))
