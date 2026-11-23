import Formalism.SharpRestriction.GlobalSchurBounds.GL3Columns
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.IsoDualPair
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.IsoFunV
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.IsoScaleA
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.IsoInvMetric
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.ScalDeg
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.IsoDerivB
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.WwCauchyBinet
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.WwMinorExpand
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.WwMain
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.WwEval
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.WwInjective

namespace Formalism.MainNotions.GL3Columns

open Formalism.BasicNotions Formalism.MainNotions.G Formalism.MainNotions.GL3Theta Formalism.MainNotions.TaylorLogMetric

theorem dual_pair_isometry (D : D7) : IsometryOntoDualFrames D := fun N nu => isometry_dual_pair (Bool × HH D) N nu

theorem isoFun_holds (D : D7) : isoFun D := fun N N' nu s Θ => isometry_function_v (Bool × HH D) D.what₂.Tau (tauPl D) N N' nu s Θ

theorem isoScale_holds (D : D7) : isoScale D := fun N N' nu c s Θ φ => isometry_scaling (Bool × HH D) D.what₂.Tau (tauPl D) N N' nu c s Θ φ

theorem inverse_metric_isometry (D : D7) : InducedNormInvariantMetric D := fun N nu => isometry_invariant_metric (Bool × HH D) N nu

theorem scal_holds (D : D7) : scal D := fun N N' s s' Qp dg hH y' => scalar_degree D.what₂.Tau N N' s s' Qp dg hH y'

theorem isoB_holds (D : D7) : isoB D :=
  fun N N' nu s Θ φ Q hQ y' => isometry_derivative_bound (Bool × HH D) D.what₂.Tau (tauPl D) N N' nu s Θ φ Q hQ y'

theorem wwCB_holds (D : D7) : wwCB D := fun k _ N nu y => cauchy_binet_minors (Bool × HH D) k N nu y

theorem wwKt_holds (D : D7) : wwKt D := fun N0 N1 nu I => minor_expansion (Bool × HH D) N0 N1 nu I

theorem ww_holds (D : D7) : ww D :=
  fun l _ N0 N1 nu Th ph Q hQ y' => minor_identity (Bool × HH D) l N0 N1 nu Th ph Q hQ y'

theorem wwEv_holds (D : D7) : wwEv D := fun l _ N0 N1 nu Th x I => minor_evaluation (Bool × HH D) l N0 N1 nu Th x I

theorem wwInj_holds (D : D7) : wwInj D :=
  fun l _ N nu ph hy J => wwInjective_of cauchy_binet_minors (Bool × HH D) l N nu ph hy J

theorem theta_isometry_facts_hold (D : D7) : ConclusionW D :=
  ⟨wwCB_holds D, wwInj_holds D, wwKt_holds D, ww_holds D, wwEv_holds D, inverse_metric_isometry D, dual_pair_isometry D, isoB_holds D, isoFun_holds D,
    isoScale_holds D⟩

end Formalism.MainNotions.GL3Columns
