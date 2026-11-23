import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAGaugeLinesAsm
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAGaugeLinesLeft
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAGaugeLinesRight

namespace Formalism.FourierDecayAlt.P.CutMP.JA

theorem gauge_lines_holds : PRho.GaugeLines :=
  PRho.GL.gaugeLines_of_cut PRho.GL.gauge_right_line_holds PRho.GL.gauge_left_line_holds

end Formalism.FourierDecayAlt.P.CutMP.JA
