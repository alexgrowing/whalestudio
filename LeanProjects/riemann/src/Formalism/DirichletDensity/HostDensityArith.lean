import Formalism.DirichletDensity.DirichletDensityProofs.QuadDiscr
import Formalism.DirichletDensity.DirichletDensityProofs.MQDiscr
import Formalism.DirichletDensity.DirichletDensityProofs.APLogDensity
import Formalism.DirichletDensity.DirichletDensityProofs.LogToDir
import Formalism.DirichletDensity.DirichletDensityProofs.HostDensityArith
import Formalism.DirichletDensity.DirichletDensityProofs.HostDensity

namespace Formalism.HF.Final

theorem quadDiscr : Formalism.HF.QuadDiscr := Formalism.HF.quadDiscr
theorem mqDiscr : Formalism.HF.MQDiscr := Formalism.HF.mqDiscr_of quadDiscr
theorem hostDiscr : Formalism.HF.HostDiscr := Formalism.HF.hostDiscr_of mqDiscr
theorem apLogDensity : Formalism.HF.APLogDensity := Formalism.HF.apLogDensity
theorem logToDir : Formalism.HF.LogToDir := Formalism.HF.logToDir
theorem hostDensityArith : Formalism.HF.HostDensityArith := Formalism.HF.hostDensityArith_of apLogDensity logToDir
theorem hostDensity : Formalism.HF.HostDensity := Formalism.HF.hostDensity_of hostDensityArith

end Formalism.HF.Final
