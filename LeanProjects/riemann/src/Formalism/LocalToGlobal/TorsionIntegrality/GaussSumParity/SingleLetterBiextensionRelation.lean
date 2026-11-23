import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.FinalOfNRDense
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.OneLetterGaussEveryOf
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.SecondLogDerivativeUnique

namespace Formalism.L2.Th1.D

theorem nrDense : NRDense := NRDense_of sqrtKur

theorem nrcmOfCM4 : Formalism.L2.Th1.CM.CM4 → NRCM := NRCM_of sqrtKur denseOK homothetic_lattice_integral_s2 nrDense

theorem thmAEntryFinal : ThmAEntryFinal := ThmAEntryFinal_of' nrcmOfCM4
theorem thmAGaussFinal : ThmAGaussFinal := ThmAGaussFinal_of' nrcmOfCM4
theorem oneLetterGaussFinal : OneLetterGaussFinal := OneLetterGaussFinal_of' nrcmOfCM4
theorem kernelFinal : KernelFinal := KernelFinal_of' nrcmOfCM4

theorem thmAEntryEvery : ThmAEntryEvery := ThmAEntryEvery_of nrcmOfCM4
theorem thmAGaussEvery : ThmAGaussEvery := ThmAGaussEvery_of nrcmOfCM4
theorem oneLetterGaussEvery : OneLetterGaussEvery := OneLetterGaussEvery_of nrcmOfCM4
theorem kernelEvery : KernelEvery := KernelEvery_of nrcmOfCM4

end Formalism.L2.Th1.D
