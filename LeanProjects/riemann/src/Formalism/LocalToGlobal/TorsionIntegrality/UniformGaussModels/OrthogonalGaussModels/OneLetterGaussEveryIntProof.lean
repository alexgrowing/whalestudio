import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.StatementA
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.SingleLetterBiextensionRelation
import Formalism.LocalToGlobal.TorsionIntegrality.CMGoodModels.CmAll

namespace Formalism.L2.Th1.Top

open Formalism.L2.Th1.CM (cm2 cm3 cm4)

variable [Fact _root_.Formalism.L2.Th1.CM.CM2] in
theorem ThmAEntryInt_proof : ThmAEntryInt := Formalism.L2.Th1.D.thmAEntryFinal cm2 cm3 cm4
variable [Fact _root_.Formalism.L2.Th1.CM.CM2] in
theorem ThmAGaussInt_proof : ThmAGaussInt := Formalism.L2.Th1.D.thmAGaussFinal cm2 cm3 cm4
variable [Fact _root_.Formalism.L2.Th1.CM.CM2] in
theorem OneLetterGaussInt_proof : OneLetterGaussInt := Formalism.L2.Th1.D.oneLetterGaussFinal cm2 cm3 cm4
variable [Fact _root_.Formalism.L2.Th1.CM.CM2] in
theorem KernelInt_proof : KernelInt := Formalism.L2.Th1.D.kernelFinal cm2 cm3 cm4

theorem ThmAEntryEveryInt_proof : ThmAEntryEveryInt := Formalism.L2.Th1.D.thmAEntryEvery cm4
theorem ThmAGaussEveryInt_proof : ThmAGaussEveryInt := Formalism.L2.Th1.D.thmAGaussEvery cm4
theorem OneLetterGaussEveryInt_proof : OneLetterGaussEveryInt := Formalism.L2.Th1.D.oneLetterGaussEvery cm4
theorem KernelEveryInt_proof : KernelEveryInt := Formalism.L2.Th1.D.kernelEvery cm4

end Formalism.L2.Th1.Top
