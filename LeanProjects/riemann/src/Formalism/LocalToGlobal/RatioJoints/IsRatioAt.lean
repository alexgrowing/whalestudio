import Formalism.LocalToGlobal.ThetaChr
import Formalism.LocalToGlobal.JointCharacters.LocEMulLocE

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open scoped TensorProduct

namespace Formalism.L2.Joints

variable (D : D7)

def finE : Formalism.L2.Theta.AE D →+* D.host.E ⊗[D.host.F] Formalism.L2.Herm.Af D.host.F :=
  (Algebra.TensorProduct.comm D.host.F (Formalism.L2.Herm.Af D.host.F) D.host.E).toRingHom.comp (Formalism.L2.Theta.finPart D)

def IsRatioAt (e : Formalism.L2.Theta.AE D) (k : D.host.E) (y : Formalism.L2.Theta.AE D) : Prop :=
  y * Formalism.L2.Theta.cA D (Formalism.L2.JoinChr.locE D e k) = Formalism.L2.JoinChr.locE D e k

def InPrimeK (x : D.host.E) (p : HeightOneSpectrum (𝓞 D.host.K)) : Prop :=
  ∃ y : 𝓞 D.host.K, ((y : D.host.K) : D.host.E) = x ∧ y ∈ p.asIdeal

open Classical in

def redV (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (x : v.adicCompletion F) : Formalism.L2.Forms.kv F v :=
  if h : x ∈ v.adicCompletionIntegers F then IsLocalRing.residue (v.adicCompletionIntegers F) ⟨x, h⟩ else 0

end Formalism.L2.Joints

end
