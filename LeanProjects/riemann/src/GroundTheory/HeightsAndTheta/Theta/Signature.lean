import Mathlib
import GroundTheory.AutomorphicForms.HermitianSpaces
import GroundTheory.HeightsAndTheta.Theta.CMDatum
import GroundTheory.HeightsAndTheta.Theta.Inertia
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Theta

open Module Matrix NumberField GroundTheory.Automorphic

section General

variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {V : Type*} [AddCommGroup V] [Module E V]
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

noncomputable def completedGram (h : HermitianForm F E V) (b : Basis ι E V) (φ : E →+* ℂ) :
    Matrix ι ι ℂ :=
  (gram h.toSesq b).map φ

variable {φ : E →+* ℂ}

variable [FiniteDimensional E V]

noncomputable def signatureAt (h : HermitianForm F E V) (φ : E →+* ℂ) : ℕ × ℕ :=
  matrixSignature (completedGram h (Module.finBasis E V) φ)

end General

section CM

variable {F E : Type*} [Field F] [NumberField F] [IsTotallyReal F] [Field E] [NumberField E]
  [IsTotallyComplex E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {V : Type*} [AddCommGroup V] [Module E V] [FiniteDimensional E V]

noncomputable def signature (h : HermitianForm F E V) (v : InfinitePlace F) : ℕ × ℕ :=
  signatureAt h (exists_embedding_over F E v).choose

end CM

end GroundTheory.Heights₂.Theta
