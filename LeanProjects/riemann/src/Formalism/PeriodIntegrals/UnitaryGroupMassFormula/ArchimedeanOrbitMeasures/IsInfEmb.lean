import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.InstTopologicalSpaceHA

noncomputable section

namespace HcS.MainNotions.StandardLattice

open NumberField HcS.BasicNotions Finset
open scoped ENNReal

section SW

open HcS.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain
open scoped TensorProduct

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E)

end SW

section Vol

open HcS.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)

def infMat (θ : Ainf F ⊗[F] E →+* ℂ) (h : HA (AF F) σ J) : Matrix (Fin M) (Fin M) ℂ :=
  (((HA.mat (AF F) σ J h : GL (Fin M) (AF F ⊗[F] E)) : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)).map
    (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E))).map θ

def IsInfEmb (τ : E →+* ℂ) (θ : Ainf F ⊗[F] E →+* ℂ) : Prop :=
  (∀ x : E, θ ((1 : Ainf F) ⊗ₜ[F] x) = τ x) ∧ Continuous fun a : Ainf F => θ (a ⊗ₜ[F] (1 : E))

end Vol

section DS

open MeasureTheory Matrix
open scoped InnerProductSpace ComplexOrder

end DS

section Fam

end Fam

end HcS.MainNotions.StandardLattice
