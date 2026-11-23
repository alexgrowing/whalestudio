import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.LocIsotypic
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC UpperTheory.V.Af
open scoped Matrix TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Af

section Sys

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}

variable (n) in

def IsCusp (sat : HeightOneSpectrum (𝓞 F) → Multiset ℂˣ → Prop) (inf : (F →+* ℂ) → Multiset ℂ → Prop) : Prop :=
  (∃ (_ : IsTotallyComplex F) (π : CuspSub F n), sat = (CG.mk π).HasSat ∧ inf = π.HasInfChar) ∨
    ∃ (_ : IsTotallyReal F) (π : TR.CuspSub F n), sat = π.HasSat ∧ inf = fun τ => π.HasInfChar (InfinitePlace.mk τ)

omit [NumberField F] in
variable (n) in

def RegInf (inf : (F →+* ℂ) → Multiset ℂ → Prop) : Prop :=
  ∀ τ, ∃ m, inf τ m ∧ m.Nodup ∧ ∀ z ∈ m, ∃ k : ℤ, z = (k : ℂ) + ((n : ℂ) - 1) / 2

def IsAut (ι : Qbar l ≃+* ℂ) (r : G F Ω →* GL (Fin n) (Qbar l)) : Prop :=
  ∃ sat inf, IsCusp n sat inf ∧ RegInf n inf ∧ AttachedSys ι r sat

def IsCharOf [IsAlgClosure F Ω] (ι : Qbar l ≃+* ℂ) (χ : HChar F) (μ : G F Ω →* (Qbar l)ˣ) : Prop :=
  Continuous μ ∧ ∃ (art : Ideles F →* Gab F Ω) (a : (F →+* ℂ) → ℤ), IsGlobalArtin art ∧ IsAlgPos χ a ∧ IsLAdicOf art ι χ a μ

def IsAlgChar [IsAlgClosure F Ω] (ι : Qbar l ≃+* ℂ) (μ : G F Ω →* (Qbar l)ˣ) : Prop := ∃ χ : HChar F, IsCharOf ι χ μ

omit [NumberField F] in

def IsConjEl (c : G F Ω) : Prop := ∃ j : Ω →+* ℂ, ∀ x, j (c x) = starRingEnd ℂ (j x)

end Sys

section Pol

variable {F₀ F Ω : Type} [Field F₀] [Field F] [Field Ω] [Algebra F₀ F] [Algebra F₀ Ω] [Algebra F Ω] [IsScalarTower F₀ F Ω]
  {k : Type} [Field k] {n : ℕ}

def IsPairing (c : G F₀ Ω) (r : G F Ω →* GL (Fin n) k) (μ : G F Ω →* kˣ) (P : GL (Fin n) k) : Prop :=
  ∀ s s' : G F Ω, s'.restrictScalars F₀ = c * s.restrictScalars F₀ * c⁻¹ →
    (r s : Matrix (Fin n) (Fin n) k)ᵀ * (P : Matrix (Fin n) (Fin n) k) * (r s' : Matrix (Fin n) (Fin n) k) =
      (μ s : k) • (P : Matrix (Fin n) (Fin n) k)

variable (F₀ F) in

abbrev resG (Ω : Type) [Field Ω] [Algebra F₀ Ω] [Algebra F Ω] [IsScalarTower F₀ F Ω] : G F Ω →* G F₀ Ω :=
  AlgEquiv.restrictScalarsHom F₀

end Pol

def IsPlusOf (F₀ F : Type) [Field F₀] [NumberField F₀] [Field F] [NumberField F] [Algebra F₀ F] : Prop :=
  IsTotallyReal F₀ ∧ (Module.finrank F₀ F = 1 ∨ (Module.finrank F₀ F = 2 ∧ IsTotallyComplex F))

section Quat

variable (F : Type) [Field F] [NumberField F]

structure DefQuat : Type 1 where

  D : Type
  [ring : DivisionRing D]
  [alg : Algebra F D]
  central : Algebra.IsCentral F D
  rank : Module.finrank F D = 4

  definite : ∀ τ : F →+* ℝ, letI := τ.toAlgebra; NoZeroDivisors (ℝ ⊗[F] D)

  jf : D →ₐ[F] Matrix (Fin 2) (Fin 2) (Af F)
  jf_bij : Function.Bijective (Algebra.TensorProduct.lift (Algebra.ofId (Af F) (Matrix (Fin 2) (Fin 2) (Af F))) jf
    fun _ _ => Algebra.commutes _ _)

  jc : InfinitePlace F → D →+* Matrix (Fin 2) (Fin 2) ℂ
  jc_alg : ∀ v x, jc v (algebraMap F D x) = algebraMap ℂ _ (v.embedding x)

attribute [instance] DefQuat.ring DefQuat.alg

variable {F}

def IsOuter (lam : InfinitePlace F → DomWeight 2) {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (InfinitePlace F → GL (Fin 2) ℂ) V) : Prop :=
  FiniteDimensional ℂ V ∧ ρ.IsIrreducible ∧ ∀ v, ∃ f : _ →ₗ[ℂ] V, f ≠ 0 ∧
    ∀ g x, f (GlobalTheory.Branching.sqRep ℂ 2 (lam v) g x) = ρ (by classical exact Pi.mulSingle v g) (f x)

namespace DefQuat

variable (Q : DefQuat F)

def toFin : Q.Dˣ →* GL (Fin 2) (Af F) := Units.map Q.jf.toRingHom.toMonoidHom

def toInf : Q.Dˣ →* (InfinitePlace F → GL (Fin 2) ℂ) := Pi.monoidHom fun v => Units.map (Q.jc v).toMonoidHom

def Occurs {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (InfinitePlace F → GL (Fin 2) ℂ) V)
    (τ : SmIrr (GL (Fin 2) (Af F))) : Prop :=
  ∃ Φ : τ.V →ₗ[ℂ] (GL (Fin 2) (Af F) → V), Φ ≠ 0 ∧ (∀ x γ g, Φ x (Q.toFin γ * g) = ρ (Q.toInf γ) (Φ x g)) ∧
    ∀ h x g, Φ (τ.ρ h x) g = Φ x (g * h)

end DefQuat

end Quat

end UpperTheory.V.Af
