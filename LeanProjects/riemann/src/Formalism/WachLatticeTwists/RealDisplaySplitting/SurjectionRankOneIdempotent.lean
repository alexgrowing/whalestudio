import Formalism.WachLatticeTwists.RamifiedBlockRings.DistinctEigenvalueCornerPerturbation

open Finset Classical

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.SF

open Formalism.NG

def LatM {R : Type} [Ring R] (O : Type) [CommRing O] (M : Type) [AddCommGroup M] [Module O M]
    (n : Type) [Fintype n] [DecidableEq n] (_ρ : R →+* Matrix n n O) : Type := n → M

section LatM
variable {R : Type} [Ring R] (O : Type) [CommRing O] (M : Type) [AddCommGroup M] [Module O M]
  (n : Type) [Fintype n] [DecidableEq n] (ρ : R →+* Matrix n n O)

instance : AddCommGroup (LatM O M n ρ) := inferInstanceAs (AddCommGroup (n → M))
instance : Module O (LatM O M n ρ) := inferInstanceAs (Module O (n → M))
instance : Module R (LatM O M n ρ) := Module.compHom (n → M) ((matEnd O M n).comp ρ)

end LatM

section Maps
variable {R : Type} [Ring R] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  (n : Type) [Fintype n] [DecidableEq n] (ρ : R →+* Matrix n n O)

instance : Module (FractionRing O) (LatM O (FractionRing O) n ρ) :=
  inferInstanceAs (Module (FractionRing O) (n → FractionRing O))

def tensM : LatM O O n ρ →ₗ[O] KO O →ₗ[O] LatQ O n ρ :=
  LinearMap.mk₂ O (fun (v : n → O) (x : KO O) => (fun a => v a • x : n → KO O))
    (fun v v' x => funext fun a => add_smul (v a) (v' a) x)
    (fun c v x => funext fun a => mul_smul c (v a) x)
    (fun v x x' => funext fun a => smul_add (v a) x x')
    (fun c v x => funext fun a => smul_comm (v a) c x)

def iLM : LatM O O n ρ →ₗ[O] LatM O (FractionRing O) n ρ :=
  ((Algebra.linearMap O (FractionRing O)).compLeft n : (n → O) →ₗ[O] (n → FractionRing O))

def qVM : LatM O (FractionRing O) n ρ →ₗ[O] LatQ O n ρ :=
  (((1 : Submodule O (FractionRing O)).mkQ).compLeft n : (n → FractionRing O) →ₗ[O] (n → KO O))

end Maps

def SurjectionRankOneIdempotent (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (A : Type) [Ring A]
    (n : Type) [Fintype n] [DecidableEq n] (ρ : A →+* Matrix n n O) (e₁ : A) : Prop :=
  ∃ v₁ : LatM O O n ρ,
    (∀ (a : A) v x, tensM O n ρ (a • v) x = a • tensM O n ρ v x) ∧
    (∀ m : LatQ O n ρ, e₁ • m = m → ∃ x, m = tensM O n ρ v₁ x) ∧
    (∀ (a : A) v, iLM O n ρ (a • v) = a • iLM O n ρ v) ∧ (∀ (a : A) v, qVM O n ρ (a • v) = a • qVM O n ρ v) ∧
    (∀ v (x : FractionRing O), tensM O n ρ v (Submodule.Quotient.mk x) = qVM O n ρ (x • iLM O n ρ v)) ∧
    Function.Injective (iLM O n ρ) ∧ Function.Surjective (qVM O n ρ) ∧
    LinearMap.ker (qVM O n ρ) = LinearMap.range (iLM O n ρ) ∧
    (∀ v : LatM O (FractionRing O) n ρ, ∃ c : O, c ≠ 0 ∧ c • v ∈ LinearMap.range (iLM O n ρ)) ∧
    e₁ • v₁ = v₁ ∧ (∀ v : LatM O O n ρ, ∃ c : A, (c * e₁) • v₁ = v)

def ScalarActionOnBlock (O : Type) [CommRing O] (A : Type) [Ring A] (M : Type) [AddCommGroup M] [Module A M] [Module O M]
    (E : A) (δO : O) : Prop :=
  (∀ c : A, ∃ x ∈ Ideal.span {δO}, ∀ m : M, (c * E) • m = x • m) ∧
  (∀ x ∈ Ideal.span {δO}, ∃ c : A, ∀ m : M, (c * E) • m = x • m)

end Formalism.RepresentationBoundsCohomology.SF
