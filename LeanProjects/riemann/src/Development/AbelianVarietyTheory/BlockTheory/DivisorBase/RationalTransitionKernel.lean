import Mathlib
import Formalism.LocalToGlobal.Divisibility.RowLat

open NumberField
open scoped Matrix

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.RationalTransitionKernel

open Formalism.L2.DIV Formalism.L2.Indef

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G]
  {Pl0 T J : Type} [Fintype J]

def cx (v : InfinitePlace K) {m n : ℕ} (A : Matrix (Fin m) (Fin n) K) : (Fin n → ℂ) →ₗ[ℂ] (Fin m → ℂ) :=
  (A.map v.embedding).mulVecLin

open Classical in

def mult (P : Subgroup G) (ψ : P →* Kˣ) (χ : G → K) : K :=
  (Nat.card P : K)⁻¹ * ∑ h : P, ((ψ h⁻¹ : Kˣ) : K) * χ (h : G)

def Generic (X : Finset (G → K)) (P : Subgroup G) (ψ : P →* Kˣ) : Prop := ∀ χ ∈ X, mult P ψ χ ≠ 0

section Data

variable (F : DefFam K G Pl0 T J) {EE : Type} [AddCommGroup EE] [Module ℂ EE]
  (ρ : Representation ℂ G EE) (Θ : ∀ t : T, (Fin (F.R t).S.dim → ℂ) →ₗ[ℂ] EE)

def Equivariant : Prop :=
  ∀ (t : T) (g : G), ∀ x ∈ LinearMap.range (cx F.v0 ((F.R t).vE (F.lvl ⊥ 1))),
    Θ t (cx F.v0 ((F.R t).S.actMat (F.R t).r g) x) = ρ g (Θ t x)

variable (Zs : DefSub F.amb) (P : Subgroup G) (ψ : P →* Kˣ)

def onGood (t : T) : (Fin ((F.R t).nV (F.lvl P ψ)) → ℂ) →ₗ[ℂ] EE :=
  Θ t ∘ₗ cx F.v0 ((F.R t).vE (F.lvl P ψ))

def KernelIsTrivial (t : T) : Prop :=
  LinearMap.ker (onGood F Θ P ψ t) = LinearMap.ker (cx F.v0 ((F.R t).Pq (F.lvl P ψ) (Zs.Z t)))

def iota (t : T) : (Fin ((F.R t).dZ (F.lvl P ψ) (Zs.Z t)) → ℂ) →ₗ[ℂ] EE :=
  onGood F Θ P ψ t ∘ₗ cx F.v0 ((F.R t).zE (F.lvl P ψ) (Zs.Z t))

def RatTransition (t : T) : Prop :=
  ∃ Y : Matrix (Fin ((F.R F.μ0).dZ (F.lvl P ψ) (Zs.Z F.μ0))) (Fin ((F.R t).dZ (F.lvl P ψ) (Zs.Z t))) K,
    Function.Bijective Y.mulVec ∧ iota F Θ Zs P ψ t = iota F Θ Zs P ψ F.μ0 ∘ₗ cx F.v0 Y

def OneFormAt : Prop := ∀ t : T, KernelIsTrivial F Θ Zs P ψ t ∧ RatTransition F Θ Zs P ψ t

def OneFormPrincipal : Prop := OneFormAt F Θ Zs ⊥ 1

end Data

def OneFormPassage : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (G : Type) [Group G] [Fintype G]
    (Pl0 T J : Type) [Fintype J] (F : DefFam K G Pl0 T J) (s : ℕ), F.Ok s →
  ∀ (Zs : DefSub F.amb), (∀ (t : T) (g : G), Zs.Z t ≤ (Zs.Z t).comap ((F.R t).r g)) →
  ∀ (EE : Type) [AddCommGroup EE] [Module ℂ EE] (ρ : Representation ℂ G EE)
    (Θ : ∀ t : T, (Fin (F.R t).S.dim → ℂ) →ₗ[ℂ] EE), Equivariant F ρ Θ →
  ∀ (P : Subgroup G) (ψ : P →* Kˣ), Generic F.X P ψ →
    OneFormAt F Θ Zs P ψ → OneFormPrincipal F Θ Zs

example (χ : G → K) : mult (⊥ : Subgroup G) 1 χ = χ 1 := by
  classical
  unfold mult
  rw [Finset.sum_eq_single (1 : (⊥ : Subgroup G))]
  · rw [Subgroup.card_bot]; simp only [Nat.cast_one, inv_one, MonoidHom.one_apply, Units.val_one, one_mul,
      OneMemClass.coe_one]
  · intro b _ hb; exact absurd (Subsingleton.elim b 1) hb
  · intro h; exact absurd (@Finset.mem_univ _ (_) _) h

example (F : DefFam K G Pl0 T J) {EE : Type} [AddCommGroup EE] [Module ℂ EE]
    (Θ : ∀ t : T, (Fin (F.R t).S.dim → ℂ) →ₗ[ℂ] EE) (Zs : DefSub F.amb) (P : Subgroup G) (ψ : P →* Kˣ) :
    RatTransition F Θ Zs P ψ F.μ0 := by
  refine ⟨1, ?_, ?_⟩
  · have : (1 : Matrix (Fin ((F.R F.μ0).dZ (F.lvl P ψ) (Zs.Z F.μ0))) _ K).mulVec = id :=
      funext fun x => Matrix.one_mulVec x
    rw [this]; exact Function.bijective_id
  · ext1
    simp [cx, Matrix.map_one]

end GlobalTheory.IndefiniteRowSideFullHecke.RationalTransitionKernel
