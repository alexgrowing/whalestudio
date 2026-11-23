import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HenselianStabilizerConjugacy.LatticeCountingFormulaAlt

noncomputable section

open scoped Classical
open ValuativeRel

namespace PI.SelfDualHermitianLattices

open Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG Formalism.L2.SG.NGDict

section Ler

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V]

def tupMul {m : ℕ} (y : Fin m → V) (A : Matrix (Fin m) (Fin m) M.L.O) : Fin m → V :=
  fun a => ∑ i, ((A i a : M.L.O) : E) • y i

def lerCnt (H : HermSp M V) (Λs : Submodule M.L.O V) (ϖ : 𝒪[F]) (J : ℕ) {m : ℕ}
    (A : Matrix (Fin m) (Fin m) M.L.O) (Gm : Matrix (Fin m) (Fin m) E) : ℕ :=
  Nat.card {c : Fin m → (Λs ⧸ piIn H (ϖ ^ J) Λs) //
    ∃ x y : Fin m → Λs, (∀ a, Submodule.Quotient.mk (x a) = c a) ∧ PrimTup H Λs y ∧
      (fun a => (x a : V)) = tupMul (fun i => (y i : V)) A ∧ GramCong H (ϖ ^ J) (fun a => (x a : V)) Gm}

def ler (H : HermSp M V) (Λs : Submodule M.L.O V) (ϖ : 𝒪[F]) (J : ℕ) {m : ℕ}
    (A : Matrix (Fin m) (Fin m) M.L.O) (Gm : Matrix (Fin m) (Fin m) E) : ℝ :=
  (lerCnt H Λs ϖ J A Gm : ℝ) / (qF F : ℝ) ^ (J * (2 * Module.finrank E V * m - m ^ 2))

end Ler

def LatticeUnfoldingLerayVolume : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    (E : Type) [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Model F E), M.OK →
    ∀ (V : Type) [AddCommGroup V] [Module E V] (H : HermSp M V) (m : ℕ) (ff : Fin m → V),
      IsUnit (H.gram ff).det →
      ∀ (Λs : Submodule M.L.O V), IsSelfDual H Λs → ∀ ϖ : 𝒪[F], Irreducible ϖ →
      ∀ K : Subgroup (V ≃ₗ[E] V), K ≤ fixZ H (Submodule.span E (Set.range ff)) →
        Commens K (fixZ H (Submodule.span E (Set.range ff)) ⊓ Aut Λs) →
      ∃ κ : ℝ, 0 < κ ∧
        ∀ (b : Fin m → V) (A : Matrix (Fin m) (Fin m) M.L.O), (∀ a, b a ∈ Submodule.span E (Set.range ff)) →
          ff = tupMul b A →
          ∀ Rs : Set (Submodule M.L.O V),
            IsTransv (OrbRel (fixZ H (Submodule.span E (Set.range ff))))
              (SigZ H (Submodule.span E (Set.range ff)) (Submodule.span M.L.O (Set.range b))) Rs →
            ∃ J0 : ℕ, ∀ J, J0 ≤ J →
              massOf (fixZ H (Submodule.span E (Set.range ff))) K Rs =
                ENNReal.ofReal (κ * ler H Λs ϖ J A (H.gram ff))

def LatticeRescalingMassFormula : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    (E : Type) [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Model F E), M.OK →
    ∀ (V : Type) [AddCommGroup V] [Module E V] (H : HermSp M V) (m : ℕ) (ff : Fin m → V),
      IsUnit (H.gram ff).det →
      ∀ (Λs : Submodule M.L.O V), IsSelfDual H Λs → ∀ ϖ : 𝒪[F], Irreducible ϖ →
      ∀ (b : Fin m → V) (A : Matrix (Fin m) (Fin m) M.L.O), ff = tupMul b A →
        ∃ J0 : ℕ, ∀ J, J0 ≤ J →
          ler H Λs ϖ J A (H.gram ff) = ((idx M ff b : ℝ) ^ (Module.finrank E V - m))⁻¹ * dl H Λs ϖ (H.gram b)

end PI.SelfDualHermitianLattices

end
