import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HenselianStabilizerConjugacy.IsSelfDual

noncomputable section

open scoped Classical
open ValuativeRel

namespace PI.SelfDualHermitianLattices

open Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG Formalism.L2.SG.NGDict

section ObjJ

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V]

def fixZ (H : HermSp M V) (Z : Submodule E V) : Subgroup (V ≃ₗ[E] V) :=
  Subgroup.closure {g | IsUnitary H g ∧ ∀ v ∈ Z, g v = v}

def Commens {G : Type*} [Group G] (K K' : Subgroup G) : Prop :=
  K.relIndex K' ≠ 0 ∧ K'.relIndex K ≠ 0

def OrbRel (G : Subgroup (V ≃ₗ[E] V)) (Λ Λ' : Submodule M.L.O V) : Prop :=
  ∃ g ∈ G, img g Λ = Λ'

def massOf (G K : Subgroup (V ≃ₗ[E] V)) (Rs : Set (Submodule M.L.O V)) : ENNReal :=
  ∑' Λ : Rs, ENNReal.ofReal (1 / volRel (G ⊓ Aut (Λ : Submodule M.L.O V)) K)

def SigZ (H : HermSp M V) (Z : Submodule E V) (Mh : Submodule M.L.O V) : Set (Submodule M.L.O V) :=
  {Λ | IsSelfDual H Λ ∧ Λ ⊓ Z.restrictScalars M.L.O = Mh}

def piIn (H : HermSp M V) (ϖ : 𝒪[F]) (Λs : Submodule M.L.O V) : Submodule M.L.O Λs :=
  (H.smulLat (algebraMap F E (ϖ : F)) Λs).comap Λs.subtype

def PrimTup (H : HermSp M V) (Λs : Submodule M.L.O V) {m : ℕ} (x : Fin m → Λs) : Prop :=
  ∀ c : Fin m → M.L.O, ∃ y ∈ Λs, ∀ a, H.h y (x a : V) = (c a : E)

def GramCong (H : HermSp M V) (ϖ : 𝒪[F]) {m : ℕ} (x : Fin m → V) (Gm : Matrix (Fin m) (Fin m) E) : Prop :=
  ∀ a b, ∃ e ∈ M.L.O, H.h (x b) (x a) - Gm a b = algebraMap F E (ϖ : F) * e

def dlCount (H : HermSp M V) (Λs : Submodule M.L.O V) (ϖ : 𝒪[F]) {m : ℕ} (Gm : Matrix (Fin m) (Fin m) E) : ℕ :=
  Nat.card {c : Fin m → (Λs ⧸ piIn H ϖ Λs) //
    ∃ x : Fin m → Λs, (∀ a, Submodule.Quotient.mk (x a) = c a) ∧ PrimTup H Λs x ∧
      GramCong H ϖ (fun a => (x a : V)) Gm}

def dl (H : HermSp M V) (Λs : Submodule M.L.O V) (ϖ : 𝒪[F]) {m : ℕ} (Gm : Matrix (Fin m) (Fin m) E) : ℝ :=
  (dlCount H Λs ϖ Gm : ℝ) / (qF F : ℝ) ^ (2 * Module.finrank E V * m - m ^ 2)

def idx (M : Model F E) {m : ℕ} (ff b : Fin m → V) : ℕ :=
  Nat.card (Submodule.span M.L.O (Set.range b) ⧸
    (Submodule.span M.L.O (Set.range ff)).comap (Submodule.span M.L.O (Set.range b)).subtype)

end ObjJ

def LatticeCountingFormula : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    (E : Type) [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Model F E), M.OK →
    ∀ (V : Type) [AddCommGroup V] [Module E V] (H : HermSp M V) (m : ℕ) (ff : Fin m → V),
      IsUnit (H.gram ff).det →
      ∀ (Λs : Submodule M.L.O V), IsSelfDual H Λs → ∀ ϖ : 𝒪[F], Irreducible ϖ →
      ∀ K : Subgroup (V ≃ₗ[E] V), K ≤ fixZ H (Submodule.span E (Set.range ff)) →
        Commens K (fixZ H (Submodule.span E (Set.range ff)) ⊓ Aut Λs) →
      ∃ κ : ℝ, 0 < κ ∧
        ∀ b : Fin m → V, (∀ a, b a ∈ Submodule.span E (Set.range ff)) →
          (∀ a, ff a ∈ Submodule.span M.L.O (Set.range b)) →
          ∀ Rs : Set (Submodule M.L.O V),
            IsTransv (OrbRel (fixZ H (Submodule.span E (Set.range ff))))
              (SigZ H (Submodule.span E (Set.range ff)) (Submodule.span M.L.O (Set.range b))) Rs →
            massOf (fixZ H (Submodule.span E (Set.range ff))) K Rs =
              ENNReal.ofReal (κ * ((idx M ff b : ℝ) ^ (Module.finrank E V - m))⁻¹ * dl H Λs ϖ (H.gram b))

end PI.SelfDualHermitianLattices

end
