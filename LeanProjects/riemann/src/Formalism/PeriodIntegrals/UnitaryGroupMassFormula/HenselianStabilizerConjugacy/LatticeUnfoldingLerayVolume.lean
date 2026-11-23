import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HenselianStabilizerConjugacy.LatticeCountingFormula
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HenselianStabilizerConjugacy.SelfDualLatticesOneOrbit

noncomputable section

open scoped Classical
open ValuativeRel

namespace PI.SelfDualHermitianLattices

open Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG Formalism.L2.SG.NGDict

namespace Hg

section TupDefs

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V]

def UGrp (H : HermSp M V) : Subgroup (V ≃ₗ[E] V) where
  carrier := {g | IsUnitary H g}
  mul_mem' {a b} ha hb x y := by
    change H.h (a (b x)) (a (b y)) = H.h x y
    rw [ha (b x) (b y), hb x y]
  one_mem' x y := rfl
  inv_mem' {a} ha x y := by
    have h1 : ∀ v, a (a⁻¹ v) = v := fun v => by
      rw [← LinearEquiv.mul_apply, mul_inv_cancel]; rfl
    change H.h (a⁻¹ x) (a⁻¹ y) = H.h x y
    rw [← ha (a⁻¹ x) (a⁻¹ y), h1, h1]

def FixT {m : ℕ} (x : Fin m → V) : Subgroup (V ≃ₗ[E] V) where
  carrier := {g | ∀ a, g (x a) = x a}
  mul_mem' {a b} ha hb i := by
    change a (b (x i)) = x i
    rw [hb i, ha i]
  one_mem' _ := rfl
  inv_mem' {a} ha i := by
    change a⁻¹ (x i) = x i
    conv_lhs => rw [← ha i]
    rw [← LinearEquiv.mul_apply, inv_mul_cancel]; rfl

def StabT (H : HermSp M V) {m : ℕ} (x : Fin m → V) : Subgroup (V ≃ₗ[E] V) := UGrp H ⊓ FixT x

def KsOf (H : HermSp M V) (Λs : Submodule M.L.O V) : Subgroup (V ≃ₗ[E] V) := UGrp H ⊓ Aut Λs

def actT {m : ℕ} (g : V ≃ₗ[E] V) (x : Fin m → V) : Fin m → V := fun a => g (x a)

def KsRel (H : HermSp M V) (Λs : Submodule M.L.O V) {m : ℕ} (x x' : Fin m → V) : Prop :=
  ∃ k ∈ KsOf H Λs, actT k x = x'

def XS (H : HermSp M V) (Λs : Submodule M.L.O V) {m : ℕ} (ff : Fin m → V)
    (A : Matrix (Fin m) (Fin m) M.L.O) : Set (Fin m → V) :=
  {x | H.gram x = H.gram ff ∧ ∃ y : Fin m → Λs, PrimTup H Λs y ∧ x = tupMul (fun i => (y i : V)) A}

def conjSub (g : V ≃ₗ[E] V) (K : Subgroup (V ≃ₗ[E] V)) : Subgroup (V ≃ₗ[E] V) :=
  K.comap (MulAut.conj g).toMonoidHom

end TupDefs

end Hg

open Hg

def WittT : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    (E : Type) [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Model F E), M.OK →
    ∀ (V : Type) [AddCommGroup V] [Module E V] (H : HermSp M V) (m : ℕ) (x x' : Fin m → V),
      IsUnit (H.gram x).det → H.gram x = H.gram x' →
      ∃ g : V ≃ₗ[E] V, IsUnitary H g ∧ ∀ a, g (x a) = x' a

def SatPrim : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    (E : Type) [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Model F E), M.OK →
    ∀ (V : Type) [AddCommGroup V] [Module E V] (H : HermSp M V) (Λ : Submodule M.L.O V), IsSelfDual H Λ →
      ∀ (m : ℕ) (y : Fin m → Λ), IsUnit (H.gram (fun a => (y a : V))).det →
        Λ ⊓ (Submodule.span E (Set.range (fun a => (y a : V)))).restrictScalars M.L.O =
          Submodule.span M.L.O (Set.range (fun a => (y a : V))) →
        PrimTup H Λ y

def LVX : Prop :=
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
          ∀ Xs : Set (Fin m → V), IsTransv (KsRel H Λs) (XS H Λs ff A) Xs →
          ∀ gx : (Fin m → V) → (V ≃ₗ[E] V), (∀ x ∈ Xs, IsUnitary H (gx x) ∧ actT (gx x) x = ff) →
            ∃ J0 : ℕ, ∀ J, J0 ≤ J →
              (∑' x : Xs, ENNReal.ofReal (1 / volRel (StabT H (x : Fin m → V) ⊓ KsOf H Λs)
                  (conjSub (gx x) K))) =
                ENNReal.ofReal (κ * ler H Λs ϖ J A (H.gram ff))

end PI.SelfDualHermitianLattices
