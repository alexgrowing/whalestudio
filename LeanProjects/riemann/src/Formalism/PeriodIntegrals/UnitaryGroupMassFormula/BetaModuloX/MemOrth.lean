import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BetaModuloX.Skeleton
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BetaUniqueness.Lemmas
import Formalism.HermitianLattices.HermitianLatticesProofs.AutFinite

noncomputable section

open scoped Classical

open NumberField Module Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat

namespace PI.UnitaryGroupMassFormula.BetaModX

section Q

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T' : E}

theorem mem_orth' {U : Submodule E S.V} {v : S.V} : v ∈ orth S U ↔ ∀ x ∈ U, S.hT x v = 0 := by
  simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker]

theorem herm' (x y : S.V) : S.hT y x = star (S.hT x y) := by
  rw [← S.herm.eq x y, starRingEnd_apply]

theorem hXz (F' : LFlag S r T') : ∀ x ∈ Xsp F', S.hT x F'.fl.z = 0 := by
  intro x hx
  change x ∈ Submodule.span E (Set.range F'.fl.e) at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨j, rfl⟩ := hy
    exact F'.fl.z_orth j
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, LinearMap.add_apply, hx, hy, add_zero]
  | smul a x _ hx => rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, hx, smul_zero]

theorem hzX (F' : LFlag S r T') : ∀ x ∈ Xsp F', S.hT F'.fl.z x = 0 := by
  intro x hx
  rw [herm', hXz F' x hx, star_zero]

abbrev Uo (F' : LFlag S r T') : Submodule E S.V := orth S (Xsp F')

abbrev Pk (F' : LFlag S r T') : Submodule E (Uo F') := (Xsp F').comap (Uo F').subtype

abbrev Qt (F' : LFlag S r T') : Type := (Uo F') ⧸ (Pk F')

def hV (F' : LFlag S r T') (c : E) : S.V →ₗ⋆[E] S.V →ₗ[E] E :=
  LinearMap.mk₂'ₛₗ (starRingEnd E) (RingHom.id E)
    (fun a b => S.hT a b + c * (S.hT a F'.fl.z * S.hT F'.fl.z b))
    (fun a a' b => by simp only [map_add, LinearMap.add_apply]; ring)
    (fun t a b => by simp only [LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul]; ring)
    (fun a b b' => by simp only [map_add]; ring)
    (fun t a b => by simp only [map_smul, smul_eq_mul, RingHom.id_apply]; ring)

theorem hV_apply (F' : LFlag S r T') (c : E) (a b : S.V) :
    hV F' c a b = S.hT a b + c * (S.hT a F'.fl.z * S.hT F'.fl.z b) := rfl

def hU (F' : LFlag S r T') (c : E) : Uo F' →ₗ⋆[E] Uo F' →ₗ[E] E :=
  LinearMap.mk₂'ₛₗ (starRingEnd E) (RingHom.id E) (fun a b => hV F' c (a : S.V) (b : S.V))
    (fun a a' b => by simp)
    (fun t a b => by simp)
    (fun a b b' => by simp)
    (fun t a b => by simp)

theorem hU_apply (F' : LFlag S r T') (c : E) (a b : Uo F') : hU F' c a b = hV F' c a b := rfl

theorem hU_left (F' : LFlag S r T') (c : E) (a b : Uo F') (ha : (a : S.V) ∈ Xsp F') : hU F' c a b = 0 := by
  rw [hU_apply, hV_apply, (mem_orth'.mp b.2) a ha, hXz F' a ha]
  ring

theorem hU_right (F' : LFlag S r T') (c : E) (a b : Uo F') (hb : (b : S.V) ∈ Xsp F') : hU F' c a b = 0 := by
  rw [hU_apply, hV_apply, herm' (b : S.V) (a : S.V), (mem_orth'.mp a.2) b hb, hzX F' b hb]
  simp

def hQ1 (F' : LFlag S r T') (c : E) : Qt F' →ₗ[E] Uo F' →ₗ⋆[E] E :=
  (Pk F').liftQ (hU F' c).flip (by
    intro b hb
    rw [LinearMap.mem_ker]
    ext a
    exact hU_right F' c a b hb)

def hQ (F' : LFlag S r T') (c : E) : Qt F' →ₗ⋆[E] Qt F' →ₗ[E] E :=
  (Pk F').liftQ (hQ1 F' c).flip (by
    intro a ha
    rw [LinearMap.mem_ker]
    ext b
    exact hU_left F' c a b ha)

theorem hQ_mk (F' : LFlag S r T') (c : E) (a b : Uo F') :
    hQ F' c (Submodule.Quotient.mk a) (Submodule.Quotient.mk b) = hV F' c a b := rfl

end Q

end PI.UnitaryGroupMassFormula.BetaModX
