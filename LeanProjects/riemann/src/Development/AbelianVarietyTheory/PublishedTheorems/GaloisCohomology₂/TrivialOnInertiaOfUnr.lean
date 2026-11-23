import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DataN

noncomputable section

namespace GlobalTheory.GalOfCusp

open Formalism.BasicNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial
open scoped Matrix

section Polarization

variable {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] {k : Type} [Field k] {a : ℕ}

def IsConjDual (c : Ω ≃+* Ω) (r : G E Ω →* GL (Fin a) k) (μ : G E Ω →* kˣ) : Prop :=
  ∃ P : GL (Fin a) k, ∀ g g' : G E Ω, (∀ x, g' x = c (g (c.symm x))) →
    (r g' : Matrix (Fin a) (Fin a) k) =
      (μ g : k) • ((P : Matrix (Fin a) (Fin a) k) * (r g⁻¹ : Matrix (Fin a) (Fin a) k)ᵀ *
        ((P⁻¹ : GL (Fin a) k) : Matrix (Fin a) (Fin a) k))

theorem IsConjDual.trace {c : Ω ≃+* Ω} {r : G E Ω →* GL (Fin a) k} {μ : G E Ω →* kˣ} (h : IsConjDual c r μ)
    {g g' : G E Ω} (hg : ∀ x, g' x = c (g (c.symm x))) :
    (r g' : Matrix (Fin a) (Fin a) k).trace = μ g * (r g⁻¹ : Matrix (Fin a) (Fin a) k).trace := by
  obtain ⟨P, hP⟩ := h
  rw [hP g g' hg, Matrix.trace_smul, Matrix.trace_mul_cycle, ← Units.val_mul, inv_mul_cancel, Units.val_one,
    one_mul, Matrix.trace_transpose, smul_eq_mul]

theorem isConjDual_one (c : Ω ≃+* Ω) : IsConjDual c (1 : G E Ω →* GL (Fin a) k) 1 :=
  ⟨1, fun _ _ _ => by simp⟩

variable (E Ω) in

def cycBar (l : ℕ) [Fact l.Prime] : G E Ω →* (Qbar l)ˣ :=
  (Units.map ((algebraMap ℚ_[l] (Qbar l)).comp PadicInt.Coe.ringHom).toMonoidHom).comp (cycZ E Ω l)

end Polarization

section Record

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} (A : NAut N)

def RegAlgShift {a : ℕ} (π : A.CG a) (s : ℝ) : Prop :=
  ∀ τ, (A.infG π τ).Nodup ∧ ∀ z ∈ A.infG π τ, ∃ m : ℤ, z + (s : ℂ) = (m : ℂ) + ((a : ℂ) - 1) / 2

theorem regAlgShift_zero {a : ℕ} (π : A.CG a) : RegAlgShift A π 0 ↔ A.ralg π := by
  rw [A.ralg_def, RegAlgShift]
  simp

def TrivialOnInertia {w : PlE H} (L : A.LP w) : Prop :=
  ∀ σ ∈ Ine (F := H.E) (N.plOm.1 w), A.inePol L σ = (X - 1) ^ A.lpDim L

structure IsAttached (i : N.Loc) {a : ℕ} (π : A.CG a) (s : ℝ) (r : G H.E N.Om →* GL (Fin a) (Qbar (N.l i))) :
    Prop where

  cont : Continuous fun g => (r g : Matrix (Fin a) (Fin a) (Qbar (N.l i)))

  ss : IsSSRep r

  pol : ∀ c : N.Om ≃+* N.Om, IsCMConjOm H.E N.Om c → ∀ m : ℤ, (m : ℝ) = 2 * s →
    IsConjDual c r (cycBar H.E N.Om (N.l i) ^ (1 - (a : ℤ) + m))

  away : ∀ w, w ∉ placesOver H.E (N.l i) → A.wdOf i r w = A.lpTw (A.locG π w) (s + (1 - (a : ℝ)) / 2)

  pure : ∀ w, w ∉ placesOver H.E (N.l i) → A.tempered (A.lpTw (A.wdOf i r w) (((a : ℝ) - 1) / 2 - s))

  deRham : ∀ w ∈ placesOver H.E (N.l i), A.IsdRW i r w

  jumps : ∀ τ : H.E →+* Qbar (N.l i), (A.jumpsW i r τ).map (fun n : ℤ => (n : ℂ)) =
    (A.infG π ((A.iotaQC i).toRingHom.comp τ)).map fun z => -(z + (s : ℂ)) + ((a : ℂ) - 1) / 2

  iwahori : ∀ w ∈ placesOver H.E (N.l i), TrivialOnInertia A (A.locG π w) →
    A.wdOf i r w = A.lpTw (A.locG π w) (s + (1 - (a : ℝ)) / 2)

  crys : ∀ w ∈ placesOver H.E (N.l i), A.unr (A.locG π w) → A.IsCrysW i r w

def Reading : Prop :=
  ∀ (i : N.Loc) (a : ℕ), 1 ≤ a → ∀ π : A.CG a, A.csd π → ∀ s : ℝ, RegAlgShift A π s →
    ∃ r, IsAttached A i π s r

variable {A}

variable {i : N.Loc} {a : ℕ} {π : A.CG a} {s : ℝ} {r : G H.E N.Om →* GL (Fin a) (Qbar (N.l i))}

theorem IsAttached.tempered (h : IsAttached A i π s r) {w : PlE H} (hw : w ∉ placesOver H.E (N.l i)) :
    A.tempered (A.locG π w) := by
  have := h.pure w hw
  rwa [h.away w hw, A.lpTw_add, show s + (1 - (a : ℝ)) / 2 + (((a : ℝ) - 1) / 2 - s) = 0 by ring,
    A.lpTw_zero] at this

theorem IsAttached.pol_zero (h : IsAttached A i π 0 r) {c : N.Om ≃+* N.Om} (hc : IsCMConjOm H.E N.Om c) :
    IsConjDual c r (cycBar H.E N.Om (N.l i) ^ (1 - (a : ℤ))) := by
  simpa using h.pol c hc 0 (by simp)

theorem IsAttached.frob (h : IsAttached A i π s r) {w : PlE H} (hw : w ∉ placesOver H.E (N.l i))
    (hu : A.unr (A.locG π w)) :
    (∀ σ ∈ Ine (F := H.E) (N.plOm.1 w), r σ = 1) ∧
    ∀ (B : ValuationSubring N.Om) (σ : G H.E N.Om), IsPlaceOver (F := H.E) B w →
      IsFrob (F := H.E) B (normV w) σ →
      (r σ : Matrix (Fin a) (Fin a) (Qbar (N.l i))).charpoly.map (A.iotaQC i).toRingHom =
        galPol A (A.lpTw (A.locG π w) (s + (1 - (a : ℝ)) / 2)) := by
  have h1 : A.unr (A.wdOf i r w) := by rw [h.away w hw]; exact (A.unr_tw _ _).2 hu
  refine ⟨(A.wdOf_unr i r w hw h.cont).1 h1, fun B σ hB hσ => ?_⟩
  rw [A.wdOf_frob i r w hw h.cont h1 B σ hB hσ, h.away w hw]
  rfl

end Record

end GlobalTheory.GalOfCusp

end
