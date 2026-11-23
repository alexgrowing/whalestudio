import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.PolyApproxZeroPadic
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPsCharOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteSemisimple
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DetSuccEqSubSumUpdateRow
open Formalism.MainNotions.N GlobalTheory.Cong GlobalTheory.PsChar

noncomputable section

namespace GlobalTheory.PsChar

open MvPolynomial

theorem aeval_eq_zero_of_polyApprox {k : Type} [NormedField k] [IsUltrametricDist k] {J : Type} {θ : J → k}
    {S : Set (J → k)} (h : PolyApprox θ S) (P : MvPolynomial J ℤ) (hP : ∀ η ∈ S, aeval η P = 0) :
    aeval θ P = 0 := by
  refine norm_le_zero_iff.1 (le_of_forall_pos_le_add fun ε hε => ?_)
  obtain ⟨s, c, hs, hb⟩ := h ε hε
  have hz : ∑ η ∈ s, c η * aeval η P = 0 :=
    Finset.sum_eq_zero fun η hη => by rw [hP η (hs hη), mul_zero]
  have := hb P
  rw [hz, sub_zero] at this
  simpa using this

theorem isPsChar_trc {Γ A : Type} [Group Γ] [CommRing A] (a : ℕ) (ρ : Γ →* GL (Fin a) A) : IsPsChar a (trc ρ) :=
  isPsChar_trace Γ A a ((Units.coeHom (Matrix (Fin a) (Fin a) A)).comp ρ)

theorem isPsChar_of_polyApprox_trc : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] (a : ℕ) (T : Γ → PadicAlgCl l)
    (C : Set (Γ →* GL (Fin a) (PadicAlgCl l))), PolyApprox T (trc '' C) → IsPsChar a T := by
  intro l _ Γ _ a T C h
  have key : ∀ P : MvPolynomial Γ ℤ, (∀ ρ ∈ C, aeval (trc ρ) P = 0) → aeval T P = 0 := fun P hP =>
    aeval_eq_zero_of_polyApprox h P (by rintro η ⟨ρ, hρ, rfl⟩; exact hP ρ hρ)
  have hm : ∀ (η : Γ → PadicAlgCl l) (x : Fin (a + 1) → Γ),
      aeval η (alt (fun g => (X g : MvPolynomial Γ ℤ)) (a + 1) x) = alt η (a + 1) x := fun η x => by
    have := map_alt (aeval η).toRingHom (fun g => (X g : MvPolynomial Γ ℤ)) (a + 1) x
    simpa using this
  refine ⟨?_, ?_, ?_⟩
  · have := key (X 1 - (a : MvPolynomial Γ ℤ)) fun ρ _ => by simp [(isPsChar_trc a ρ).one]
    simpa [sub_eq_zero] using this
  · intro x y
    have := key (X (x * y) - X (y * x)) fun ρ _ => by simp [(isPsChar_trc a ρ).comm x y]
    simpa [sub_eq_zero] using this
  · intro x
    have := key _ fun ρ _ => by rw [hm]; exact (isPsChar_trc a ρ).alt_eq_zero x
    rwa [hm] at this

example : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] (a : ℕ) (T : Γ → PadicAlgCl l)
    (C : Set (Γ →* GL (Fin a) (PadicAlgCl l))), PolyApprox T (trc '' C) → IsPsChar a T :=
  isPsChar_of_polyApprox_trc

end GlobalTheory.PsChar

end
