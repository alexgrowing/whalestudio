import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasBlockOfOccurs
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.CuspRep

namespace GlobalTheory.GalDef

def wAt {n : ℕ} (lam : DomWeight n) (k : ℕ) : ℤ := if h : k < n then lam.w ⟨k, h⟩ else 0

def IsRunAt {n : ℕ} (lam : DomWeight n) (p t : ℕ) : Prop :=
  p + t ≤ n ∧ (∀ k, p ≤ k → k < p + t → wAt lam k = wAt lam p) ∧ (1 ≤ p → wAt lam p < wAt lam (p - 1)) ∧
    (p + t < n → wAt lam (p + t) < wAt lam p)

variable {E Ω : Type} [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}

def jumpsOf (ι : Qbar l ≃+* ℂ) (lam : (E →+* ℂ) → DomWeight n) (τ : E →+* Qbar l) : Multiset ℤ :=
  Finset.univ.val.map fun k : Fin n => (k : ℤ) - (lam (ι.toRingHom.comp τ)).w k

def FrobSat (ι : Qbar l ≃+* ℂ) (π : Submodule ℂ (UA E n → ℂ)) (sgn : ℤˣ) (cp : G E Ω → Polynomial (Qbar l)) : Prop :=
  ∀ w : HeightOneSpectrum (𝓞 E), IsSplitAt w → ((l : ℕ) : 𝓞 E) ∉ w.asIdeal → IsUnramU π w →
    ∀ (σ : SmIrr (GL (Fin n) (w.adicCompletion E))) (T : Multiset ℂˣ),
      IsCompAlong π (locU n w) ((cLoc w).comp (locU n w).subtype) σ.ρ → GlobalTheory.LFun.HasSatGL w σ.ρ T →
      ∀ (B : ValuationSubring Ω) (g : G E Ω), IsPlaceOver (F := E) B w → IsFrob (F := E) B (normV w) g →
        cp (g ^ (sgn : ℤ)) = (T.map fun z : ℂˣ =>
          X - C (ι.symm ((z : ℂ) * ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (((n : ℂ) - 1) / 2)))).prod

def HasString (l : ℕ) (π : Submodule ℂ (UA E n → ℂ)) (t : ℕ) : Prop :=
  ∃ w : HeightOneSpectrum (𝓞 E), IsSplitAt w ∧ ((l : ℕ) : 𝓞 E) ∉ w.asIdeal ∧ IsUnramU π w ∧
    ∃ (σ : SmIrr (GL (Fin n) (w.adicCompletion E))) (T : Multiset ℂˣ) (ν : ℂ),
      IsCompAlong π (locU n w) ((cLoc w).comp (locU n w).subtype) σ.ρ ∧ GlobalTheory.LFun.HasSatGL w σ.ρ T ∧ ‖ν‖ = 1 ∧
        (Multiset.range t).map (fun c : ℕ => ν * ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (((t : ℂ) - 1) / 2 - c)) ≤
          T.map fun z : ℂˣ => (z : ℂ)

example : IsRunAt (n := 3) ⟨![1, 1, 0], by
    intro a b h; fin_cases a <;> fin_cases b <;> simp_all [Fin.le_def]⟩ 0 2 := by
  refine ⟨by norm_num, fun k h1 h2 => ?_, fun h => absurd h (by norm_num), fun _ => ?_⟩
  · interval_cases k <;> simp [wAt]
  · simp [wAt]

end GlobalTheory.GalDef

end
