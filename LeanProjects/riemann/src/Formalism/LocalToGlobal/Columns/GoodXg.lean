import Mathlib
import Formalism.LocalToGlobal.Columns.AbelianHostFieldConditions
import Formalism.LocalToGlobal.Columns.RowForms
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Formalism.LocalToGlobal.Divisibility.GoodPartHermitianSpec
import Formalism.LocalToGlobal.Columns.GoodXgFin

open NumberField IsDedekindDomain Polynomial

noncomputable section

namespace Formalism.L2.Col

open Formalism.L2.DIV

section Good

variable {X : Fields} (Pr : Primes X)

theorem gxMemGs (i : Fin 2) {w : HeightOneSpectrum (𝓞 X.E)} (h : w ∈ Pr.vG i) : w ∈ Pr.vGs := by
  classical
  unfold Primes.vGs
  rw [Finset.mem_union]
  match i, h with
  | 0, h => exact Or.inl h
  | 1, h => exact Or.inr h

variable {m : ℕ} (Ch : Chars X Pr m) (r : ℕ) [∀ i, Fact (Pr.g i).Prime]
  (σ : X.K →+* ℂ) (teich : ∀ i : Fin 2, Formalism.CyclotomicNorms.Fbar (Pr.g i) →* ℂ) (ζ : ∀ i : Fin 2, ℕ → Formalism.CyclotomicNorms.Fbar (Pr.g i))

def gxLoc (i : Fin 2) (w : HeightOneSpectrum (𝓞 X.E)) (χw : GL (Fin r) (𝓞 X.E ⧸ w.asIdeal) → ℂ)
    (f : (ZMod (Pr.g i))[X]) : Prop :=
  ∃ e : (𝓞 X.E ⧸ w.asIdeal) ≃+* ZMod (Pr.g i),
    Formalism.L2.NT.IsIrrChar (fun x : GL (Fin r) (ZMod (Pr.g i)) => χw (Matrix.GeneralLinearGroup.map e.symm.toRingHom x)) ∧
      Formalism.L2.NT.InSeries (teich i) (ζ i)
        (fun x : GL (Fin r) (ZMod (Pr.g i)) => χw (Matrix.GeneralLinearGroup.map e.symm.toRingHom x)) f

def gxChiLab (i : Fin 2) (w : {w // w ∈ Pr.vGs}) (j : Fin m) (a : (ZMod (Pr.g i))ˣ) : Prop :=
  ∃ (e : (𝓞 X.E ⧸ w.1.asIdeal) ≃+* ZMod (Pr.g i)) (k : ℕ),
    (∀ x : (ZMod (Pr.g i))ˣ, σ ((Ch.chi j w (Units.map e.symm.toRingHom.toMonoidHom x) : X.Kˣ) : X.K) =
      teich i (algebraMap (ZMod (Pr.g i)) (Formalism.CyclotomicNorms.Fbar (Pr.g i)) (x : ZMod (Pr.g i))) ^ k) ∧
    algebraMap (ZMod (Pr.g i)) (Formalism.CyclotomicNorms.Fbar (Pr.g i)) (a : ZMod (Pr.g i)) = ζ i 1 ^ k

def gxGoodLab (i : Fin 2) (f : {w // w ∈ Pr.vG i} → (ZMod (Pr.g i))[X]) : Prop :=
  ∃ a : {w // w ∈ Pr.vG i} → Fin m → (ZMod (Pr.g i))ˣ,
    (∀ w j, gxChiLab Pr Ch σ teich ζ i ⟨w.1, gxMemGs Pr i w.2⟩ j (a w j)) ∧
      Formalism.CyclotomicNorms.IsGood r (Pr.g i) f a ∧ Formalism.CyclotomicNorms.IsGood r (Pr.g i) f (fun w j => (a w j)⁻¹)

def gxGood (χc : G0 X.E Pr.vGs r → ℂ) : Prop :=
  ∃ (χw : ∀ w : {w // w ∈ Pr.vGs}, GL (Fin r) (𝓞 X.E ⧸ w.1.asIdeal) → ℂ)
    (f : ∀ i : Fin 2, {w // w ∈ Pr.vG i} → (ZMod (Pr.g i))[X]),
    (∀ x : G0 X.E Pr.vGs r, χc x = ∏ w, χw w (x w)) ∧
      (∀ (i : Fin 2) (w : {w // w ∈ Pr.vG i}),
        gxLoc Pr r teich ζ i w.1 (χw ⟨w.1, gxMemGs Pr i w.2⟩) (f i w)) ∧
      ∀ i : Fin 2, gxGoodLab Pr Ch r σ teich ζ i (f i)

def XgSet : Set (G0 X.E Pr.vGs r → X.K) :=
  {χ | IsAbsIrrChar χ ∧ gxGood Pr Ch r σ teich ζ (fun x => σ (χ x))}

theorem XgSet_finite : (XgSet Pr Ch r σ teich ζ).Finite :=
  (absIrrChar_finite (G := G0 X.E Pr.vGs r) (K := X.K)).subset fun _ h => h.1

def XgC : Finset (G0 X.E Pr.vGs r → X.K) := (XgSet_finite Pr Ch r σ teich ζ).toFinset

end Good

end Formalism.L2.Col
