import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsFibreNormPullback
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

noncomputable section

section Defs

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [CharZero Ω]

def pullField (y : (Σ k, ι k) → Ω) {D : ℕ} (L : Fin (D + 1) → MRing ι) : IntermediateField ℚ Ω :=
  IntermediateField.adjoin ℚ {x | ∃ i j, aeval y (L j) ≠ 0 ∧ x = aeval y (L i) / aeval y (L j)}

def IsNormForms (y : (Σ k, ι k) → Ω) {D : ℕ} (L : Fin (D + 1) → MRing ι) (m : ℕ) (s : Ω)
    (c : ℕ → MvPolynomial (Fin (D + 1)) ℚ) : Prop :=
  ∃ _ : FiniteDimensional (pullField y L) Ω,
    c 0 = 1 ∧ (∀ i ≤ Module.finrank (pullField y L) Ω, (c i).IsHomogeneous (i * m)) ∧
    (LinearMap.charpoly (Algebra.lmul (pullField y L) Ω s)).map (algebraMap (pullField y L) Ω) =
      ∑ i ∈ Finset.range (Module.finrank (pullField y L) Ω + 1),
        Polynomial.C (aeval (fun j => aeval y (L j)) (c i)) *
          Polynomial.X ^ (Module.finrank (pullField y L) Ω - i)

end Defs

def FibreNormCharpoly.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (e : K → ℕ) (L : Fin (D + 1) → MRing ι) (q : ℕ),
    IsArithVar (mCoordIdeal y) (D + 1) → Birational y →
    (∀ k, 1 ≤ e k) → (∀ j, IsMultiHomog (L j) e) →
    (∀ z ∈ mcPts (mCoordIdeal y), ∃ j, eval z (map (Int.castRingHom ℂ) (L j)) ≠ 0) →
    FiniteDimensional (pullField y L) Ω ∧
      ∀ τ : ℕ, ∀ s ∈ chartLatNm y (fun k => ((q * e k : ℕ) : ℤ)) τ,
        ∃ c : ℕ → MvPolynomial (Fin (D + 1)) ℚ, IsNormForms y L (q * τ) s c ∧
          (s ≠ 0 → c (Module.finrank (pullField y L) Ω) ≠ 0)

section Inhabitants

open ProjLine

instance charZero_fnField : CharZero FnField :=
  ⟨fun a b h => by
    have h' := congrArg (fun x : FnField => (x : Kfr)) h
    simp only [SubringClass.coe_natCast] at h'
    exact_mod_cast h'⟩

theorem FibreNormCharpoly.hyps_inhabited :
    CharZero FnField ∧
    (IsArithVar (mCoordIdeal (ι := GlobalTheory (Fin 2)) y) (1 + 1) ∧ Birational (ι := GlobalTheory (Fin 2)) y) ∧
    (∀ k : Unit, 1 ≤ (fun _ : Unit => 1) k) ∧
      (∀ j : Fin 2, IsMultiHomog (X ⟨(), j⟩ : MRing (GlobalTheory (Fin 2))) (fun _ => 1)) ∧
      ∀ z ∈ mcPts (mCoordIdeal (ι := GlobalTheory (Fin 2)) y), ∃ j : Fin 2,
        eval z (map (Int.castRingHom ℂ) (X ⟨(), j⟩ : MRing (GlobalTheory (Fin 2)))) ≠ 0 :=
  ⟨inferInstance, FibreNormPullback.hyps_inhabited⟩

end Inhabitants

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
