import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.LowestKTypeMultiplicity

noncomputable section

namespace ReciprocityTheory.ChartRestriction.DS.Lap.DifferentialActionLinearity.CW

open Formalism.QuantumDeterminants Formalism.MainNotions.S

variable {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)}

theorem dsigW_add (hU : IsURepOn (UH (Hpk k r)) σ) {a b : H} (ha : a ∈ smoothVecs (k := k) (r := r) σ)
    (hb : b ∈ smoothVecs (k := k) (r := r) σ) (W : List (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ))
    (hW : ∀ X ∈ W, InLieHpk k r X) :
    dsigW (k := k) (r := r) σ W (a + b) = dsigW (k := k) (r := r) σ W a + dsigW (k := k) (r := r) σ W b := by
  induction W with
  | nil => rfl
  | cons Y w ih =>
    have hw : ∀ X ∈ w, InLieHpk k r X := fun X hX => hW X (List.mem_cons_of_mem _ hX)
    have hY : InLieHpk k r Y := hW Y List.mem_cons_self
    have h1 := Formalism.MainNotions.LowestKTypeMultiplicity.dsigW_hasDeriv hU ha w hw hY
    have h2 := Formalism.MainNotions.LowestKTypeMultiplicity.dsigW_hasDeriv hU hb w hw hY
    show dsig σ Y (dsigW σ w (a + b)) = _
    rw [ih hw]
    unfold dsig
    simp only [map_add]
    exact (h1.add h2).deriv

theorem dsigW_smul (hU : IsURepOn (UH (Hpk k r)) σ) (c : ℂ) {a : H} (ha : a ∈ smoothVecs (k := k) (r := r) σ)
    (W : List (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)) (hW : ∀ X ∈ W, InLieHpk k r X) :
    dsigW (k := k) (r := r) σ W (c • a) = c • dsigW (k := k) (r := r) σ W a := by
  induction W with
  | nil => rfl
  | cons Y w ih =>
    have hw : ∀ X ∈ w, InLieHpk k r X := fun X hX => hW X (List.mem_cons_of_mem _ hX)
    have hY : InLieHpk k r Y := hW Y List.mem_cons_self
    have h1 := Formalism.MainNotions.LowestKTypeMultiplicity.dsigW_hasDeriv hU ha w hw hY
    show dsig σ Y (dsigW σ w (c • a)) = _
    rw [ih hw]
    unfold dsig
    simp only [map_smul]
    exact (h1.const_smul c).deriv

end ReciprocityTheory.ChartRestriction.DS.Lap.DifferentialActionLinearity.CW
