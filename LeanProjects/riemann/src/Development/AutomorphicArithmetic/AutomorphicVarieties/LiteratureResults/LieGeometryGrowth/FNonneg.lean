import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PairFactsAlt

noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor

namespace UpperTheory.V.Lit.Geo

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

def BddDer (φ : Sm E a) : Prop :=
  ∀ (X : Lie E a) (l : List (Lie E a)), ∃ C : ℝ, ∀ g, ‖(((X :: l).map (lie E a)).prod φ).1 g‖ ≤ C

structure IsStep (U : Subgroup (GL (Fin a) (Af E))) (f : GA E a → ℝ) (Y : GA E a → Herm E a) (C c f₀ : ℝ) : Prop where
  c_pos : 0 < c
  f_sm : ∃ φ : Sm E a, (∀ g, φ.1 g = f g) ∧ BddDer φ
  f_left : ∀ γ t g, f (ratGL E a γ * splitCentre E a t * g) = f g
  f_cpt : ∀ (k : Kinf E a) g, f (g * infGL E a (Unitary.toUnits k)) = f g
  f_lev : ∀ u ∈ U, ∀ g, f (g * finGL E a u) = f g
  f_nonneg : ∀ g, 0 ≤ f g
  f_le : ∀ g, f g ≤ C * (1 + Real.log (qht g))
  le_f : ∀ g, Real.log (qht g) ≤ C * (1 + f g)
  Y_sm : ∀ i j w, ∃ φ : Sm E a, (∀ g, φ.1 g = (Y g).1 i j w) ∧ BddDer φ
  Y_left : ∀ γ t g, Y (ratGL E a γ * splitCentre E a t * g) = Y g
  Y_cpt : ∀ (k : Kinf E a) g, adHerm k (Y (g * infGL E a (Unitary.toUnits k))) = Y g
  Y_lev : ∀ u ∈ U, ∀ g, Y (g * finGL E a u) = Y g
  root : ∀ g (t : ℝ), |t| ≤ 1 → ∃ h : GL (Fin a) (Cinf E), h.val * star h.val = 1 + t • (Y g).1 ∧
    ‖toL h.val‖ ≤ C ∧ ‖toL (h⁻¹).val‖ ≤ C
  up : ∀ g (h : GL (Fin a) (Cinf E)), f₀ ≤ f g → h.val * star h.val = 1 + (Y g).1 → f g + c ≤ f (g * infGL E a h)
  down : ∀ g (h : GL (Fin a) (Cinf E)), f₀ ≤ f g → h.val * star h.val = 1 - (Y g).1 → f (g * infGL E a h) ≤ f g - c
  near : ∀ g (t : ℝ) (h : GL (Fin a) (Cinf E)), |t| ≤ 1 → h.val * star h.val = 1 + t • (Y g).1 →
    |f (g * infGL E a h) - f g| ≤ C

def StepEx : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), 1 ≤ a → ∀ U : Subgroup (GL (Fin a) (Af E)),
    IsCompact (U : Set (GL (Fin a) (Af E))) → ∃ f Y C c f₀, IsStep U f Y C c f₀

end UpperTheory.V.Lit.Geo
