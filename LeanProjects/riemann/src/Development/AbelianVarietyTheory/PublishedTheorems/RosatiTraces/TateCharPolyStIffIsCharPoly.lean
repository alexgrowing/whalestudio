import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RosatiNormLEOfStarNormLE

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Published

def TateCharPolySt : Prop := EndCharPolySt

theorem tateCharPolySt_iff : TateCharPolySt ↔ EndCharPolySt := Iff.rfl

end GlobalTheory.Published

namespace GlobalTheory.TateCharPoly

open ThetaDetCompare ThetaCoord

variable {K : Type} [Field K] {P : PolAV (Sp K)}

def IsCharPoly (P : PolAV (Sp K)) (ψ : P.A ⟶ P.A) (χ : Polynomial ℤ) : Prop :=
  ∀ l r : ℕ, l.Prime → (l : K) ≠ 0 → ∀ y, Frame P (l ^ r) y →
    ∀ B : Matrix (Fin (2 * P.g)) (Fin (2 * P.g)) (ZMod (l ^ r)), Rep y ψ B →
      B.charpoly = χ.map (Int.castRingHom (ZMod (l ^ r)))

theorem tateCharPolySt_iff_isCharPoly : Published.TateCharPolySt ↔
    ∀ (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Sp K)) (ψ : P.A ⟶ P.A), IsMonHom ψ →
      ∃ χ : Polynomial ℤ, χ.Monic ∧ χ.natDegree = 2 * P.g ∧ IsCharPoly P ψ χ := by
  refine ⟨fun h K _ _ P ψ hψ => ?_, fun h K _ _ P ψ hψ => ?_⟩
  · obtain ⟨χ, hm, hd, hc⟩ := h K P ψ hψ
    exact ⟨χ, hm, hd, fun l r hl hK y hy B hB => hc l r hl hK y hy.1 hy.2 B hB⟩
  · obtain ⟨χ, hm, hd, hc⟩ := h K P ψ hψ
    exact ⟨χ, hm, hd, fun l r hl hK y h₁ h₂ B hB => hc l r hl hK y ⟨h₁, h₂⟩ B hB⟩

variable [IsAlgClosed K]

theorem IsCharPoly.unique (hL : Laws) {ψ : P.A ⟶ P.A} [IsMonHom ψ] {χ χ' : Polynomial ℤ} (h : IsCharPoly P ψ χ)
    (h' : IsCharPoly P ψ χ') : χ = χ' :=
  Polynomial.ext fun n => int_eq_of_frames hL P fun l r hl hK y hy => by
    obtain ⟨B, hB⟩ := hy.exists_rep ψ
    simpa using congrArg (·.coeff n) ((h l r hl hK y hy B hB).symm.trans (h' l r hl hK y hy B hB))

theorem IsCharPoly.eq_of_id (hL : Laws) {χ : Polynomial ℤ} (h : IsCharPoly P (𝟙 _) χ) :
    χ = (Polynomial.X - 1) ^ (2 * P.g) :=
  Polynomial.ext fun n => int_eq_of_frames hL P fun l r hl hK y hy => by
    have : NeZero (l ^ r) := ⟨pow_ne_zero _ hl.ne_zero⟩
    have h₁ := h l r hl hK y hy 1 (repRing (endAct P) hy.1).one_mem
    have h₂ : (1 : Matrix (Fin (2 * P.g)) (Fin (2 * P.g)) (ZMod (l ^ r))).charpoly =
        ((Polynomial.X - 1) ^ (2 * P.g) : Polynomial ℤ).map (Int.castRingHom (ZMod (l ^ r))) := by
      simp [Matrix.charpoly_one]
    simpa only [Polynomial.coeff_map, eq_intCast] using congrArg (·.coeff n) (h₁.symm.trans h₂)

end GlobalTheory.TateCharPoly
