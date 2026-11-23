import Mathlib
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems

noncomputable section

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ProjSpace

namespace GlobalTheory.ProjBlowup

variable {R : Type} [CommRing R] {X W T : Scheme.{0}} {L : LB X} {m : ℕ}

def Generates (J : X.IdealSheafData) (σ : Fin (m + 1) → L.Sec) : Prop :=
  (⨆ k, L.U k = ⊤) ∧ ∀ (k : L.ι) (V : X.affineOpens) (h : V.1 ≤ L.U k),
    J.ideal V = Ideal.span (Set.range fun j => resG X h ((σ j).f k))

def Proportional (σ : Fin (m + 1) → L.Sec) (g : W ⟶ X) (ψ : W ⟶ PSpace R m) : Prop :=
  ∀ (A : W.Opens) (k : L.ι) (hk : A ≤ g ⁻¹ᵁ L.U k) (i : Fin (m + 1)) (hi : A ≤ ψ ⁻¹ᵁ chart R m i) (j : Fin (m + 1)),
    (g.appLE (L.U k) A hk).hom ((σ j).f k) = pullRatio ψ A i hi j * (g.appLE (L.U k) A hk).hom ((σ i).f k)

theorem Proportional.comp {σ : Fin (m + 1) → L.Sec} {g : W ⟶ X} {ψ : W ⟶ PSpace R m} (h : Proportional σ g ψ)
    (d : T ⟶ W) : Proportional σ (d ≫ g) (d ≫ ψ) := by
  intro A k hk i hi j
  have hA : A ≤ d ⁻¹ᵁ (g ⁻¹ᵁ L.U k ⊓ ψ ⁻¹ᵁ chart R m i) := fun x hx => ⟨hk hx, hi hx⟩
  have := congrArg (d.appLE _ A hA).hom (h _ k inf_le_left i inf_le_right j)
  rwa [map_mul, appLE_appLE, appLE_appLE, appLE_pullRatio] at this

theorem Proportional.of_comp {σ : Fin (m + 1) → L.Sec} {g : W ⟶ X} {ψ : W ⟶ PSpace R m} (d : T ⟶ W)
    [IsSchemeTheoreticallyDominant d] [QuasiCompact d] (h : Proportional σ (d ≫ g) (d ≫ ψ)) :
    Proportional σ g ψ := by
  intro A k hk i hi j
  apply d.app_injective A
  rw [Scheme.Hom.app_eq_appLE, map_mul, appLE_appLE, appLE_appLE, appLE_pullRatio]
  exact h _ k _ i _ j

end GlobalTheory.ProjBlowup
