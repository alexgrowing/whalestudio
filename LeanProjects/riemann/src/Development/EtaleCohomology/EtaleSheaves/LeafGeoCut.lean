import Development.EtaleCohomology.EtaleSheaves.H0TwistOverClosedField

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4

namespace LateralTheory.E.LeafGeoCut

def FamilyV {k Ω : Type} [Field k] [Field Ω] (X : Scheme.{0}) {C0 C1 C2 : Scheme.{0}} (c0 : C0 ⟶ Sp Ω) (γ1 : C1 ⟶ C0)
    (γ2 : C2 ⟶ C1) : Prop :=
  ∃ (B Y0 Y1 Y2 : Scheme.{0}) (b : B ⟶ Sp k) (V : B.Opens) (p : Y0 ⟶ B) (g1 : Y1 ⟶ Y0) (g2 : Y2 ⟶ Y1)
    (h : Y0 ⟶ X) (s : Sp Ω ⟶ B) (u0 : C0 ⟶ Y0) (u1 : C1 ⟶ Y1) (u2 : C2 ⟶ Y2),
    IsIntegral B ∧ IsProper b ∧ Set.range s ⊆ V ∧
    SmP p V ∧ SmP (g1 ≫ p) V ∧ SmP (g2 ≫ g1 ≫ p) V ∧ IsProper (g2 ≫ g1 ≫ h) ∧ Surjective (g2 ≫ g1 ≫ h) ∧
    topologicalKrullDim B < topologicalKrullDim X ∧
    IrreducibleSpace Y0 ∧ topologicalKrullDim Y0 ≤ topologicalKrullDim X ∧ topologicalKrullDim Y0 < ⊤ ∧
    (p ⁻¹' (V : Set B)).Nonempty ∧
    IsPullback u0 c0 p s ∧ IsPullback u1 (γ1 ≫ c0) (g1 ≫ p) s ∧ IsPullback u2 (γ2 ≫ γ1 ≫ c0) (g2 ≫ g1 ≫ p) s ∧
    γ1 ≫ u0 = u1 ≫ g1 ∧ γ2 ≫ u1 = u2 ≫ g2

def LeafGeoV : Prop := ∀ (k : Type) [Field k] [IsAlgClosed k] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ Sp k) [IsProper p],
  0 < topologicalKrullDim X → ∃ (Ω : Type) (_ : Field Ω) (_ : IsAlgClosed Ω) (_ : Algebra k Ω) (C0 : Scheme.{0})
    (c0 : C0 ⟶ Sp Ω), IsCurve c0 ∧ ∀ (C1 C2 : Scheme.{0}) (γ1 : C1 ⟶ C0) (γ2 : C2 ⟶ C1), IsCurve (γ1 ≫ c0) →
      IsCurve (γ2 ≫ γ1 ≫ c0) → Surjective γ1 → Surjective γ2 → FamilyV (k := k) X c0 γ1 γ2

def LeafClosed : Prop := ∀ (B : Scheme.{0}) (V : B.Opens),
  ∃ (W : Scheme.{0}) (ι : W ⟶ B), IsClosedImmersion ι ∧ (V : Set B) = (Set.range ι)ᶜ

def LeafBdry : Prop := ∀ {Y B W : Scheme.{0}} (p : Y ⟶ B) (ι : W ⟶ B), IsClosedImmersion ι → IrreducibleSpace Y →
  topologicalKrullDim Y < ⊤ → (p ⁻¹' (Set.range ι)ᶜ).Nonempty →
  topologicalKrullDim (pullback p ι : Scheme.{0}) < topologicalKrullDim Y

theorem goal_of (hV : LeafGeoV) (hC : LeafClosed) (hB : LeafBdry) : LateralTheory.E.E4.LeafGeo := by
  intro k _ _ X _ p _ hd
  obtain ⟨Ω, iF, iA, iK, C0, c0, hc0, hall⟩ := hV k p hd
  refine ⟨Ω, iF, iA, iK, C0, c0, hc0, fun C1 C2 γ1 γ2 h1 h2 s1 s2 => ?_⟩
  obtain ⟨B, Y0, Y1, Y2, b, V, π, g1, g2, h, s, u0, u1, u2, iB, pb, hs, m0, m1, m2, f1, f2, dB, irr, dY, fin, ne,
    P0, P1, P2, w1, w2⟩ := hall C1 C2 γ1 γ2 h1 h2 s1 s2
  obtain ⟨W, ι, hι, hWV⟩ := hC B V
  exact ⟨B, W, Y0, Y1, Y2, b, ι, V, π, g1, g2, h, s, u0, u1, u2, iB, pb, hι, hWV, hs, m0, m1, m2, f1, f2, dB,
    lt_of_lt_of_le (hB π ι hι irr fin (hWV ▸ ne)) dY, P0, P1, P2, w1, w2⟩

end LateralTheory.E.LeafGeoCut

end
