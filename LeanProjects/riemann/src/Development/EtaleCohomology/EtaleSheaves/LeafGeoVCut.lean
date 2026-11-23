import Development.EtaleCohomology.EtaleSheaves.LeafGeoCut

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4

namespace LateralTheory.E.LeafGeoVCut

def FamilyVe {k Ω : Type} [Field k] [Field Ω] (X : Scheme.{0}) {C0 C1 C2 : Scheme.{0}} (c0 : C0 ⟶ Sp Ω) (e : C0 ⟶ X)
    (γ1 : C1 ⟶ C0) (γ2 : C2 ⟶ C1) : Prop :=
  ∃ (B Y0 Y1 Y2 : Scheme.{0}) (b : B ⟶ Sp k) (V : B.Opens) (p : Y0 ⟶ B) (g1 : Y1 ⟶ Y0) (g2 : Y2 ⟶ Y1)
    (h : Y0 ⟶ X) (s : Sp Ω ⟶ B) (u0 : C0 ⟶ Y0) (u1 : C1 ⟶ Y1) (u2 : C2 ⟶ Y2),
    IsIntegral B ∧ IsProper b ∧ Set.range s ⊆ V ∧
    SmP p V ∧ SmP (g1 ≫ p) V ∧ SmP (g2 ≫ g1 ≫ p) V ∧ IsProper (g2 ≫ g1 ≫ h) ∧
    topologicalKrullDim B < topologicalKrullDim X ∧
    IrreducibleSpace Y0 ∧ topologicalKrullDim Y0 ≤ topologicalKrullDim X ∧ topologicalKrullDim Y0 < ⊤ ∧
    (p ⁻¹' (V : Set B)).Nonempty ∧
    IsPullback u0 c0 p s ∧ IsPullback u1 (γ1 ≫ c0) (g1 ≫ p) s ∧ IsPullback u2 (γ2 ≫ γ1 ≫ c0) (g2 ≫ g1 ≫ p) s ∧
    γ1 ≫ u0 = u1 ≫ g1 ∧ γ2 ≫ u1 = u2 ≫ g2 ∧ u0 ≫ h = e

def LeafCurveV : Prop := ∀ (k : Type) [Field k] [IsAlgClosed k] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ Sp k) [IsProper p],
  0 < topologicalKrullDim X → ∃ (Ω : Type) (_ : Field Ω) (_ : IsAlgClosed Ω) (_ : Algebra k Ω) (C0 : Scheme.{0})
    (c0 : C0 ⟶ Sp Ω) (e : C0 ⟶ X), IsCurve c0 ∧ e ≫ p = c0 ≫ Spec.map (CommRingCat.ofHom (algebraMap k Ω)) ∧
    genericPoint X ∈ Set.range e ∧ ∀ R : Subalgebra k Ω, R.FG → ringKrullDim R < topologicalKrullDim X

def LeafSpreadV : Prop := ∀ (k : Type) [Field k] [IsAlgClosed k] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ Sp k)
  [IsProper p] (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra k Ω], (∀ R : Subalgebra k Ω, R.FG → ringKrullDim R <
    topologicalKrullDim X) → ∀ {C0 : Scheme.{0}} (c0 : C0 ⟶ Sp Ω) (e : C0 ⟶ X), IsCurve c0 →
    e ≫ p = c0 ≫ Spec.map (CommRingCat.ofHom (algebraMap k Ω)) →
    ∀ (C1 C2 : Scheme.{0}) (γ1 : C1 ⟶ C0) (γ2 : C2 ⟶ C1), IsCurve (γ1 ≫ c0) → IsCurve (γ2 ≫ γ1 ≫ c0) →
      Surjective γ1 → Surjective γ2 → FamilyVe (k := k) X c0 e γ1 γ2

theorem surj_of_generic {Y X : Scheme.{0}} [IrreducibleSpace X] (f : Y ⟶ X) [IsProper f]
    (hη : genericPoint X ∈ Set.range f) : Surjective f := by
  have hc : IsClosed (Set.range f) := f.isClosedMap.isClosed_range
  have h1 : closure ({genericPoint X} : Set X) ⊆ Set.range f :=
    closure_minimal (Set.singleton_subset_iff.mpr hη) hc
  rw [(genericPoint_spec X).def] at h1
  exact ⟨fun x => h1 (Set.mem_univ x)⟩

theorem goal_of (hC : LeafCurveV) (hS : LeafSpreadV) : LateralTheory.E.LeafGeoCut.LeafGeoV := by
  intro k _ _ X _ p _ hd
  obtain ⟨Ω, iF, iA, iK, C0, c0, e, hc0, he, hη, hdim⟩ := hC k p hd
  refine ⟨Ω, iF, iA, iK, C0, c0, hc0, fun C1 C2 γ1 γ2 h1 h2 s1 s2 => ?_⟩
  obtain ⟨B, Y0, Y1, Y2, b, V, π, g1, g2, h, s, u0, u1, u2, iB, pb, hs, m0, m1, m2, f1, dB, irr, dY, fin, ne,
    P0, P1, P2, w1, w2, ue⟩ := hS k p Ω hdim c0 e hc0 he C1 C2 γ1 γ2 h1 h2 s1 s2
  refine ⟨B, Y0, Y1, Y2, b, V, π, g1, g2, h, s, u0, u1, u2, iB, pb, hs, m0, m1, m2, f1, ?_, dB, irr, dY, fin, ne,
    P0, P1, P2, w1, w2⟩
  obtain ⟨x0, hx0⟩ := hη
  obtain ⟨x1, rfl⟩ := s1.surj x0
  obtain ⟨x2, rfl⟩ := s2.surj x1
  have key : u2 ≫ g2 ≫ g1 ≫ h = γ2 ≫ γ1 ≫ e := by
    rw [← ue, ← Category.assoc u2 g2, ← w2, Category.assoc, ← Category.assoc u1 g1, ← w1]
    simp only [Category.assoc]
  have := f1
  refine surj_of_generic (g2 ≫ g1 ≫ h) ⟨u2 x2, ?_⟩
  rw [← Scheme.Hom.comp_apply, key, ← hx0]
  simp only [Scheme.Hom.comp_apply]

end LateralTheory.E.LeafGeoVCut

end
