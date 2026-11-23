import Development.EtaleCohomology.EtaleSheaves.LeafGeoVCut

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4

namespace LateralTheory.E.LeafSpreadVCut

def LeafDescendV : Prop := ∀ (k : Type) [Field k] {X : Scheme.{0}} (p : X ⟶ Sp k) [IsProper p] (Ω : Type) [Field Ω]
    [Algebra k Ω] {C0 : Scheme.{0}} (c0 : C0 ⟶ Sp Ω) (e : C0 ⟶ X), IsCurve c0 →
    e ≫ p = c0 ≫ Spec.map (CommRingCat.ofHom (algebraMap k Ω)) →
    ∀ (C1 C2 : Scheme.{0}) (γ1 : C1 ⟶ C0) (γ2 : C2 ⟶ C1), IsCurve (γ1 ≫ c0) → IsCurve (γ2 ≫ γ1 ≫ c0) →
    ∃ (R : Subalgebra k Ω), R.FG ∧ ∃ (D0 D1 D2 : Scheme.{0}) (q : D0 ⟶ Sp R) (d1 : D1 ⟶ D0) (d2 : D2 ⟶ D1)
      (f : D0 ⟶ X) (v0 : C0 ⟶ D0) (v1 : C1 ⟶ D1) (v2 : C2 ⟶ D2),
      IsProper q ∧ SmoothOfRelativeDimension 1 q ∧ IsProper (d1 ≫ q) ∧ SmoothOfRelativeDimension 1 (d1 ≫ q) ∧
      IsProper (d2 ≫ d1 ≫ q) ∧ SmoothOfRelativeDimension 1 (d2 ≫ d1 ≫ q) ∧
      f ≫ p = q ≫ Spec.map (CommRingCat.ofHom (algebraMap k R)) ∧
      IrreducibleSpace D0 ∧ topologicalKrullDim D0 ≤ ringKrullDim R + 1 ∧
      IsPullback v0 c0 q (Spec.map (CommRingCat.ofHom (algebraMap R Ω))) ∧
      IsPullback v1 (γ1 ≫ c0) (d1 ≫ q) (Spec.map (CommRingCat.ofHom (algebraMap R Ω))) ∧
      IsPullback v2 (γ2 ≫ γ1 ≫ c0) (d2 ≫ d1 ≫ q) (Spec.map (CommRingCat.ofHom (algebraMap R Ω))) ∧
      γ1 ≫ v0 = v1 ≫ d1 ∧ γ2 ≫ v1 = v2 ≫ d2 ∧ v0 ≫ f = e

def LeafCloseB : Prop := ∀ (k : Type) [Field k] (A : Type) [CommRing A] [IsDomain A] [Algebra k A]
    [Algebra.FiniteType k A], ∃ (B : Scheme.{0}) (b : B ⟶ Sp k) (ι : Sp A ⟶ B), IsIntegral B ∧ IsProper b ∧
    IsOpenImmersion ι ∧ ι ≫ b = Spec.map (CommRingCat.ofHom (algebraMap k A)) ∧ topologicalKrullDim B ≤ ringKrullDim A

def LeafExtendY : Prop := ∀ (k : Type) [Field k] {X : Scheme.{0}} (p : X ⟶ Sp k) [IsProper p] (A : Type) [CommRing A]
    [Algebra k A] (B : Scheme.{0}) (b : B ⟶ Sp k) [IsProper b] (ι : Sp A ⟶ B) [IsOpenImmersion ι],
    ι ≫ b = Spec.map (CommRingCat.ofHom (algebraMap k A)) →
    ∀ (D0 D1 D2 : Scheme.{0}) (q : D0 ⟶ Sp A) (d1 : D1 ⟶ D0) (d2 : D2 ⟶ D1) (f : D0 ⟶ X),
    IsProper q → SmoothOfRelativeDimension 1 q → IsProper (d1 ≫ q) → SmoothOfRelativeDimension 1 (d1 ≫ q) →
    IsProper (d2 ≫ d1 ≫ q) → SmoothOfRelativeDimension 1 (d2 ≫ d1 ≫ q) →
    f ≫ p = q ≫ Spec.map (CommRingCat.ofHom (algebraMap k A)) → IrreducibleSpace D0 →
    ∃ (Y0 Y1 Y2 : Scheme.{0}) (π : Y0 ⟶ B) (g1 : Y1 ⟶ Y0) (g2 : Y2 ⟶ Y1) (h : Y0 ⟶ X)
      (w0 : D0 ⟶ Y0) (w1 : D1 ⟶ Y1) (w2 : D2 ⟶ Y2),
      SmP π ι.opensRange ∧ SmP (g1 ≫ π) ι.opensRange ∧ SmP (g2 ≫ g1 ≫ π) ι.opensRange ∧ IsProper (g2 ≫ g1 ≫ h) ∧
      IrreducibleSpace Y0 ∧ topologicalKrullDim Y0 ≤ topologicalKrullDim D0 ∧
      IsPullback w0 q π ι ∧ IsPullback w1 (d1 ≫ q) (g1 ≫ π) ι ∧ IsPullback w2 (d2 ≫ d1 ≫ q) (g2 ≫ g1 ≫ π) ι ∧
      d1 ≫ w0 = w1 ≫ g1 ∧ d2 ≫ w1 = w2 ≫ g2 ∧ w0 ≫ h = f

lemma succ_le_of_lt {a x : WithBot ℕ∞} (h : a < x) : a + 1 ≤ x ∧ a + 1 < ⊤ := by
  induction a with
  | bot => exact ⟨by simp, by simp⟩
  | coe n =>
    induction x with
    | bot => exact absurd h (not_lt_bot)
    | coe m =>
      have h' : n < m := WithBot.coe_lt_coe.mp h
      have hn : n ≠ ⊤ := ne_top_of_lt h'
      refine ⟨?_, ?_⟩
      · rw [← WithBot.coe_one, ← WithBot.coe_add, WithBot.coe_le_coe]
        exact Order.add_one_le_of_lt h'
      · rw [← WithBot.coe_one, ← WithBot.coe_add]
        exact WithBot.coe_lt_coe.mpr (lt_top_iff_ne_top.mpr (by
          lift n to ℕ using hn
          exact ENat.natCast_ne_top (n + 1)))

theorem goal_of (hD : LeafDescendV) (hB : LeafCloseB) (hE : LeafExtendY) : LateralTheory.E.LeafGeoVCut.LeafSpreadV := by
  intro k _ _ X _ p _ Ω _ _ _ hdim C0 c0 e hc0 he C1 C2 γ1 γ2 h1 h2 _ _
  obtain ⟨R, hR, D0, D1, D2, q, d1, d2, f, v0, v1, v2, pq, sq, pq1, sq1, pq2, sq2, hf, irr, dD, P0, P1, P2,
    c1, c2, ve⟩ := hD k p Ω c0 e hc0 he C1 C2 γ1 γ2 h1 h2
  have : Algebra.FiniteType k R := Subalgebra.fg_iff_finiteType R |>.mp hR
  obtain ⟨B, b, ι, iB, pb, oι, hι, dB⟩ := hB k R
  obtain ⟨Y0, Y1, Y2, π, g1, g2, h, w0, w1, w2, m0, m1, m2, f1, irrY, dY, Q0, Q1, Q2, e1, e2, we⟩ :=
    hE k p R B b ι hι D0 D1 D2 q d1 d2 f pq sq pq1 sq1 pq2 sq2 hf irr
  have hR' : ringKrullDim R < topologicalKrullDim X := hdim R hR
  obtain ⟨hle, hlt⟩ := succ_le_of_lt hR'
  have := hc0.1
  obtain ⟨x⟩ : Nonempty C0 := inferInstance
  refine ⟨B, Y0, Y1, Y2, b, ι.opensRange, π, g1, g2, h, Spec.map (CommRingCat.ofHom (algebraMap R Ω)) ≫ ι,
    v0 ≫ w0, v1 ≫ w1, v2 ≫ w2, iB, pb, ?_, m0, m1, m2, f1, lt_of_le_of_lt dB hR', irrY, dY.trans (dD.trans hle),
    lt_of_le_of_lt (dY.trans dD) hlt, ⟨(v0 ≫ w0) x, ?_⟩, P0.paste_horiz Q0, P1.paste_horiz Q1, P2.paste_horiz Q2, ?_, ?_,
    by rw [Category.assoc, we, ve]⟩
  · rintro _ ⟨y, rfl⟩
    exact ⟨_, rfl⟩
  · show π ((v0 ≫ w0) x) ∈ Set.range ι
    rw [← Scheme.Hom.comp_apply, Category.assoc, Q0.w, ← Category.assoc, P0.w]
    exact ⟨_, rfl⟩
  · rw [← Category.assoc, c1, Category.assoc, Category.assoc, e1]
  · rw [← Category.assoc, c2, Category.assoc, Category.assoc, e2]

end LateralTheory.E.LeafSpreadVCut

end
