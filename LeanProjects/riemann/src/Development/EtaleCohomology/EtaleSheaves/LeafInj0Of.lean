import Development.EtaleCohomology.EtaleSheaves.LeafDegCut

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.LeafInj0Pf
open LateralTheory.E.E4 LateralTheory.E.LeafGhostCut LateralTheory.E.EtaleTopologySheaves LateralTheory.E.LeafDegCut

theorem cov_of_pts {B : Scheme.{0}} {U : B.Etale} {P : ∀ U' : B.Etale, (U' ⟶ U) → Prop}
    (h : ∀ x : U.left, ∃ (U' : B.Etale) (a : U' ⟶ U) (y : U'.left), a.left y = x ∧
      Cov U' (fun U'' b => P U'' (b ≫ a))) : Cov U P := by
  choose U' a y hy hC using h
  choose T hT hP using hC
  let R : Sieve U :=
    { arrows := fun {Z} g => ∃ x, ∃ b : Z ⟶ U' x, T x b ∧ g = b ≫ a x
      downward_closed := by
        rintro Z W g ⟨x, b, hb, rfl⟩ h
        exact ⟨x, h ≫ b, (T x).downward_closed hb h, by simp⟩ }
  refine ⟨R, ?_, ?_⟩
  · have h0 : Sieve.ofArrows U' a ∈ (EtTop B) U := by
      rw [Scheme.ofArrows_mem_smallEtaleTopology_iff]
      ext z
      simp only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
      exact ⟨z, y z, hy z⟩
    refine (EtTop B).transitive h0 R ?_
    intro Z f hf
    obtain ⟨W, g, f', hf', rfl⟩ := hf
    cases hf' with
    | mk x =>
      refine (EtTop B).superset_covering ?_ ((EtTop B).pullback_stable g (hT x))
      intro V c hc
      exact ⟨x, c ≫ g, hc, by simp⟩
  · rintro Z g ⟨x, b, hb, rfl⟩
    exact hP x Z b hb

def LeafInj0W : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k], IsUnit (q : k) → ∀ (i : ℤ)
  {B W Y0 Y1 Y2 : Scheme.{0}} (_ : B ⟶ Sp k) (ι : W ⟶ B) [IsClosedImmersion ι] (V : B.Opens), (V : Set B) = (Set.range ι)ᶜ →
  ∀ (p : Y0 ⟶ B) (g1 : Y1 ⟶ Y0) (g2 : Y2 ⟶ Y1), IsProper p → IsProper (g1 ≫ p) → IsProper (g2 ≫ g1 ≫ p) →
  SHV q i V p g1 g2 → ∀ (U : B.Etale), ∀ c : Hrel (ZMod q) (sch.map (prB ι U)) (tw q i) 0,
  ∀ x : U.left, U.hom x ∈ Set.range ι →
  ∃ (U' : B.Etale) (a : U' ⟶ U) (y : U'.left), a.left y = x ∧ Cov U' (fun U'' b => rB q i ι (b ≫ a) 0 c = 0)

def LeafInj0V : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k], IsUnit (q : k) → ∀ (i : ℤ)
  {B W Y0 Y1 Y2 : Scheme.{0}} (_ : B ⟶ Sp k) (ι : W ⟶ B) [IsClosedImmersion ι] (V : B.Opens), (V : Set B) = (Set.range ι)ᶜ →
  ∀ (p : Y0 ⟶ B) (g1 : Y1 ⟶ Y0) (g2 : Y2 ⟶ Y1), IsProper p → IsProper (g1 ≫ p) → IsProper (g2 ≫ g1 ≫ p) →
  SHV q i V p g1 g2 → ∀ (U : B.Etale), ∀ c : Hrel (ZMod q) (sch.map (prB ι U)) (tw q i) 0,
  Cov U (fun U' a => rY q i (g2 ≫ g1 ≫ p) ι a 0 (bY q i (g2 ≫ g1 ≫ p) ι U 0 c) = 0) →
  ∀ x : U.left, U.hom x ∉ Set.range ι →
  ∃ (U' : B.Etale) (a : U' ⟶ U) (y : U'.left), a.left y = x ∧ Cov U' (fun U'' b => rB q i ι (b ≫ a) 0 c = 0)

theorem LeafInj0_of (hW : LeafInj0W) (hV : LeafInj0V) : LateralTheory.E.LeafDegCut.LeafInj0 := by
  intro hH q _ k _ hq i B W Y0 Y1 Y2 s ι _ V hV' p g1 g2 hp1 hp2 hp3 hS U c hc
  apply cov_of_pts
  intro x
  by_cases hx : U.hom x ∈ Set.range ι
  · exact hW hH q k hq i s ι V hV' p g1 g2 hp1 hp2 hp3 hS U c x hx
  · exact hV hH q k hq i s ι V hV' p g1 g2 hp1 hp2 hp3 hS U c hc x hx
end LateralTheory.E.LeafInj0Pf
