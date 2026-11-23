import Development.EtaleCohomology.KummerTheory.FinalTheorems

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.KummerTheory.LHCut

def AffNbhd : Prop := ∀ {R : CommRingCat.{0}} (U : Over (Spec R)) (u : U.left),
  ∃ (B : CommRingCat.{0}) (s : R ⟶ B) (ι : Spec B ⟶ U.left) (_ : IsOpenImmersion ι) (b : Spec B),
    ι ≫ U.hom = Spec.map s ∧ ι b = u

def CokAff : Prop := A2 → DivisorNaturality → B1 → ∀ (q : ℕ) [NeZero q] {X : Scheme.{0}} {R : CommRingCat.{0}} (p : X ⟶ Spec R)
  [QuasiCompact p] [IsSeparated p], IsUnit (q : R) →
  ∀ (i : ℤ) (r : ℕ → ℕ) (c : ∀ a : ℕ, Fin (r a) → Ht q (sch.obj X) a i) (M N : ℕ) (n : ℤ),
  (∀ (A : CommRingCat.{0}) (s : R ⟶ A), SH A → IsoUpTo N (lh q p (Spec.map s) i r c M n)) →
  ∀ (B : CommRingCat.{0}) (s : R ⟶ B) (b : Spec B) (x : Ht q (sch.obj (pullback p (Spec.map s))) n i),
  ∃ (C : CommRingCat.{0}) (t : B ⟶ C), t.hom.Etale ∧ (∃ w : Spec C, Spec.map t w = b) ∧
    ∃ y, lh q p (Spec.map (s ≫ t)) i r c M n y = N • pull _ (sch.map (bcMap p s (s ≫ t) t rfl)) _ _ x

theorem affNbhd : AffNbhd := by
  intro R U u
  obtain ⟨b, hb⟩ := U.left.affineCover.covers u
  exact ⟨_, Spec.preimage (U.left.affineCover.f (U.left.affineCover.idx u) ≫ U.hom),
    U.left.affineCover.f (U.left.affineCover.idx u), U.left.affineCover.map_prop _, b, by simp, hb⟩

theorem locCok_of (hA : AffNbhd) (hC : CokAff) : LocCok := by
  intro h2 h6 hb1 q _ X R p _ _ hq i r c M N n hiso U u x
  obtain ⟨B, s, ι, _, b, hs, hb'⟩ := hA U u
  let g0 : Over.mk (Spec.map s) ⟶ U := Over.homMk ι hs
  obtain ⟨C, t, ht, ⟨w, hw⟩, y, hy⟩ := hC h2 h6 hb1 q p hq i r c M N n hiso B s b
    (pull _ (sch.map (rst p g0)) _ _ x)
  have : Etale (Spec.map t) := (HasRingHomProperty.Spec_iff (P := @Etale)).2 ht
  let g : Over.mk (Spec.map (s ≫ t)) ⟶ U := Over.homMk (Spec.map t ≫ ι) (by simp [hs, Spec.map_comp])
  refine ⟨Over.mk (Spec.map (s ≫ t)), g, ⟨?_, w, ?_⟩, y, ?_⟩
  · show Etale (Spec.map t ≫ ι); infer_instance
  · show (Spec.map t ≫ ι) w = u
    rw [Scheme.Hom.comp_apply, hw, hb']
  · show lh q p (Spec.map (s ≫ t)) i r c M n y = _
    have key : bcMap p s (s ≫ t) t rfl ≫ rst p g0 = rst p g := by
      apply pullback.hom_ext
      · simp only [bcMap, rst, g, g0, pullback.map, Over.homMk_left, Category.assoc, Category.comp_id]
        erw [pullback.lift_fst, pullback.lift_fst, pullback.lift_fst]
        rfl
      · simp only [bcMap, rst, g, g0, pullback.map, Over.homMk_left, Category.assoc, Category.comp_id]
        erw [pullback.lift_snd, pullback.lift_snd_assoc, pullback.lift_snd]
        simp only [Category.assoc]
        rfl
    rw [hy, ← pull_comp, ← Functor.map_comp, key]

theorem locCok_of_cokAff (hC : CokAff) : LocCok := locCok_of affNbhd hC

end LateralTheory.KummerTheory.LHCut
