import Mathlib
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.GoodRoot
import Development.EtaleCohomology.EtaleSheaves.StandardChartsLineOne

noncomputable section
open CategoryTheory Limits AlgebraicGeometry IsLocalRing GlobalTheory.EtC UpperTheory.Et LateralTheory.E.t_E2Cut LateralTheory.E.LineOneCut LateralTheory.E.StandardEtaleChartsMultivariableHensel

theorem UpperTheory.exists_fiber_pullback_square_of_open_immersions :
    ∀ (A : Type) [CommRing A] [IsLocalRing A] {Z U V : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of A)) (ι₁ : U ⟶ Z) (ι₂ : V ⟶ Z),
      ∃ (r : pullback (fibMap p ι₁) (fibMap p ι₂) ⟶ pullback ι₁ ι₂) (c : pullback (fibMap p ι₁) (fibMap p ι₂) ⟶ Spec (CommRingCat.of (ResidueField A))),
        IsPullback r c (pullback.fst ι₁ ι₂ ≫ ι₁ ≫ p) (cpt A) ∧
        r ≫ pullback.fst ι₁ ι₂ = pullback.fst (fibMap p ι₁) (fibMap p ι₂) ≫ pullback.fst (ι₁ ≫ p) (cpt A) ∧
        r ≫ pullback.snd ι₁ ι₂ = pullback.snd (fibMap p ι₁) (fibMap p ι₂) ≫ pullback.fst (ι₂ ≫ p) (cpt A) := by
  intro A _ _ Z U V p ι₁ ι₂
  have m1 : ∀ {Y : Scheme.{0}} (ι : Y ⟶ Z), fibMap p ι ≫ pullback.fst p (cpt A) = pullback.fst (ι ≫ p) (cpt A) ≫ ι := by
    intro Y ι
    exact pullback.lift_fst _ _ _
  have m2 : ∀ {Y : Scheme.{0}} (ι : Y ⟶ Z), fibMap p ι ≫ pullback.snd p (cpt A) = pullback.snd (ι ≫ p) (cpt A) := by
    intro Y ι
    exact (pullback.lift_snd _ _ _).trans (Category.comp_id _)
  have m1' : ∀ {Y W : Scheme.{0}} (ι : Y ⟶ Z) (k : Z ⟶ W), fibMap p ι ≫ pullback.fst p (cpt A) ≫ k = pullback.fst (ι ≫ p) (cpt A) ≫ ι ≫ k := by
    intro Y W ι k
    rw [← Category.assoc, m1, Category.assoc]
  have m2' : ∀ {Y W : Scheme.{0}} (ι : Y ⟶ Z) (k : _ ⟶ W), fibMap p ι ≫ pullback.snd p (cpt A) ≫ k = pullback.snd (ι ≫ p) (cpt A) ≫ k := by
    intro Y W ι k
    rw [← Category.assoc, m2]
  have hr1 : (pullback.fst (fibMap p ι₁) (fibMap p ι₂) ≫ pullback.fst (ι₁ ≫ p) (cpt A)) ≫ ι₁ =
      (pullback.snd (fibMap p ι₁) (fibMap p ι₂) ≫ pullback.fst (ι₂ ≫ p) (cpt A)) ≫ ι₂ := by
    rw [Category.assoc, Category.assoc, ← m1, ← m1, ← Category.assoc, pullback.condition, Category.assoc]
  let r := pullback.lift _ _ hr1
  let c := pullback.fst (fibMap p ι₁) (fibMap p ι₂) ≫ pullback.snd (ι₁ ≫ p) (cpt A)
  refine ⟨r, c, ?_, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  have cond : pullback.fst (ι₁ ≫ p) (cpt A) ≫ ι₁ ≫ p = pullback.snd (ι₁ ≫ p) (cpt A) ≫ cpt A := by
    exact pullback.condition
  have w : r ≫ pullback.fst ι₁ ι₂ ≫ ι₁ ≫ p = c ≫ cpt A := by
    simp only [r, c, pullback.lift_fst_assoc, Category.assoc, cond]
  have cond2 : pullback.fst ι₁ ι₂ ≫ ι₁ = pullback.snd ι₁ ι₂ ≫ ι₂ := pullback.condition
  have L : ∀ (s : PullbackCone (pullback.fst ι₁ ι₂ ≫ ι₁ ≫ p) (cpt A)),
      ∃ l : s.pt ⟶ pullback (fibMap p ι₁) (fibMap p ι₂), l ≫ r = s.fst ∧ l ≫ c = s.snd ∧
        ∀ m : s.pt ⟶ pullback (fibMap p ι₁) (fibMap p ι₂), m ≫ r = s.fst → m ≫ c = s.snd → m = l := by
    intro s
    have hs : s.fst ≫ pullback.fst ι₁ ι₂ ≫ ι₁ ≫ p = s.snd ≫ cpt A := s.condition
    have hs1 : (s.fst ≫ pullback.fst ι₁ ι₂) ≫ ι₁ ≫ p = s.snd ≫ cpt A := by
      rw [Category.assoc]
      exact hs
    have hs2 : (s.fst ≫ pullback.snd ι₁ ι₂) ≫ ι₂ ≫ p = s.snd ≫ cpt A := by
      rw [Category.assoc, ← Category.assoc (pullback.snd ι₁ ι₂), ← cond2, Category.assoc]
      exact hs
    let x₁ := pullback.lift _ _ hs1
    let x₂ := pullback.lift _ _ hs2
    have hx : x₁ ≫ fibMap p ι₁ = x₂ ≫ fibMap p ι₂ := by
      apply pullback.hom_ext
      · simp only [x₁, x₂, Category.assoc, m1, pullback.lift_fst_assoc, cond2]
      · simp only [x₁, x₂, Category.assoc, m2, pullback.lift_snd]
    refine ⟨pullback.lift x₁ x₂ hx, ?_, ?_, ?_⟩
    · apply pullback.hom_ext
      · simp only [r, x₁, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]
      · simp only [r, x₂, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc, pullback.lift_fst]
    · simp only [c, x₁, pullback.lift_fst_assoc, pullback.lift_snd]
    · intro m hm1 hm2
      have e1 : m ≫ pullback.fst (fibMap p ι₁) (fibMap p ι₂) ≫ pullback.fst (ι₁ ≫ p) (cpt A) = s.fst ≫ pullback.fst ι₁ ι₂ := by
        rw [← hm1, Category.assoc, pullback.lift_fst]
      have e2 : m ≫ pullback.snd (fibMap p ι₁) (fibMap p ι₂) ≫ pullback.fst (ι₂ ≫ p) (cpt A) = s.fst ≫ pullback.snd ι₁ ι₂ := by
        rw [← hm1, Category.assoc, pullback.lift_snd]
      have e3 : m ≫ pullback.fst (fibMap p ι₁) (fibMap p ι₂) ≫ pullback.snd (ι₁ ≫ p) (cpt A) = s.snd := hm2
      have e4 : m ≫ pullback.snd (fibMap p ι₁) (fibMap p ι₂) ≫ pullback.snd (ι₂ ≫ p) (cpt A) = s.snd := by
        rw [← m2 ι₂, ← pullback.condition_assoc, m2 ι₁]
        exact e3
      apply pullback.hom_ext
      · apply pullback.hom_ext
        · simp only [Category.assoc, pullback.lift_fst, x₁, e1]
        · simp only [Category.assoc, pullback.lift_fst, x₁, e3, pullback.lift_snd]
      · apply pullback.hom_ext
        · simp only [Category.assoc, pullback.lift_snd, x₂, e2, pullback.lift_fst]
        · simp only [Category.assoc, pullback.lift_snd, x₂, e4]
  choose l hl1 hl2 hl3 using L
  exact IsPullback.of_isLimit (c := PullbackCone.mk r c w)
    (PullbackCone.IsLimit.mk w l hl1 hl2 (fun s m h1 h2 => hl3 s m h1 h2))

end
