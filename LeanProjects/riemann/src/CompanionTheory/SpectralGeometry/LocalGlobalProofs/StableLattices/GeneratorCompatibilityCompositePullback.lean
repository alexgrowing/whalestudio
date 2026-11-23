import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.LineBundleTrivialOfDescendedGeneratorStatement
import CompanionTheory.AutomorphicTheory.TemperedLocalSpectra.ObstructionLifting.H1StructureDimLe
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual CompanionTheory.ObstructionTrivialLocus
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.RigGlue

theorem gm_gen_pull {Y X : Scheme.{0}} {L : LB X} {F : Y ⟶ X} {t : LB.Gen (L.pull F)} (ht : t.IsGen) (x : Y)
    (i i' : L.ι) (hi : F x ∈ L.U i) (hi' : F x ∈ L.U i') :
    gm (𝟙 Y) x ((L.pull F).U fun _ => i) (t.s fun _ => i) =
      gm (𝟙 Y ≫ F) x _ (L.g i i') * gm (𝟙 Y) x ((L.pull F).U fun _ => i') (t.s fun _ => i') := by
  have m₁ : (𝟙 Y : Y ⟶ Y) x ∈ (L.pull F).U (fun _ => i) := mem_pull.2 hi
  have m₂ : (𝟙 Y : Y ⟶ Y) x ∈ (L.pull F).U (fun _ => i') := mem_pull.2 hi'
  have hm : (𝟙 Y : Y ⟶ Y) x ∈ (L.pull F).U (fun _ => i) ⊓ (L.pull F).U (fun _ => i') := ⟨m₁, m₂⟩
  have e := congrArg (gm (𝟙 Y) x _) (ht (fun _ => i) (fun _ => i'))
  rw [map_mul, gm_res (𝟙 Y) x _ hm, gm_res (𝟙 Y) x _ hm, gm_pull_g L F (𝟙 Y) x _ _ m₁ m₂] at e
  exact e

theorem gm_pull_div_g {Z P Q : Scheme.{0}} (g : Z ⟶ P) (f : P ⟶ Q) (M : LB P) (N : LB Q) (x : Z) (i i' : N.ι) (k k' : M.ι)
    (hi : f (g x) ∈ N.U i) (hi' : f (g x) ∈ N.U i') (hk : g x ∈ M.U k) (hk' : g x ∈ M.U k') :
    gm (𝟙 Z) x (((LB.div (N.pull f) M).pull g).U (fun _ => (fun _ => i, k)) ⊓
        ((LB.div (N.pull f) M).pull g).U (fun _ => (fun _ => i', k')))
      (((LB.div (N.pull f) M).pull g).g (fun _ => (fun _ => i, k)) (fun _ => (fun _ => i', k'))) =
      gm (𝟙 Z ≫ g ≫ f) x _ (N.g i i') * (gm (𝟙 Z ≫ g) x _ (M.g k k'))⁻¹ := by
  have m₁ : (𝟙 Z : Z ⟶ Z) x ∈ ((LB.div (N.pull f) M).pull g).U (fun _ => (fun _ => i, k)) :=
    mem_pull.2 ⟨mem_pull.2 hi, hk⟩
  have m₂ : (𝟙 Z : Z ⟶ Z) x ∈ ((LB.div (N.pull f) M).pull g).U (fun _ => (fun _ => i', k')) :=
    mem_pull.2 ⟨mem_pull.2 hi', hk'⟩
  refine (gm_pull_g (LB.div (N.pull f) M) g (𝟙 Z) x _ _ m₁ m₂).trans ?_
  refine (gm_div_g (L := N) (F := f) (L' := M) (𝟙 Z ≫ g) x i i' k k' hi hi' hk hk').trans ?_
  rw [Category.assoc]

theorem lbIso_of_same_descent : ∀ {Z P Q : Scheme.{0}} (g : Z ⟶ P) (f : P ⟶ Q), Flat g → LocallyOfFinitePresentation g → Surjective g →
    ∀ (M : LB P), M.IsLB → ∀ (N : LB Q), N.IsLB → ∀ (τ : LB.Gen (M.pull g)), τ.IsGen →
    ∀ (T : LB.Gen (N.pull (g ≫ f))), T.IsGen →
      (∀ (W : Scheme.{0}) (a b : W ⟶ Z), a ≫ g = b ≫ g → ∀ (w : W) (i : N.ι) (k : M.ι), f (g (a w)) ∈ N.U i → g (a w) ∈ M.U k →
        gm a w ((N.pull (g ≫ f)).U fun _ => i) (T.s fun _ => i) * (gm a w ((M.pull g).U fun _ => k) (τ.s fun _ => k))⁻¹ =
          gm b w ((N.pull (g ≫ f)).U fun _ => i) (T.s fun _ => i) * (gm b w ((M.pull g).U fun _ => k) (τ.s fun _ => k))⁻¹) →
      LBIso M (N.pull f) := by
  intro Z P Q g f hfl hlf hsu M hM N hN τ hτ T hT hinv
  have hD : (LB.div (N.pull f) M).IsLB := LB.isLB_div (pull_isLB hN f) hM
  have mem₁ : ∀ (J : PUnit → (LB.div (N.pull f) M).ι) (x : Z), x ∈ ((LB.div (N.pull f) M).pull g).U J →
      f (g x) ∈ N.U ((J PUnit.unit).1 PUnit.unit) := fun J x hx => mem_pull.1 (mem_pull.1 hx).1
  have mem₂ : ∀ (J : PUnit → (LB.div (N.pull f) M).ι) (x : Z), x ∈ ((LB.div (N.pull f) M).pull g).U J →
      g x ∈ M.U (J PUnit.unit).2 := fun J x hx => (mem_pull.1 hx).2
  have le₁ : ∀ J : PUnit → (LB.div (N.pull f) M).ι, ((LB.div (N.pull f) M).pull g).U J ≤
      (N.pull (g ≫ f)).U (fun _ => (J PUnit.unit).1 PUnit.unit) := fun J x hx => mem_pull.2 (mem₁ J x hx)
  have le₂ : ∀ J : PUnit → (LB.div (N.pull f) M).ι, ((LB.div (N.pull f) M).pull g).U J ≤
      (M.pull g).U (fun _ => (J PUnit.unit).2) := fun J x hx => mem_pull.2 (mem₂ J x hx)
  let ω : LB.Gen ((LB.div (N.pull f) M).pull g) :=
    ⟨fun J => res (le₁ J) (T.s _) * (res (le₂ J) (τ.s _))⁻¹⟩
  have germ : ∀ (W : Scheme.{0}) (a : W ⟶ Z) (w : W) (J : PUnit → (LB.div (N.pull f) M).ι)
      (h : a w ∈ ((LB.div (N.pull f) M).pull g).U J),
      gm a w _ (ω.s J) = gm a w ((N.pull (g ≫ f)).U fun _ => (J PUnit.unit).1 PUnit.unit) (T.s _) *
        (gm a w ((M.pull g).U fun _ => (J PUnit.unit).2) (τ.s _))⁻¹ := by
    intro W a w J h
    show gm a w _ (res (le₁ J) (T.s _) * (res (le₂ J) (τ.s _))⁻¹) = _
    rw [map_mul, map_inv, gm_res a w _ h, gm_res a w _ h]
  have hω : ω.IsGen := by
    have split : ∀ J : PUnit → (LB.div (N.pull f) M).ι, ∃ (i : N.ι) (k : M.ι), J = fun _ => (fun _ => i, k) :=
      fun J => ⟨(J PUnit.unit).1 PUnit.unit, (J PUnit.unit).2, rfl⟩
    intro J J'
    obtain ⟨i, k, rfl⟩ := split J
    obtain ⟨i', k', rfl⟩ := split J'
    apply unit_ext
    intro x hx
    have h₁ := hx.1
    have h₂ := hx.2
    have i₁ : f (g x) ∈ N.U i := mem₁ _ x h₁
    have i₂ : f (g x) ∈ N.U i' := mem₁ _ x h₂
    have k₁ : g x ∈ M.U k := mem₂ _ x h₁
    have k₂ : g x ∈ M.U k' := mem₂ _ x h₂
    have eT := gm_gen_pull hT x i i' i₁ i₂
    have eτ := gm_gen_pull hτ x k k' k₁ k₂
    refine (gm_res (𝟙 Z) x _ hx _).trans (Eq.trans ?_ (map_mul _ _ _).symm)
    refine Eq.trans ?_ (congrArg₂ (· * ·) (gm_pull_div_g g f M N x i i' k k' i₁ i₂ k₁ k₂).symm
      (gm_res (𝟙 Z) x _ hx _).symm)
    refine (germ _ (𝟙 Z) x _ h₁).trans (Eq.trans ?_ (congrArg (_ * ·) (germ _ (𝟙 Z) x _ h₂).symm))
    show gm (𝟙 Z) x _ (T.s fun _ => i) * (gm (𝟙 Z) x _ (τ.s fun _ => k))⁻¹ =
      _ * (gm (𝟙 Z) x _ (T.s fun _ => i') * (gm (𝟙 Z) x _ (τ.s fun _ => k'))⁻¹)
    rw [eT, eτ, mul_inv, _root_.mul_mul_mul_comm]
  refine GlobalTheory.T.line_bundle_trivial_of_descended_generator g hfl hlf hsu _ hD ω hω ?_
  intro W a b hab w i hi
  have hpt : g (a w) = g (b w) := by
    have := congrArg (fun q : W ⟶ P => q w) hab
    simpa using this
  have ha : a w ∈ ((LB.div (N.pull f) M).pull g).U (fun _ => i) := mem_pull.2 hi
  have hb : b w ∈ ((LB.div (N.pull f) M).pull g).U (fun _ => i) := mem_pull.2 (hpt ▸ hi)
  rw [germ W a w _ ha, germ W b w _ hb]
  exact hinv W a b hab w _ _ (mem₁ _ _ ha) (mem₂ _ _ ha)

end GlobalTheory.CompanionTheory.RigGlue
