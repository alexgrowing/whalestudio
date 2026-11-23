import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfHasRepUnit
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvcCompOfIso
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.DualCon.ProdGlue

theorem same_precomp {S : Scheme.{0}} {A T U Y Z : Over S} {N : LB (A ⊗ T).left} {M : LB (A ⊗ U).left}
    (hN : N.IsLB) (hM : M.IsLB) {y : Y ⟶ T} {u : Y ⟶ U} (z : Z ⟶ Y)
    (e : Same A N M y u) : Same A N M (z ≫ y) (z ≫ u) := by
  have e' := congrArg (CechPic.pull (lift (fst A Z) (snd A Z ≫ z)).left) ((same_iff hN hM _ _).1 e)
  rw [pull_evc, pull_evc, lift_fst, lift_snd_assoc, lift_snd_assoc, Category.assoc, Category.assoc] at e'
  exact (same_iff hN hM _ _).2 e'

theorem eq_of_same_of_disjoint_cover : ∀ {S : Scheme.{0}} (A : Over S) [GrpObj A] {κ : Type} [Finite κ] (X : Over S) (V : κ → X.left.Opens), (⨆ i, V i = ⊤) → (Pairwise fun i i' => Disjoint (V i) (V i')) → ∀ (Bt : Over S) (B : κ → Over S) (j : ∀ i, B i ⟶ Bt) [∀ i, IsOpenImmersion (j i).left], (⨆ i, (j i).left.opensRange = ⊤) → (Pairwise fun i i' => Disjoint (j i).left.opensRange (j i').left.opensRange) → ∀ (b : ∀ i, B i ⟶ Over.mk ((V i).ι ≫ X.hom)) (bt : Bt ⟶ X), (∀ i, j i ≫ bt = b i ≫ Over.homMk (V i).ι) → ∀ (P : ∀ i, LB (A ⊗ B i).left) (Pt : LB (A ⊗ Bt).left), (∀ i, Rep A (b i) (P i)) → Pt.IsLB → (∀ i, LBIso (Pt.pull (A ◁ j i).left) (P i)) → ∀ (T : Over S) (x y : T ⟶ Bt), x ≫ bt = y ≫ bt → Same A Pt Pt x y → x = y := by
  intro S A _ κ _ X V hV hVd Bt B j _ hj hjd b bt hb P Pt hP hPt hPi T x y hxy e

  have mem : ∀ i (p : Bt.left), bt.left p ∈ V i → p ∈ Set.range (j i).left := by
    intro i p hp
    have hp' : p ∈ (⨆ i', (j i').left.opensRange) := by rw [hj]; trivial
    obtain ⟨i', q, rfl⟩ := (TopologicalSpace.Opens.mem_iSup.1 hp')
    have h1 : bt.left ((j i').left q) ∈ V i' := by
      rw [← Scheme.Hom.comp_apply, ← Over.comp_left, hb i', Over.comp_left, Scheme.Hom.comp_apply]
      change (V i').ι ((b i').left q) ∈ V i'
      exact (Scheme.Opens.range_ι (V i')).subset ⟨_, rfl⟩
    by_cases hii : i' = i
    · subst hii; exact ⟨q, rfl⟩
    · exact absurd (⟨h1, hp⟩ : bt.left ((j i').left q) ∈ (V i' ⊓ V i : X.left.Opens))
        (fun h ↦ (hVd hii).le_bot h)
  have loc : ∀ i, ((x ≫ bt).left ⁻¹ᵁ V i).ι ≫ x.left = ((x ≫ bt).left ⁻¹ᵁ V i).ι ≫ y.left := by
    intro i
    let Ti : Over S := Over.mk (((x ≫ bt).left ⁻¹ᵁ V i).ι ≫ T.hom)
    let w : Ti ⟶ T := Over.homMk ((x ≫ bt).left ⁻¹ᵁ V i).ι rfl
    have lf : ∀ z : T ⟶ Bt, z ≫ bt = x ≫ bt → ∃ zi : Ti ⟶ B i, zi ≫ j i = w ≫ z := by
      intro z hz
      have r : Set.range (w ≫ z).left ⊆ Set.range (j i).left := by
        rintro _ ⟨p, rfl⟩
        apply mem i
        rw [← Scheme.Hom.comp_apply, ← Over.comp_left, Category.assoc, hz, Over.comp_left,
          Scheme.Hom.comp_apply]
        exact (Scheme.Opens.range_ι ((x ≫ bt).left ⁻¹ᵁ V i)).subset ⟨p, rfl⟩
      exact ⟨Over.homMk (IsOpenImmersion.lift (j i).left _ r)
        (by rw [← Over.w (j i), IsOpenImmersion.lift_fac_assoc, Over.w]),
        Over.OverMorphism.ext (IsOpenImmersion.lift_fac _ _ _)⟩
    obtain ⟨xi, hx⟩ := lf x rfl
    obtain ⟨yi, hy⟩ := lf y hxy.symm
    have hQ := (hP i).fam.isLB
    have hb' : xi ≫ b i = yi ≫ b i := by
      have k : xi ≫ b i ≫ Over.homMk (V i).ι = yi ≫ b i ≫ Over.homMk (V i).ι := by
        rw [← hb, reassoc_of% hx, reassoc_of% hy, hxy]
      apply Over.OverMorphism.ext
      rw [← cancel_mono (V i).ι]
      exact congrArg (fun q ↦ q.left) k
    have hs : Same A (P i) (P i) xi yi := by
      have e2 := (same_iff hPt hPt _ _).1 (same_precomp hPt hPt w e)
      rw [same_iff hQ hQ, ← evc_comp_of_iso (j i) hPt hQ (hPi i), ← evc_comp_of_iso (j i) hPt hQ (hPi i),
        Category.assoc, Category.assoc, hx, hy]
      exact e2
    have h3 := Model.rep_ext (hP i) hb' hs
    exact congrArg (fun q ↦ q.left) (show w ≫ x = w ≫ y by rw [← hx, ← hy, h3])
  refine Over.OverMorphism.ext (Scheme.hom_ext_of_forall _ _ fun z ↦ ?_)
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1
    (show (x ≫ bt).left z ∈ ⨆ i, V i by rw [hV]; trivial)
  exact ⟨_, hi, loc i⟩

end GlobalTheory.DualCon.ProdGlue
