import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ToRingActOpOfRingAct
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyHomFixRepTrivial
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfPullbackQuotientEq
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

namespace GlobalTheory.EndLoc.HomFixUnr

theorem base_eq {X Y Z Y' Z' : Scheme.{0}} (b : Y ⟶ X) (c : Z ⟶ Y) (b' : Y' ⟶ X) (c' : Z' ⟶ Y')
    (h : Z' ⟶ Z) (e : c' ≫ b' = h ≫ c ≫ b) (y : Z') : b' (c' y) = b (c (h y)) := by
  have := congrArg (fun k => k.base y) e
  simpa only [Scheme.Hom.comp_base, TopCat.hom_comp, ContinuousMap.comp_apply] using this

def chartPullPullPull {X Y Z Y' Z' : Scheme.{0}} (M : LB X) (b : Y ⟶ X) (c : Z ⟶ Y) (b' : Y' ⟶ X) (c' : Z' ⟶ Y')
    (h : Z' ⟶ Z) (e : c' ≫ b' = h ≫ c ≫ b) : ChartPull ((M.pull b').pull c') ((M.pull b).pull c) h where
  idx J := J
  le J y hy := by
    have h1 := mem_pull.1 (mem_pull.1 hy)
    show h y ∈ ((M.pull b).pull c).U J
    refine mem_pull.2 (mem_pull.2 ?_)
    rw [← base_eq b c b' c' h e y]; exact h1
  g y J J' hj hj' := by
    have hj2 : (𝟙 Z' ≫ c') y ∈ (M.pull b').U (J PUnit.unit) := mem_pull.1 hj
    have hj2' : (𝟙 Z' ≫ c') y ∈ (M.pull b').U (J' PUnit.unit) := mem_pull.1 hj'
    have hk : ∀ K : PUnit → PUnit → M.ι, y ∈ ((M.pull b').pull c').U K → h y ∈ ((M.pull b).pull c).U K := fun K hK =>
      mem_pull.2 (mem_pull.2 (by rw [← base_eq b c b' c' h e y]; exact mem_pull.1 (mem_pull.1 hK)))
    have hk2 : (h ≫ c) y ∈ (M.pull b).U (J PUnit.unit) := by
      have := mem_pull.1 (hk J hj); simpa using this
    have hk2' : (h ≫ c) y ∈ (M.pull b).U (J' PUnit.unit) := by
      have := mem_pull.1 (hk J' hj'); simpa using this
    rw [gm_pull_g (M.pull b') c' (𝟙 Z') y J J' hj hj', gm_pull_g M b' (𝟙 Z' ≫ c') y _ _ hj2 hj2',
      gm_pull_g (M.pull b) c h y J J' (hk J hj) (hk J' hj'), gm_pull_g M b (h ≫ c) y _ _ hk2 hk2']
    have e' : (𝟙 Z' ≫ c') ≫ b' = (h ≫ c) ≫ b := by rw [Category.id_comp, e, Category.assoc]
    rw [e']

theorem lbIso_pull_square {XA XB YA YB ZA ZB : Scheme.{0}} (L : LB XA) (M : LB XB) (φA : YA ⟶ XA) (φB : YB ⟶ XB)
    (Φ : YA ⟶ YB) (ψA : ZA ⟶ XA) (ψB : ZB ⟶ XB) (v : ZA ⟶ ZB) (χA : ZA ⟶ YA) (χB : ZB ⟶ YB)
    (hA : χA ≫ φA = ψA) (hB : χB ≫ φB = ψB) (hv : v ≫ χB = χA ≫ Φ)
    (H : LBIso (L.pull φA) ((M.pull φB).pull Φ)) : LBIso (L.pull ψA) ((M.pull ψB).pull v) :=
  LBIso.chartPull (chartPullSame L (fun _ => ψA) (fun _ => φA) (fun _ => 1) χA fun _ => hA.symm)
    (chartPullPullPull M φB Φ ψB v χA (by rw [← hB, ← Category.assoc, hv, Category.assoc])) H

end GlobalTheory.EndLoc.HomFixUnr

namespace GlobalTheory.EndLoc

open GlobalTheory.EndLoc.HomFixUnr in

theorem formallyUnramified_homFixRep : ∀ (S : Scheme.{0}) (A B : Over S) [GrpObj A] [IsCommMonObj A] [GrpObj B]
    [IsCommMonObj B] (L : LB A.left) (M : LB B.left) (R : HomFixRep A B L M), IsAbelianScheme A → IsAbelianScheme B →
    FormallyUnramified R.π := by
  intro S A B _ _ _ _ L M Rp hA _
  refine FormallyUnramified.of_hom_ext _ fun R R₀ q hq hsq g₁ g₂ hi hg ↦ ?_
  let f : Spec R ⟶ S := g₁ ≫ Rp.π
  let AT : Over (Spec R) := (Over.pullback f).obj A
  let BT : Over (Spec R) := (Over.pullback f).obj B
  let ψA : AT.left ⟶ A.left := pullback.fst A.hom f
  let ψB : BT.left ⟶ B.left := pullback.fst B.hom f
  have hAT : IsGrpPullback AT A f ψA := isGrpPullback_pullback A f
  have hBT : IsGrpPullback BT B f ψB := isGrpPullback_pullback B f
  have hAbT : IsAbelianScheme AT := GlobalTheory.isAbelianScheme_pullback_obj f A hA
  have tr : ∀ (g : Spec R ⟶ Rp.H), g ≫ Rp.π = f → ∀ (G : Over S) [GrpObj G] (GH : Over Rp.H) [GrpObj GH]
      (φ : GH.left ⟶ G.left), IsGrpPullback GH G Rp.π φ →
      ∃ e : (Over.pullback f).obj G ≅ (Over.pullback g).obj GH, IsMonHom e.hom ∧
        IsGrpPullback ((Over.pullback f).obj G) GH g (e.hom.left ≫ pullback.fst GH.hom g) ∧
        (e.hom.left ≫ pullback.fst GH.hom g) ≫ φ = pullback.fst G.hom f := by
    intro g hgf G _ GH _ φ hG
    have h' : IsGrpPullback ((Over.pullback g).obj GH) G f (pullback.fst GH.hom g ≫ φ) :=
      ((isGrpPullback_pullback GH g).comp hG).congr hgf rfl
    obtain ⟨e, he, heφ⟩ := grpPullback_iso (isGrpPullback_pullback G f) h'
    haveI := he
    exact ⟨e, he, ((isGrpPullback_of_iso e).comp (isGrpPullback_pullback GH g)).congr (Category.id_comp _) rfl,
      by rw [Category.assoc, heφ]⟩
  have build : ∀ g : Spec R ⟶ Rp.H, g ≫ Rp.π = f → ∃ (v : AT ⟶ BT) (χA : AT.left ⟶ Rp.AH.left)
      (χB : BT.left ⟶ Rp.BH.left), IsMonHom v ∧ IsGrpPullback AT Rp.AH g χA ∧ IsGrpPullback BT Rp.BH g χB ∧
        χA ≫ Rp.φA = ψA ∧ χB ≫ Rp.φB = ψB ∧ v.left ≫ χB = χA ≫ Rp.Φ.left := by
    intro g hgf
    obtain ⟨eA, heA, hpA, hφA⟩ := tr g hgf A Rp.AH Rp.φA Rp.pbA
    obtain ⟨eB, heB, hpB, hφB⟩ := tr g hgf B Rp.BH Rp.φB Rp.pbB
    haveI := heA
    haveI := heB
    haveI := Rp.hom
    have hie : eB.inv.left ≫ eB.hom.left = 𝟙 _ := by rw [← Over.comp_left, eB.inv_hom_id, Over.id_left]
    refine ⟨eA.hom ≫ (Over.pullback g).map Rp.Φ ≫ eB.inv, _, _, inferInstance, hpA, hpB, hφA, hφB, ?_⟩
    have hm : ((Over.pullback g).map Rp.Φ).left ≫ pullback.fst Rp.BH.hom g =
        pullback.fst Rp.AH.hom g ≫ Rp.Φ.left := pullback.lift_fst _ _ _
    simp only [Over.comp_left, Category.assoc]
    rw [reassoc_of% hie, hm]
  obtain ⟨v₁, χA₁, χB₁, hv₁, hpA₁, hpB₁, hχA₁, hχB₁, hχ₁⟩ := build g₁ rfl
  obtain ⟨v₂, χA₂, χB₂, hv₂, hpA₂, hpB₂, hχA₂, hχB₂, hχ₂⟩ := build g₂ hg.symm
  let I : Ideal R := RingHom.ker q.hom
  have hI : IsNilpotent I := ⟨2, hsq⟩
  let j : Sp (R ⧸ I) ⟶ Sp R := spMap (Ideal.Quotient.mk I)
  have hj : j ≫ g₁ = j ≫ g₂ := by
    let ε : (R ⧸ I) ≃+* R₀ := RingHom.quotientKerEquivOfSurjective hq
    have hε : Spec.map q = Spec.map (CommRingCat.ofHom ε.toRingHom) ≫ j := by
      rw [← Spec.map_comp]
      congr 1
    haveI : IsIso (CommRingCat.ofHom ε.toRingHom) := ε.toCommRingCatIso.isIso_hom
    rw [hε, Category.assoc, Category.assoc] at hi
    exact (cancel_epi _).1 hi
  have hχA : pullback.fst AT.hom j ≫ χA₁ = pullback.fst AT.hom j ≫ χA₂ := by
    apply Rp.pbA.1.hom_ext
    · rw [Category.assoc, Category.assoc, hχA₁, hχA₂]
    · rw [Category.assoc, Category.assoc, hpA₁.1.w, hpA₂.1.w, pullback.condition_assoc, pullback.condition_assoc, hj]
  have hv : v₁ = v₂ := by
    refine GlobalTheory.NilRigidity.eq_of_pullback_quotient_eq I hI AT BT hAbT v₁ v₂ ?_
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · rw [show ((Over.pullback j).map v₁).left ≫ pullback.fst BT.hom j =
          pullback.fst AT.hom j ≫ v₁.left from pullback.lift_fst _ _ _,
        show ((Over.pullback j).map v₂).left ≫ pullback.fst BT.hom j =
          pullback.fst AT.hom j ≫ v₂.left from pullback.lift_fst _ _ _]
      apply hBT.1.hom_ext
      · calc (pullback.fst AT.hom j ≫ v₁.left) ≫ ψB
            = pullback.fst AT.hom j ≫ v₁.left ≫ χB₁ ≫ Rp.φB := by rw [hχB₁, Category.assoc]
          _ = pullback.fst AT.hom j ≫ χA₁ ≫ Rp.Φ.left ≫ Rp.φB := by rw [reassoc_of% hχ₁]
          _ = pullback.fst AT.hom j ≫ χA₂ ≫ Rp.Φ.left ≫ Rp.φB := by rw [reassoc_of% hχA]
          _ = pullback.fst AT.hom j ≫ v₂.left ≫ χB₂ ≫ Rp.φB := by rw [reassoc_of% hχ₂]
          _ = (pullback.fst AT.hom j ≫ v₂.left) ≫ ψB := by rw [hχB₂, Category.assoc]
      · rw [Category.assoc, Category.assoc, Over.w v₁, Over.w v₂]
    · rw [show ((Over.pullback j).map v₁).left ≫ pullback.snd BT.hom j =
          pullback.snd AT.hom j from pullback.lift_snd _ _ _,
        show ((Over.pullback j).map v₂).left ≫ pullback.snd BT.hom j =
          pullback.snd AT.hom j from pullback.lift_snd _ _ _]
  have hL : LBIso (L.pull ψA) ((M.pull ψB).pull v₁.left) :=
    lbIso_pull_square L M Rp.φA Rp.φB Rp.Φ.left ψA ψB v₁.left χA₁ χB₁ hχA₁ hχB₁ hχ₁ Rp.iso
  obtain ⟨g, -, hg'⟩ := Rp.rep (Spec R) f AT BT ψA ψB v₁ hAT hBT hv₁ hL
  have e1 := hg' g₁ ⟨rfl, χA₁, χB₁, hpA₁, hpB₁, hχA₁, hχB₁, hχ₁⟩
  have e2 := hg' g₂ ⟨hg.symm, χA₂, χB₂, hpA₂, hpB₂, hχA₂, hχB₂, by rw [hv]; exact hχ₂⟩
  rw [e1, e2]

end GlobalTheory.EndLoc
