import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ToRingActOpOfRingAct
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyHomFixRepTrivial
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfPullbackQuotientEq
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.EndLoc.ActUnr

section Chart

variable {X Y₁ Y₂ Z W : Scheme.{0}}

def chartPullPullAlong (L : LB X) (a₁ : Y₁ ⟶ X) (a₂ : Z ⟶ Y₁) (c₁ : Y₂ ⟶ X) (c₂ : W ⟶ Y₂) (h : Z ⟶ W)
    (e : a₂ ≫ a₁ = h ≫ c₂ ≫ c₁) : ChartPull ((L.pull a₁).pull a₂) ((L.pull c₁).pull c₂) h where
  idx J := fun _ _ => J PUnit.unit PUnit.unit
  le J y hy := by
    have h₁ := mem_pull.1 (mem_pull.1 hy)
    have h₂ : (a₂ ≫ a₁) y ∈ L.U (J PUnit.unit PUnit.unit) := by simpa using h₁
    rw [e] at h₂
    exact mem_pull.2 (mem_pull.2 (by simpa using h₂))
  g y J J' hj hj' := by
    have hc : ∀ K : PUnit → PUnit → L.ι, y ∈ ((L.pull a₁).pull a₂).U K →
        h y ∈ ((L.pull c₁).pull c₂).U (fun _ _ => K PUnit.unit PUnit.unit) := fun K hK => by
      have h₁ := mem_pull.1 (mem_pull.1 hK)
      have h₂ : (a₂ ≫ a₁) y ∈ L.U (K PUnit.unit PUnit.unit) := by simpa using h₁
      rw [e] at h₂
      exact mem_pull.2 (mem_pull.2 (by simpa using h₂))
    have l₁ := gm_pull_g (L.pull a₁) a₂ (𝟙 Z) y J J' hj hj'
    rw [Category.id_comp] at l₁
    have l₂ := gm_pull_g L a₁ a₂ y (J PUnit.unit) (J' PUnit.unit) (mem_pull.1 hj) (mem_pull.1 hj')
    have l₃ := gm_pull_g (L.pull c₁) c₂ h y (fun _ _ => J PUnit.unit PUnit.unit)
      (fun _ _ => J' PUnit.unit PUnit.unit) (hc J hj) (hc J' hj')
    have l₄ := gm_pull_g L c₁ (h ≫ c₂) y (fun _ => J PUnit.unit PUnit.unit) (fun _ => J' PUnit.unit PUnit.unit)
      (mem_pull.1 (hc J hj)) (mem_pull.1 (hc J' hj'))
    rw [l₁, l₂, l₃, l₄, e, Category.assoc]

theorem lbIso_pullPull_along (Q : LB X) (φ₂ : Y₁ ⟶ X) (m₁ m₂ : Y₁ ⟶ Y₁) (φ₂' : Y₂ ⟶ X) (m₁' m₂' : Y₂ ⟶ Y₂)
    (u : Y₂ ⟶ Y₁) (hφ : φ₂' = u ≫ φ₂) (h₁ : m₁' ≫ u = u ≫ m₁) (h₂ : m₂' ≫ u = u ≫ m₂)
    (H : LBIso ((Q.pull φ₂).pull m₁) ((Q.pull φ₂).pull m₂)) :
    LBIso ((Q.pull φ₂').pull m₁') ((Q.pull φ₂').pull m₂') :=
  LBIso.chartPull
    (chartPullPullAlong Q φ₂' m₁' φ₂ m₁ u (by rw [hφ, ← Category.assoc, h₁, Category.assoc]))
    (chartPullPullAlong Q φ₂' m₂' φ₂ m₂ u (by rw [hφ, ← Category.assoc, h₂, Category.assoc])) H

end Chart

section Square

variable {S S' : Scheme.{0}} {f : S' ⟶ S} {G : Over S} {B : Over S'} {φ : B.left ⟶ G.left}

def sqMap (w : φ ≫ G.hom = B.hom ≫ f) : (B ⊗ B).left ⟶ (G ⊗ G).left :=
  (lift (pushPt w (fst B B)) (pushPt w (snd B B))).left

theorem sqMap_fst (w : φ ≫ G.hom = B.hom ≫ f) : sqMap w ≫ (fst G G).left = (fst B B).left ≫ φ :=
  congrArg (fun z => z.left) (lift_fst (pushPt w (fst B B)) (pushPt w (snd B B)))

theorem sqMap_snd (w : φ ≫ G.hom = B.hom ≫ f) : sqMap w ≫ (snd G G).left = (snd B B).left ≫ φ :=
  congrArg (fun z => z.left) (lift_snd (pushPt w (fst B B)) (pushPt w (snd B B)))

theorem left_hom_ext {H Z : Scheme.{0}} {G : Over H} {x y : Z ⟶ (G ⊗ G).left}
    (h1 : x ≫ (fst G G).left = y ≫ (fst G G).left) (h2 : x ≫ (snd G G).left = y ≫ (snd G G).left) : x = y := by
  have hw : y ≫ (G ⊗ G).hom = x ≫ (G ⊗ G).hom := by
    rw [← Over.w (fst G G), ← Category.assoc, ← h1, Category.assoc]
  let x' : Over.mk (x ≫ (G ⊗ G).hom) ⟶ G ⊗ G := Over.homMk x rfl
  let y' : Over.mk (x ≫ (G ⊗ G).hom) ⟶ G ⊗ G := Over.homMk y hw
  have : x' = y' := CartesianMonoidalCategory.hom_ext _ _ (Over.OverMorphism.ext h1) (Over.OverMorphism.ext h2)
  exact congrArg (fun t => t.left) this

theorem lift_left_comp_sqMap (w : φ ≫ G.hom = B.hom ≫ f) (x' y' : B ⊗ B ⟶ B) (x y : G ⊗ G ⟶ G)
    (hx : x'.left ≫ φ = sqMap w ≫ x.left) (hy : y'.left ≫ φ = sqMap w ≫ y.left) :
    (lift x' y').left ≫ sqMap w = sqMap w ≫ (lift x y).left := by
  apply left_hom_ext
  · rw [Category.assoc, sqMap_fst, ← Category.assoc, ← Over.comp_left, lift_fst, hx, Category.assoc,
      ← Over.comp_left, lift_fst]
  · rw [Category.assoc, sqMap_snd, ← Category.assoc, ← Over.comp_left, lift_snd, hy, Category.assoc,
      ← Over.comp_left, lift_snd]

end Square

section Act

variable {O : Type} [Ring O]

theorem isRAct_pullback {H T : Scheme.{0}} (g : T ⟶ H) (AH : Over H) [GrpObj AH] (act : O → (AH ⟶ AH))
    (h : IsRAct AH act) : IsRAct ((Over.pullback g).obj AH) (fun a => (Over.pullback g).map (act a)) := by
  refine ⟨fun a => ?_, ?_, fun a b => ?_, fun a b => ?_⟩
  · haveI := h.1 a
    infer_instance
  · dsimp only
    rw [h.2.1]
    exact (Over.pullback g).map_id _
  · dsimp only
    rw [h.2.2.1, Functor.map_comp]
  · dsimp only
    rw [h.2.2.2, Functor.map_mul]

theorem isRAct_conj {T : Scheme.{0}} {B C : Over T} [GrpObj B] [GrpObj C] (e : B ≅ C) [IsMonHom e.hom]
    (act : O → (C ⟶ C)) (h : IsRAct C act) : IsRAct B (fun a => e.hom ≫ act a ≫ e.inv) := by
  refine ⟨fun a => ?_, ?_, fun a b => ?_, fun a b => ?_⟩
  · haveI := h.1 a
    infer_instance
  · simp only [h.2.1, Category.id_comp, Iso.hom_inv_id]
  · simp only [h.2.2.1, Category.assoc, Iso.inv_hom_id_assoc]
  · dsimp only
    rw [h.2.2.2, MonObj.mul_comp, MonObj.comp_mul]

theorem adj_along {H T : Scheme.{0}} {AH : Over H} {AT : Over T} [GrpObj AH] [GrpObj AT] {g : T ⟶ H}
    {χ : AT.left ⟶ AH.left} (w : χ ≫ AH.hom = AT.hom ≫ g) (act : O → (AH ⟶ AH)) (v : O → (AT ⟶ AT))
    (hv : ∀ a, (v a).left ≫ χ = χ ≫ (act a).left) {X : Scheme.{0}} (Q : LB X) (φ₂ : (AH ⊗ AH).left ⟶ X)
    (bar : O → O) (h : Adj AH (Q.pull φ₂) bar act) : Adj AT (Q.pull (sqMap w ≫ φ₂)) bar v := fun a =>
  lbIso_pullPull_along Q φ₂ _ _ (sqMap w ≫ φ₂) _ _ (sqMap w) rfl
    (lift_left_comp_sqMap w _ _ _ _
      (by rw [Over.comp_left, Category.assoc, hv, ← Category.assoc, ← sqMap_fst w, Category.assoc, Over.comp_left])
      (by rw [sqMap_snd]))
    (lift_left_comp_sqMap w _ _ _ _ (by rw [sqMap_fst])
      (by rw [Over.comp_left, Category.assoc, hv, ← Category.assoc, ← sqMap_snd w, Category.assoc, Over.comp_left]))
    (h a)

end Act

end GlobalTheory.EndLoc.ActUnr

namespace GlobalTheory.EndLoc

open ActUnr in

theorem formallyUnramified_actRep : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (Q : LB (A ⊗ A).left)
    (O : Type) [Ring O] (bar : O → O) (R : ActRep A Q bar), IsAbelianScheme A → FormallyUnramified R.π := by
  intro S A _ _ Q O _ bar Rp hA
  refine FormallyUnramified.of_hom_ext _ fun R R₀ q hq hsq g₁ g₂ hi hg ↦ ?_
  let f : Spec R ⟶ S := g₁ ≫ Rp.π
  let AT : Over (Spec R) := (Over.pullback f).obj A
  let ψ : AT.left ⟶ A.left := pullback.fst A.hom f
  have hAT : IsGrpPullback AT A f ψ := isGrpPullback_pullback A f
  have hAbT : IsAbelianScheme AT := GlobalTheory.isAbelianScheme_pullback_obj f A hA
  have build : ∀ g : Spec R ⟶ Rp.H, g ≫ Rp.π = f → ∃ (v : O → (AT ⟶ AT)) (χ : AT.left ⟶ Rp.AH.left)
      (φ₂' : (AT ⊗ AT).left ⟶ (A ⊗ A).left),
      IsRAct AT v ∧ IsSquare ψ φ₂' ∧ Adj AT (Q.pull φ₂') bar v ∧ IsGrpPullback AT Rp.AH g χ ∧ χ ≫ Rp.φ = ψ ∧
        ∀ a, (v a).left ≫ χ = χ ≫ (Rp.act a).left := by
    intro g hgf
    have h' : IsGrpPullback ((Over.pullback g).obj Rp.AH) A f (pullback.fst Rp.AH.hom g ≫ Rp.φ) :=
      ((isGrpPullback_pullback Rp.AH g).comp Rp.pb).congr hgf rfl
    obtain ⟨e, he, heφ⟩ := grpPullback_iso hAT h'
    haveI := he
    have hie : e.inv.left ≫ e.hom.left = 𝟙 _ := by rw [← Over.comp_left, e.inv_hom_id, Over.id_left]
    let χ : AT.left ⟶ Rp.AH.left := e.hom.left ≫ pullback.fst Rp.AH.hom g
    let v : O → (AT ⟶ AT) := fun a ↦ e.hom ≫ (Over.pullback g).map (Rp.act a) ≫ e.inv
    have hχφ : χ ≫ Rp.φ = ψ := by simp only [χ, Category.assoc]; exact heφ
    have hw : χ ≫ Rp.AH.hom = AT.hom ≫ g := by
      simp only [χ]
      rw [Category.assoc, pullback.condition, ← Category.assoc]
      congr 1
      exact Over.w e.hom
    have hv : ∀ a, (v a).left ≫ χ = χ ≫ (Rp.act a).left := fun a ↦ by
      have hm : ((Over.pullback g).map (Rp.act a)).left ≫ pullback.fst Rp.AH.hom g =
          pullback.fst Rp.AH.hom g ≫ (Rp.act a).left := pullback.lift_fst _ _ _
      simp only [v, χ, Over.comp_left, Category.assoc]
      rw [reassoc_of% hie, hm]
    have hR : IsRAct AT v := isRAct_conj e _ (isRAct_pullback g Rp.AH Rp.act Rp.isAct)
    refine ⟨v, χ, sqMap hw ≫ Rp.φ₂, hR, ⟨?_, ?_⟩, adj_along hw Rp.act v hv Q Rp.φ₂ bar Rp.adj,
      Rp.pb.cancel ((hAT.congr hgf.symm hχφ.symm)) hw, hχφ, hv⟩
    · rw [Category.assoc, Rp.sq.1, ← Category.assoc, sqMap_fst, Category.assoc, hχφ]
    · rw [Category.assoc, Rp.sq.2, ← Category.assoc, sqMap_snd, Category.assoc, hχφ]
  obtain ⟨v₁, χ₁, φ₂₁, hR₁, hsq₁, hadj₁, hpb₁, hχ₁φ, hχ₁u⟩ := build g₁ rfl
  obtain ⟨v₂, χ₂, -, hR₂, -, -, hpb₂, hχ₂φ, hχ₂u⟩ := build g₂ hg.symm
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
  have hχ : pullback.fst AT.hom j ≫ χ₁ = pullback.fst AT.hom j ≫ χ₂ := by
    apply Rp.pb.1.hom_ext
    · rw [Category.assoc, Category.assoc, hχ₁φ, hχ₂φ]
    · rw [Category.assoc, Category.assoc, hpb₁.1.w, hpb₂.1.w, pullback.condition_assoc, pullback.condition_assoc, hj]
  have hv : ∀ a, v₁ a = v₂ a := fun a ↦ by
    haveI := hR₁.1 a
    haveI := hR₂.1 a
    refine GlobalTheory.NilRigidity.eq_of_pullback_quotient_eq I hI AT AT hAbT (v₁ a) (v₂ a) ?_
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · rw [show ((Over.pullback j).map (v₁ a)).left ≫ pullback.fst AT.hom j =
          pullback.fst AT.hom j ≫ (v₁ a).left from pullback.lift_fst _ _ _,
        show ((Over.pullback j).map (v₂ a)).left ≫ pullback.fst AT.hom j =
          pullback.fst AT.hom j ≫ (v₂ a).left from pullback.lift_fst _ _ _]
      apply hAT.1.hom_ext
      · calc (pullback.fst AT.hom j ≫ (v₁ a).left) ≫ ψ
            = pullback.fst AT.hom j ≫ (v₁ a).left ≫ χ₁ ≫ Rp.φ := by rw [hχ₁φ, Category.assoc]
          _ = pullback.fst AT.hom j ≫ χ₁ ≫ (Rp.act a).left ≫ Rp.φ := by rw [reassoc_of% (hχ₁u a)]
          _ = pullback.fst AT.hom j ≫ χ₂ ≫ (Rp.act a).left ≫ Rp.φ := by rw [reassoc_of% hχ]
          _ = pullback.fst AT.hom j ≫ (v₂ a).left ≫ χ₂ ≫ Rp.φ := by rw [reassoc_of% (hχ₂u a)]
          _ = (pullback.fst AT.hom j ≫ (v₂ a).left) ≫ ψ := by rw [hχ₂φ, Category.assoc]
      · rw [Category.assoc, Category.assoc, Over.w (v₁ a), Over.w (v₂ a)]
    · rw [show ((Over.pullback j).map (v₁ a)).left ≫ pullback.snd AT.hom j =
          pullback.snd AT.hom j from pullback.lift_snd _ _ _,
        show ((Over.pullback j).map (v₂ a)).left ≫ pullback.snd AT.hom j =
          pullback.snd AT.hom j from pullback.lift_snd _ _ _]
  obtain ⟨g, -, hg'⟩ := Rp.rep (Spec R) f AT ψ φ₂₁ v₁ hAT hsq₁ hR₁ hadj₁
  have e1 := hg' g₁ ⟨rfl, χ₁, hpb₁, hχ₁φ, hχ₁u⟩
  have e2 := hg' g₂ ⟨hg.symm, χ₂, hpb₂, hχ₂φ, fun a ↦ by rw [hv a]; exact hχ₂u a⟩
  rw [e1, e2]

end GlobalTheory.EndLoc
