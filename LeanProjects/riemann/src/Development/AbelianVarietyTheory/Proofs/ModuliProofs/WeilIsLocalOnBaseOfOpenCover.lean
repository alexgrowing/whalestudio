import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueHom
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsIffOfIsGrpPullbackComm
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.WeilLocal

open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.CommPairing

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {k : ℤ}

private theorem gm_comp_global_eq_gm_units_map {X Y Z : Scheme.{0}} (f : Z ⟶ Y) (g : Y ⟶ X) (z : Z) (c : Γ(X, ⊤)ˣ) :
    gm (f ≫ g) z ⊤ c = gm f z ⊤ (Units.map g.appTop.hom.toMonoidHom c) := by
  unfold gm pullU
  rw [dif_pos (show (f ≫ g) z ∈ (⊤ : X.Opens) from trivial), dif_pos (show f z ∈ (⊤ : Y.Opens) from trivial)]
  ext
  simp only [MonoidHom.comp_apply, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe, Scheme.Hom.comp_app, CommRingCat.hom_comp, RingHom.comp_apply, Scheme.Hom.appTop]
  rfl

theorem commIsOf_of_retract (hL : L.IsLB) {T T' : Over S} (g : T' ⟶ T) (h : T ⟶ T') (w : g ≫ h = 𝟙 T')
    {c : Γ(T.left, ⊤)ˣ} (θx' θy' : ThetaGrp A L k T')
    (H : ∀ θx θy : ThetaGrp A L k T, θx.pt = h ≫ θx'.pt → θy.pt = h ≫ θy'.pt → CommIsOf A L k θx θy c) :
    CommIsOf A L k θx' θy' (Units.map g.left.appTop.hom.toMonoidHom c) := by
  obtain ⟨θx, hx, hxv⟩ := exists_pull hL h θx'
  obtain ⟨θy, hy, hyv⟩ := exists_pull hL h θy'
  have Hc := (commIsOf_iff hL θx θy c).1 (H θx θy hx hy)
  rw [commIsOf_iff hL]
  intro Z r z J hJ
  have e := Hc Z (r ≫ (g ▷ A).left) z J hJ
  have e1 : r ≫ (g ▷ A).left ≫ (h ▷ A).left = r := by
    rw [← Over.comp_left, ← comp_whiskerRight, w, id_whiskerRight, Over.id_left, Category.comp_id]
  have e2 : ∀ x : T' ⟶ A, r ≫ (g ▷ A).left ≫ (translT A (h ≫ x)).left ≫ (h ▷ A).left = r ≫ (translT A x).left := by
    intro x
    rw [← Over.comp_left _ _ _ (translT A (h ≫ x)), whisker_translT, Over.comp_left, ← Category.assoc (g ▷ A).left,
      ← Over.comp_left _ _ _ (g ▷ A), ← comp_whiskerRight, w, id_whiskerRight, Over.id_left, Category.id_comp]
  have e3 : r ≫ (g ▷ A).left ≫ (fst T A).left = (r ≫ (fst T' A).left) ≫ g.left := by
    rw [← Over.comp_left, whiskerRight_fst, Over.comp_left, Category.assoc]
  rw [hxv _ _ _ _ hJ, hxv _ _ _ _ hJ, hyv _ _ _ _ hJ, hyv _ _ _ _ hJ, hx, hy] at e
  simp only [Category.assoc] at e
  rw [e1, e2, e2, e3, gm_comp_global_eq_gm_units_map] at e
  exact e

private theorem exists_overRes_section_image_openImmersion {T T' : Over S} (j : T' ⟶ T) [IsOpenImmersion j.left]
    (V' : T'.left.Opens) :
    ∃ (a : overRes V' ⟶ overRes (j.left ''ᵁ V')) (b : overRes (j.left ''ᵁ V') ⟶ overRes V'),
      b ≫ a = 𝟙 _ ∧ a ≫ overResι (j.left ''ᵁ V') = overResι V' ≫ j := by
  have he : (j.left.isoImage V').hom ≫ (j.left ''ᵁ V').ι = V'.ι ≫ j.left := Scheme.Hom.isoImage_hom_ι _ _
  refine ⟨Over.homMk (j.left.isoImage V').hom ?_, Over.homMk (j.left.isoImage V').inv ?_, ?_, ?_⟩
  · show (j.left.isoImage V').hom ≫ (j.left ''ᵁ V').ι ≫ T.hom = V'.ι ≫ T'.hom
    rw [← Category.assoc, he, Category.assoc, Over.w j]
  · show (j.left.isoImage V').inv ≫ V'.ι ≫ T'.hom = (j.left ''ᵁ V').ι ≫ T.hom
    rw [← Over.w j, ← Category.assoc V'.ι, ← he, Category.assoc, Iso.inv_hom_id_assoc]
  · apply Over.OverMorphism.ext
    show (j.left.isoImage V').inv ≫ (j.left.isoImage V').hom = 𝟙 _
    exact Iso.inv_hom_id _
  · apply Over.OverMorphism.ext
    show (j.left.isoImage V').hom ≫ (j.left ''ᵁ V').ι = V'.ι ≫ j.left
    exact he

theorem local_of_openImmersion (hL : L.IsLB) {T T' : Over S} (j : T' ⟶ T) [IsOpenImmersion j.left]
    {x y : T ⟶ A} {c : Γ(T.left, ⊤)ˣ}
    (H : WeilIs A L k (j ≫ x) (j ≫ y) (Units.map j.left.appTop.hom.toMonoidHom c)) (p : T'.left) :
    ∃ V : T.left.Opens, j.left p ∈ V ∧
      (∃ θx θy : ThetaGrp A L k (overRes V), θx.pt = overResι V ≫ x ∧ θy.pt = overResι V ≫ y) ∧
      ∀ θx θy : ThetaGrp A L k (overRes V), θx.pt = overResι V ≫ x → θy.pt = overResι V ≫ y →
        CommIsOf A L k θx θy (unitRes V c) := by
  obtain ⟨V', hpV', ⟨θx₀, θy₀, hx₀, hy₀⟩, HV'⟩ := H p
  obtain ⟨a, b, hba, ha⟩ := exists_overRes_section_image_openImmersion j V'
  have hb : b ≫ overResι V' ≫ j = overResι (j.left ''ᵁ V') := by
    rw [← ha, ← Category.assoc, hba, Category.id_comp]
  refine ⟨j.left ''ᵁ V', ⟨p, hpV', rfl⟩, ?_, ?_⟩
  · obtain ⟨θx, hx, -⟩ := exists_pull hL b θx₀
    obtain ⟨θy, hy, -⟩ := exists_pull hL b θy₀
    refine ⟨θx, θy, ?_, ?_⟩
    · rw [hx, hx₀, ← hb]
      simp only [Category.assoc]
    · rw [hy, hy₀, ← hb]
      simp only [Category.assoc]
  · intro θx θy hx hy
    have key := commIsOf_of_retract hL b a hba θx θy
      (c := unitRes V' (Units.map j.left.appTop.hom.toMonoidHom c))
      (fun θ₁ θ₂ h₁ h₂ => HV' θ₁ θ₂ (by rw [h₁, hx, ← Category.assoc, ha, Category.assoc])
        (by rw [h₂, hy, ← Category.assoc, ha, Category.assoc]))
    have hbl : b.left ≫ V'.ι ≫ j.left = (j.left ''ᵁ V').ι := congrArg Over.Hom.left hb
    have hu : Units.map b.left.appTop.hom.toMonoidHom (unitRes V' (Units.map j.left.appTop.hom.toMonoidHom c)) =
        unitRes (j.left ''ᵁ V') c := by
      unfold unitRes
      rw [← hbl]
      ext
      simp only [Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe, Scheme.Hom.comp_app,
        CommRingCat.hom_comp, RingHom.comp_apply, Scheme.Hom.appTop]
      rfl
    rw [hu] at key
    exact key

end GlobalTheory.WeilLocal

theorem GlobalTheory.weilIs_of_openCover : ∀ (S : Scheme.{0}) (I : Type) (U : I → S.Opens) (A : Over S) [GrpObj A] (G : ∀ i, Over (U i).toScheme) [∀ i, GrpObj (G i)] (ψ : ∀ i, (G i).left ⟶ A.left), iSup U = ⊤ → (∀ i, IsGrpPullback (G i) A (U i).ι (ψ i)) → ∀ (L : LB A.left) (M : ∀ i, LB (G i).left), L.IsLB → (∀ i, (M i).IsLB) → (∀ i, LBIso (M i) (L.pull (ψ i))) → IsAbelianScheme A → (∀ i, IsAbelianScheme (G i)) → ∀ (k : ℤ) (x y : Out.baseOver S ⟶ A) (x' y' : ∀ i, Out.baseOver (U i).toScheme ⟶ G i) (c : Γ(S, ⊤)ˣ), (∀ i, (x' i).left ≫ ψ i = (U i).ι ≫ x.left) → (∀ i, (y' i).left ≫ ψ i = (U i).ι ≫ y.left) → (∀ i, Out.WeilIs (G i) (M i) k (x' i) (y' i) (Units.map (U i).ι.appTop.hom.toMonoidHom c)) → Out.WeilIs A L k x y c := by
  intro S I U A _ G _ ψ hU hψ L M hL hM hML hA hG k x y x' y' c hx hy hW
  haveI : IsCommMonObj A := hA.comm
  unfold Out.WeilIs
  intro p
  obtain ⟨i, hi⟩ := GlobalTheory.CoverGlue.exists_mem hU p
  obtain ⟨j, hj⟩ : ∃ j : Over.mk ((Out.baseOver (U i).toScheme).hom ≫ (U i).ι) ⟶ Out.baseOver S,
      j.left = (U i).ι := ⟨Over.homMk (U i).ι (by simp [Out.baseOver]), rfl⟩
  haveI : IsOpenImmersion j.left := by
    rw [hj]
    infer_instance
  have hx₀ : (j ≫ x).left = (x' i).left ≫ ψ i := by rw [Over.comp_left, hj, hx i]
  have hy₀ : (j ≫ y).left = (y' i).left ≫ ψ i := by rw [Over.comp_left, hj, hy i]
  have H₀ := (GlobalTheory.weilIs_iff_of_isGrpPullback_comm S (U i).toScheme A (G i) (U i).ι (ψ i) L (M i) hL (hM i)
    (hψ i) (hML i) (Out.baseOver (U i).toScheme) k (x' i) (y' i) (j ≫ x) (j ≫ y)
    (Units.map (U i).ι.appTop.hom.toMonoidHom c) hx₀ hy₀).1 (hW i)
  have H₁ : Out.WeilIs A L k (j ≫ x) (j ≫ y) (Units.map j.left.appTop.hom.toMonoidHom c) := by
    rw [hj]
    exact H₀
  obtain ⟨V, hV, hl, hc⟩ := GlobalTheory.WeilLocal.local_of_openImmersion hL j H₁ ⟨p, hi⟩
  refine ⟨V, ?_, hl, hc⟩
  rw [hj] at hV
  exact hV
