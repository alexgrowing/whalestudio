import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.GalOfKer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorInverseHeckeTranslatesForgetLevel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackProdInjectiveBirigidifiedGaloisIsogenyStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo
open UpperTheory.Gal.G3 (sp)
open GlobalTheory.UPel.HT.HeckeAd (IsTranslA heckeSubA)
open scoped TensorProduct
open UpperTheory.Gal.FiniteEtaleModels
open GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.Hecke.Comp

theorem UpperTheory.Gal.FiniteEtaleModels.trSame_holds :
    TrSame := by
  intro q _ D R _ b f c k N S s o o₁ o₂ ψ₁ ψ₂ h₁ h₂
  obtain ⟨m₁, a₁, e₁, g₁, l₁, -⟩ := h₁
  obtain ⟨m₂, a₂, e₂, g₂, l₂, -⟩ := h₂
  have ep₁ := GlobalTheory.GaloisCartDesc.epi_of_isGaloisCover g₁
  have ep₂ := GlobalTheory.GaloisCartDesc.epi_of_isGaloisCover g₂
  have kill : ∀ {X : Over S} [GrpObj X] (ψ : o.A ⟶ X), IsMonHom ψ →
      GlobalTheory.ZM.IsGaloisCover (↥(heckeSubA o f N)) (fun h ↦ Over.Hom.left (transl h.1)) (Over.Hom.left ψ) →
      ∀ h ∈ heckeSubA o f N, h ≫ ψ = 1 := by
    intro X _ ψ hψ g h hh
    exact comp_eq_one_of_transl ψ h (g.inv ⟨h, hh⟩)
  obtain ⟨φ, hφ, hφc⟩ := GlobalTheory.HomDescent.exists_desc S o.A o₁.A o₂.A _ ψ₁ m₁ g₁ ψ₂ m₂ (kill ψ₂ m₂ g₂)
  obtain ⟨φ', hφ', hφ'c⟩ := GlobalTheory.HomDescent.exists_desc S o.A o₂.A o₁.A _ ψ₂ m₂ g₂ ψ₁ m₁ (kill ψ₁ m₁ g₁)
  have canc : ∀ {X Y : Over S} (π : X ⟶ Y) [Epi π.left] {Z : Over S} (u v : Y ⟶ Z), π ≫ u = π ≫ v → u = v := by
    intro X Y π _ Z u v h
    ext1
    rw [← cancel_epi π.left, ← Over.comp_left, h, Over.comp_left]
  let e : o₁.A ≅ o₂.A :=
    { hom := φ, inv := φ',
      hom_inv_id := canc ψ₁ _ _ (by rw [reassoc_of% hφc, hφ'c, Category.comp_id])
      inv_hom_id := canc ψ₂ _ _ (by rw [reassoc_of% hφ'c, hφc, Category.comp_id]) }
  haveI : IsMonHom e.hom := hφ
  haveI : IsMonHom ψ₁ := m₁
  haveI : IsMonHom ψ₂ := m₂
  have hc : ψ₁.left ≫ φ.left = ψ₂.left := by rw [← Over.comp_left, hφc]
  refine ⟨⟨φ.left, sq2 φ, isGrpPullback_of_iso e, ⟨grpSchemeSquareProductMap_fst φ, grpSchemeSquareProductMap_snd φ⟩, ?_, ?_, ?_⟩, hc⟩
  · intro a
    have t₁ := congrArg Over.Hom.left (a₁ a)
    have t₂ := congrArg Over.Hom.left (a₂ a)
    simp only [Over.comp_left] at t₁ t₂
    rw [← cancel_epi ψ₁.left, ← Category.assoc, ← t₁, Category.assoc, hc, reassoc_of% hc, ← t₂]
  · have hP := o₂.isLB
    have Z : ∀ (u : o₁.A.left ⟶ (G2 o₁.A).left) (v : o₂.A.left ⟶ (G2 o₂.A).left),
        u ≫ sq2 φ = φ.left ≫ v → (∃ t : (o₂.P.pull v).Gen, t.IsGen) →
        ∃ t : ((o₂.P.pull (sq2 φ)).pull u).Gen, t.IsGen := by
      intro u v huv hv
      rw [← GlobalTheory.CechPic.cls_eq_zero_iff (pull_isLB (pull_isLB hP _) _),
        GlobalTheory.CechPic.cls_pull (pull_isLB hP _), GlobalTheory.CechPic.cls_pull hP, ← GlobalTheory.CechPic.pull_comp, huv,
        GlobalTheory.CechPic.pull_comp, ← GlobalTheory.CechPic.cls_pull hP v (pull_isLB hP v),
        (GlobalTheory.CechPic.cls_eq_zero_iff _).2 hv, map_zero]
    obtain ⟨l₁⟩ := l₁
    obtain ⟨l₂⟩ := l₂
    have lA := ReciprocityTheory.ChartRestriction.G.Semi.LB.isLB_linComb o.isLB (fun _ : Fin (k ^ 2 / c) ↦ 𝟙 _) (fun _ ↦ (1 : ℤ))
    have Y : LBIso (o₂.P.pull (sq2 ψ₂)) ((o₂.P.pull (sq2 φ)).pull (sq2 ψ₁)) := by
      rw [← GlobalTheory.CechPic.cls_eq_iff (pull_isLB hP _) (pull_isLB (pull_isLB hP _) _),
        GlobalTheory.CechPic.cls_pull hP, GlobalTheory.CechPic.cls_pull (pull_isLB hP _), GlobalTheory.CechPic.cls_pull hP,
        ← GlobalTheory.CechPic.pull_comp, ← grpSchemeSquareProductMap_comp, hφc]
    refine GlobalTheory.T.pullback_prod_injective_birigidified_galois_isogeny S o.A o₁.A _ ψ₁ o.ab o₁.ab m₁ g₁ o₁.P (o₂.P.pull (sq2 φ)) o₁.isLB
      (pull_isLB o₂.isLB _) o₁.rig₁ o₁.rig₂ ?_ ?_ ?_
    · exact Z _ _ (lift_one_id_grpSchemeSquareProductMap φ) o₂.rig₁
    · exact Z _ _ (lift_id_one_grpSchemeSquareProductMap φ) o₂.rig₂
    · exact LBIso.trans (pull_isLB o₁.isLB _) lA (pull_isLB (pull_isLB hP _) _) (LBIso.symm l₁)
        (LBIso.trans lA (pull_isLB hP _) (pull_isLB (pull_isLB hP _) _) l₂ Y)
  · intro y
    rw [e₁ y, e₂ y, Over.comp_left, Over.comp_left, Category.assoc, hc, Category.id_comp]
