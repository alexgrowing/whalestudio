import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SRelOneOneIff
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatOverArtinFibreProductIsPushoutStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalSiegelObjectOddLevelRigid
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitsOfPullEqZero
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelPullbackIdCompCancel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelPrePullbackPrincipalRingChange
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsSchemeTheoreticallyDominantSpecOfInjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullbackPowersCartesianGroupSquare
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMonHomOfBaseChangesArtinFibreProductStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueUnitsGlueArtinFibreProductStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeUnitsLiftArtinPinchStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

namespace GlobalTheory.SiegPinch

theorem glue_hom : ∀ (P R₁ R₂ R₀ : CommRingCat.{0}) (f₁ : P ⟶ R₁) (f₂ : P ⟶ R₂) (g₁ : R₁ ⟶ R₀) (g₂ : R₂ ⟶ R₀), IsPullback f₁ f₂ g₁ g₂ → IsLocalRing P → IsArtinianRing P → Function.Surjective g₁ → Function.Surjective g₂ → ∀ (Y Z : Over (Spec P)) (Y₁ : Over (Spec R₁)) (Y₂ : Over (Spec R₂)) (Y₀ : Over (Spec R₀)) (j₁ : Y₁.left ⟶ Y.left) (j₂ : Y₂.left ⟶ Y.left) (k₁ : Y₁.left ⟶ Z.left) (k₂ : Y₂.left ⟶ Z.left) (i₁ : Y₀.left ⟶ Y₁.left) (i₂ : Y₀.left ⟶ Y₂.left), Flat Y.hom → Flat Z.hom → IsPullback j₁ Y₁.hom Y.hom (Spec.map f₁) → IsPullback j₂ Y₂.hom Y.hom (Spec.map f₂) → IsPullback k₁ Y₁.hom Z.hom (Spec.map f₁) → IsPullback k₂ Y₂.hom Z.hom (Spec.map f₂) → IsPullback i₁ Y₀.hom Y₁.hom (Spec.map g₁) → i₂ ≫ Y₂.hom = Y₀.hom ≫ Spec.map g₂ → i₁ ≫ j₁ = i₂ ≫ j₂ → i₁ ≫ k₁ = i₂ ≫ k₂ → ∃ φ : Y.left ⟶ Z.left, IsPullback φ Y.hom Z.hom (𝟙 _) ∧ j₁ ≫ φ = k₁ ∧ j₂ ≫ φ = k₂ := by
  intro P R₁ R₂ R₀ f₁ f₂ g₁ g₂ hpb hloc hart hs₁ hs₂ Y Z Y₁ Y₂ Y₀ j₁ j₂ k₁ k₂ i₁ i₂ hY hZ pj₁ pj₂ pk₁ pk₂ pi₁ w₂ ej ek
  have poY := GlobalTheory.T.flat_over_artinFibreProduct_isPushout P R₁ R₂ R₀ f₁ f₂ g₁ g₂ hpb hloc hart hs₁ hs₂ Y Y₁ Y₂ Y₀ j₁ j₂ i₁ i₂ hY pj₁ pj₂ pi₁ ej w₂
  have poZ := GlobalTheory.T.flat_over_artinFibreProduct_isPushout P R₁ R₂ R₀ f₁ f₂ g₁ g₂ hpb hloc hart hs₁ hs₂ Z Y₁ Y₂ Y₀ k₁ k₂ i₁ i₂ hZ pk₁ pk₂ pi₁ ek w₂
  let φ : Y.left ⟶ Z.left := poY.desc k₁ k₂ ek
  let ψ : Z.left ⟶ Y.left := poZ.desc j₁ j₂ ej
  have h₁ : φ ≫ ψ = 𝟙 _ := poY.hom_ext
    (by rw [← Category.assoc, poY.inl_desc, poZ.inl_desc, Category.comp_id])
    (by rw [← Category.assoc, poY.inr_desc, poZ.inr_desc, Category.comp_id])
  have h₂ : ψ ≫ φ = 𝟙 _ := poZ.hom_ext
    (by rw [← Category.assoc, poZ.inl_desc, poY.inl_desc, Category.comp_id])
    (by rw [← Category.assoc, poZ.inr_desc, poY.inr_desc, Category.comp_id])
  have hw : φ ≫ Z.hom = Y.hom ≫ 𝟙 _ := poY.hom_ext
    (by rw [Category.comp_id, ← Category.assoc, poY.inl_desc, pk₁.w, pj₁.w])
    (by rw [Category.comp_id, ← Category.assoc, poY.inr_desc, pk₂.w, pj₂.w])
  haveI : IsIso φ := ⟨ψ, h₁, h₂⟩
  exact ⟨φ, IsPullback.of_horiz_isIso ⟨hw⟩, poY.inl_desc _ _ _, poY.inr_desc _ _ _⟩

section Tools

variable {h n : ℕ} {B B' B'' : Type} [CommRing B] [CommRing B'] [CommRing B''] {ζ : B} {ζ' : B'} {ζ'' : B''}
  {S S' S'' : Scheme.{0}} {s : S ⟶ Sp B} {s' : S' ⟶ Sp B'} {s'' : S'' ⟶ Sp B''}

theorem srelBy_comp {c : SiegPre h n ζ s} {c' : SiegPre h n ζ' s'} {c'' : SiegPre h n ζ'' s''} {f : S' ⟶ S}
    {f' : S'' ⟶ S'} {φ : c'.A.left ⟶ c.A.left} {ψ : c''.A.left ⟶ c'.A.left}
    (m : SRelBy c' c 1 1 f φ) (m' : SRelBy c'' c' 1 1 f' ψ) : SRelBy c'' c 1 1 (f' ≫ f) (ψ ≫ φ) := by
  obtain ⟨hφ, ⟨φ₂, hs, hw⟩, hl⟩ := m
  obtain ⟨hψ, ⟨ψ₂, hs', hw'⟩, hl'⟩ := m'
  simp only [pow_one] at hl hl' ⊢
  refine ⟨hψ.comp hφ, ⟨ψ₂ ≫ φ₂, ⟨?_, ?_⟩, ?_⟩, fun a => ?_⟩
  · rw [Category.assoc, hs.1, ← Category.assoc, hs'.1, Category.assoc]
  · rw [Category.assoc, hs.2, ← Category.assoc, hs'.2, Category.assoc]
  · exact (hw'.trans c''.isLB (pull_isLB c'.isLB _) (pull_isLB (pull_isLB c.isLB _) _)
      (GlobalTheory.SiegelPullComp.iso_pull ψ₂ hw)).trans
      c''.isLB (pull_isLB (pull_isLB c.isLB _) _) (pull_isLB c.isLB _) (GlobalTheory.SiegelPullComp.iso_pull_pull c.isLB φ₂ ψ₂)
  · simp only [pow_one]
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ φ) (hl' a)).trans ((Category.assoc _ _ _).trans
      ((congrArg (f' ≫ ·) (hl a)).trans (Category.assoc _ _ _).symm)))

theorem sq_ext {S : Scheme.{0}} (A : Over S) {X : Scheme.{0}} {a b : X ⟶ (G2 A).left}
    (h₁ : a ≫ (fst A A).left = b ≫ (fst A A).left) (h₂ : a ≫ (snd A A).left = b ≫ (snd A A).left) : a = b :=
  pullback.hom_ext h₁ h₂

theorem isPullback_sq {G : Over S} {G' : Over S'} {f : S' ⟶ S} {β : G'.left ⟶ G.left}
    (hp : IsPullback β G'.hom G.hom f) {β₂ : (G2 G').left ⟶ (G2 G).left} (hs : IsSquare β β₂) :
    IsPullback β₂ (G2 G').hom (G2 G).hom f := by
  have e : β₂ = (lift (pushPt hp.w (fst G' G')) (pushPt hp.w (snd G' G'))).left := by
    apply sq_ext
    · rw [hs.1]; exact (congrArg (fun q => q.left) (lift_fst (pushPt hp.w (fst G' G')) (pushPt hp.w (snd G' G')))).symm
    · rw [hs.2]; exact (congrArg (fun q => q.left) (lift_snd (pushPt hp.w (fst G' G')) (pushPt hp.w (snd G' G')))).symm
  rw [e]
  exact GlobalTheory.Mum.PowCart.isPullback_two hp

theorem sq_comp {G : Over S} {G' : Over S'} {G'' : Over S''} {β : G'.left ⟶ G.left} {β' : G''.left ⟶ G'.left}
    {β₂ : (G2 G').left ⟶ (G2 G).left} {β₂' : (G2 G'').left ⟶ (G2 G').left} (hs : IsSquare β β₂) (hs' : IsSquare β' β₂') :
    IsSquare (β' ≫ β) (β₂' ≫ β₂) :=
  ⟨by rw [Category.assoc, hs.1, ← Category.assoc, hs'.1, Category.assoc],
   by rw [Category.assoc, hs.2, ← Category.assoc, hs'.2, Category.assoc]⟩

theorem sq_unique {G : Over S} {G' : Over S'} {β : G'.left ⟶ G.left} {β₂ β₂' : (G2 G').left ⟶ (G2 G).left}
    (hs : IsSquare β β₂) (hs' : IsSquare β β₂') : β₂ = β₂' :=
  sq_ext G (hs.1.trans hs'.1.symm) (hs.2.trans hs'.2.symm)

end Tools

theorem siegPB_of_pinch : ∀ (g n : ℕ), 3 ≤ n → Odd n → ∀ (P R₁ R₂ R₀ : CommRingCat.{0}) (f₁ : P ⟶ R₁) (f₂ : P ⟶ R₂) (g₁ : R₁ ⟶ R₀) (g₂ : R₂ ⟶ R₀), IsPullback f₁ f₂ g₁ g₂ → IsLocalRing P → IsArtinianRing P → Function.Surjective g₁ → Function.Surjective g₂ → ∀ (β : CommRingCat.of (cycAway n) ⟶ P) (c c' : SiegPre g n (zetaAway n) (Spec.map β)) (c₁ : SiegPre g n (zetaAway n) (Spec.map f₁ ≫ Spec.map β)) (c₂ : SiegPre g n (zetaAway n) (Spec.map f₂ ≫ Spec.map β)), c.Principal → c'.Principal → SiegPB c₁ c (Spec.map f₁) → SiegPB c₁ c' (Spec.map f₁) → SiegPB c₂ c (Spec.map f₂) → SiegPB c₂ c' (Spec.map f₂) → SiegPB c' c (𝟙 _) := by
  intro g n hn hodd P R₁ R₂ R₀ f₁ f₂ g₁ g₂ hpb hloc hart hs₁ hs₂ β c c' c₁ c₂ hc hc' m₁ m₁' m₂ m₂'
  have hn0 : n ≠ 0 := by omega
  have hbase : Spec.map g₁ ≫ Spec.map f₁ = Spec.map g₂ ≫ Spec.map f₂ := by
    rw [← Spec.map_comp, ← Spec.map_comp, hpb.w]
  obtain ⟨c₀, m₀⟩ := (GlobalTheory.SiegelRingChange.siegPre_pull_ringChange g n (cycAway n) (cycAway n) (zetaAway n)
    (zetaAway n) (RingHom.id _) (Spec R₁) (Spec R₀) (Spec.map f₁ ≫ Spec.map β)
    (Spec.map g₁ ≫ Spec.map f₁ ≫ Spec.map β) (Spec.map g₁) rfl (by simp [spMap])).1 c₁
  have m₀₂ : SiegPB c₀ c₂ (Spec.map g₂) := by
    have := GlobalTheory.SiegelPullComp.pb_comp m₁' m₀
    rw [hbase] at this
    exact GlobalTheory.SiegelPullComp.pb_cancel m₂' this
  obtain ⟨ρ₁, r₁⟩ := (sRel_one_one_iff _ _ _).2 m₀
  obtain ⟨ρ₂, r₂⟩ := (sRel_one_one_iff _ _ _).2 m₀₂
  obtain ⟨ψ₁, q₁⟩ := (sRel_one_one_iff _ _ _).2 m₁
  obtain ⟨ψ₁', q₁'⟩ := (sRel_one_one_iff _ _ _).2 m₁'
  obtain ⟨ψ₂, q₂⟩ := (sRel_one_one_iff _ _ _).2 m₂
  obtain ⟨ψ₂', q₂'⟩ := (sRel_one_one_iff _ _ _).2 m₂'
  have e' : ρ₁ ≫ ψ₁' = ρ₂ ≫ ψ₂' :=
    GlobalTheory.SiegRigid.eq_of_sRelBy g n n 1 (cycAway n) (cycAway n) (cycBase hn0) (zetaAway n) _ _ _ _ c' c₀ _ _ _
      hn hodd hc' (srelBy_comp q₁' r₁) (by rw [hbase]; exact srelBy_comp q₂' r₂)
  have e : ρ₁ ≫ ψ₁ = ρ₂ ≫ ψ₂ :=
    GlobalTheory.SiegRigid.eq_of_sRelBy g n n 1 (cycAway n) (cycAway n) (cycBase hn0) (zetaAway n) _ _ _ _ c c₀ _ _ _
      hn hodd hc (srelBy_comp q₁ r₁) (by rw [hbase]; exact srelBy_comp q₂ r₂)
  have hfl : Flat c.A.hom := by have := c.ab.smooth; infer_instance
  have hfl' : Flat c'.A.hom := by have := c'.ab.smooth; infer_instance
  obtain ⟨φ, hφp, hφ₁, hφ₂⟩ := glue_hom P R₁ R₂ R₀ f₁ f₂ g₁ g₂ hpb hloc hart hs₁ hs₂ c'.A c.A c₁.A c₂.A c₀.A ψ₁' ψ₂' ψ₁ ψ₂
    ρ₁ ρ₂ hfl' hfl q₁'.1.1 q₂'.1.1 q₁.1.1 q₂.1.1 r₁.1.1 r₂.1.1.w e' e
  have hφ : IsGrpPullback c'.A c.A (𝟙 _) φ := GlobalTheory.T.isGrpPullback_id_of_baseChanges_artinFibreProduct P R₁ R₂ R₀ f₁ f₂ g₁ g₂ hpb hloc hart hs₁ hs₂ c'.A c.A c₁.A c₂.A c₀.A
    ψ₁' ψ₂' ψ₁ ψ₂ ρ₁ ρ₂ φ hfl' q₁'.1 q₂'.1 q₁.1 q₂.1 r₁.1 r₂.1 e' hφp hφ₁ hφ₂
  let φ₂ : (G2 c'.A).left ⟶ (G2 c.A).left := (lift (pushPt hφ.1.w (fst c'.A c'.A)) (pushPt hφ.1.w (snd c'.A c'.A))).left
  have sq : IsSquare φ φ₂ := ⟨congrArg (fun q => q.left) (lift_fst (pushPt hφ.1.w (fst c'.A c'.A)) (pushPt hφ.1.w (snd c'.A c'.A))),
    congrArg (fun q => q.left) (lift_snd (pushPt hφ.1.w (fst c'.A c'.A)) (pushPt hφ.1.w (snd c'.A c'.A)))⟩
  refine ⟨φ, φ₂, hφ, sq, ?_, fun a => ?_⟩
  · obtain ⟨χ₁', sχ₁', wχ₁'⟩ := q₁'.2.1
    obtain ⟨χ₁, sχ₁, wχ₁⟩ := q₁.2.1
    obtain ⟨χ₂', sχ₂', wχ₂'⟩ := q₂'.2.1
    obtain ⟨χ₂, sχ₂, wχ₂⟩ := q₂.2.1
    obtain ⟨τ₁, sτ₁, -⟩ := r₁.2.1
    obtain ⟨τ₂, sτ₂, -⟩ := r₂.2.1
    have eτ : τ₁ ≫ χ₁' = τ₂ ≫ χ₂' := by
      have h1 := sq_comp sχ₁' sτ₁
      have h2 := sq_comp sχ₂' sτ₂
      rw [e'] at h1
      exact sq_unique h1 h2
    have eχ₁ : χ₁' ≫ φ₂ = χ₁ := by
      have h1 := sq_comp sq sχ₁'
      rw [hφ₁] at h1
      exact sq_unique h1 sχ₁
    have pχ₁' := isPullback_sq q₁'.1.1 sχ₁'
    have pχ₂' := isPullback_sq q₂'.1.1 sχ₂'
    have pτ₁ := isPullback_sq r₁.1.1 sτ₁
    have pτ₂ := isPullback_sq r₂.1.1 sτ₂
    have hflat2 : Flat (G2 c'.A).hom := by
      have := hfl'
      exact GlobalTheory.ExtUnique.flat_tensorObj c'.A c'.A
    obtain ⟨hpatch, huniq⟩ := GlobalTheory.T.existsUnique_units_glue_artinFibreProduct P R₁ R₂ R₀ f₁ f₂ g₁ g₂ hpb hloc hart hs₁ hs₂ (G2 c'.A) (G2 c₁.A) (G2 c₂.A) (G2 c₀.A)
      χ₁' χ₂' τ₁ τ₂ hflat2 pχ₁' pχ₂' pτ₁ eτ pτ₂.w
    have hab₀ : IsAbelianScheme (G2 c₀.A) := AbelianSchemeGerms.isAbelianScheme_tensor _ _ c₀.ab c₀.ab
    have hlift := GlobalTheory.T.abelianScheme_units_lift_artinPinch P R₁ R₂ R₀ f₁ f₂ g₁ g₂ hpb hloc hart hs₁ hs₂ (G2 c₀.A) hab₀ (G2 c₁.A).left (G2 c₁.A).hom τ₁ pτ₁.w
    have hL' := c'.isLB
    have hM : (c.P.pull φ₂).IsLB := pull_isLB c.isLB φ₂
    have key := GlobalTheory.SmallGlue.cech_patching χ₁' χ₂' τ₁ τ₂ eτ hlift hpatch huniq
      (GlobalTheory.CechPic.cls c'.P hL' - GlobalTheory.CechPic.cls _ hM) ?_ ?_
    · exact (GlobalTheory.CechPic.cls_eq_iff hL' hM).1 (sub_eq_zero.1 key)
    · rw [map_sub, ← GlobalTheory.CechPic.cls_pull hL' χ₁' (pull_isLB hL' _), ← GlobalTheory.CechPic.cls_pull hM χ₁' (pull_isLB hM _),
        sub_eq_zero, GlobalTheory.CechPic.cls_eq_iff]
      refine LBIso.trans (pull_isLB hL' _) c₁.isLB (pull_isLB hM _) wχ₁'.symm ?_
      refine LBIso.trans c₁.isLB (pull_isLB c.isLB _) (pull_isLB hM _) wχ₁ ?_
      rw [← eχ₁]
      exact (GlobalTheory.SiegelPullComp.iso_pull_pull c.isLB φ₂ χ₁').symm
    · have eχ₂ : χ₂' ≫ φ₂ = χ₂ := by
        have h1 := sq_comp sq sχ₂'
        rw [hφ₂] at h1
        exact sq_unique h1 sχ₂
      rw [map_sub, ← GlobalTheory.CechPic.cls_pull hL' χ₂' (pull_isLB hL' _), ← GlobalTheory.CechPic.cls_pull hM χ₂' (pull_isLB hM _),
        sub_eq_zero, GlobalTheory.CechPic.cls_eq_iff]
      refine LBIso.trans (pull_isLB hL' _) c₂.isLB (pull_isLB hM _) wχ₂'.symm ?_
      refine LBIso.trans c₂.isLB (pull_isLB c.isLB _) (pull_isLB hM _) wχ₂ ?_
      rw [← eχ₂]
      exact (GlobalTheory.SiegelPullComp.iso_pull_pull c.isLB φ₂ χ₂').symm
  · have hpo := GlobalTheory.T.flat_over_artinFibreProduct_isPushout P R₁ R₂ R₀ f₁ f₂ g₁ g₂ hpb hloc hart hs₁ hs₂ (Over.mk (𝟙 _)) (Over.mk (𝟙 _))
      (Over.mk (𝟙 _)) (Over.mk (𝟙 _)) (Spec.map f₁) (Spec.map f₂) (Spec.map g₁) (Spec.map g₂)
      (by dsimp; infer_instance) (IsPullback.id_vert _) (IsPullback.id_vert _) (IsPullback.id_vert _) hbase (by simp)
    rw [Category.id_comp]
    have a₁ := q₁'.2.2 a
    have a₂ := q₁.2.2 a
    have a₃ := q₂'.2.2 a
    have a₄ := q₂.2.2 a
    simp only [pow_one] at a₁ a₂ a₃ a₄
    apply hpo.hom_ext
    · rw [← Category.assoc, ← a₁, Category.assoc, hφ₁, a₂]
    · rw [← Category.assoc, ← a₃, Category.assoc, hφ₂, a₄]

end GlobalTheory.SiegPinch
