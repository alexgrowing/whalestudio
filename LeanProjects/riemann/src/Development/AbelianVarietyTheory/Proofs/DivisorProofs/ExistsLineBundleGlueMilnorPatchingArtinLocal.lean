import Development.AbelianVarietyTheory.Definitions.Divisors.SRelOneOneIff
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPicPatch
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WhiskerLeftIsPullbackAffineClosed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackSquareSectionsGlueOfBasis
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.ArtinPatch

theorem elem_of_isPullback {A B C D : CommRingCat.{0}} {f : A ⟶ B} {g : A ⟶ C} {h : B ⟶ D} {i : C ⟶ D}
    (H : IsPullback f g h i) :
    (∀ x y, f.hom x = f.hom y → g.hom x = g.hom y → x = y) ∧
      ∀ b c, h.hom b = i.hom c → ∃ a, f.hom a = b ∧ g.hom a = c := by
  have H' := (Types.isPullback_iff _ _ _ _).1 (H.map (forget CommRingCat))
  exact ⟨fun x y hx hy ↦ H'.2.1 x y ⟨hx, hy⟩, fun b c hbc ↦ H'.2.2 b c hbc⟩

theorem isPushout_of_isPullback {P R₁ R₂ R₀ : CommRingCat.{0}} {f₁ : P ⟶ R₁} {f₂ : P ⟶ R₂} {g₁ : R₁ ⟶ R₀}
    {g₂ : R₂ ⟶ R₀} (H : IsPullback f₁ f₂ g₁ g₂) (hg₁ : Function.Surjective g₁.hom) :
    IsPushout f₁ f₂ g₁ g₂ := by
  obtain ⟨-, hex⟩ := elem_of_isPullback H
  have key : ∀ s : PushoutCocone f₁ f₂, RingHom.ker g₁.hom ≤ RingHom.ker s.inl.hom := by
    intro s r hr
    rw [RingHom.mem_ker] at hr ⊢
    obtain ⟨a, ha1, ha2⟩ := hex r 0 (by rw [hr, map_zero])
    have e := congrArg (fun φ => φ.hom a) s.condition
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e
    rw [← ha1, e, ha2, map_zero]
  let d : ∀ s : PushoutCocone f₁ f₂, R₀ ⟶ s.pt := fun s =>
    CommRingCat.ofHom (RingHom.liftOfRightInverse g₁.hom (Function.surjInv hg₁)
      (Function.rightInverse_surjInv hg₁) ⟨s.inl.hom, key s⟩)
  have hd : ∀ (s : PushoutCocone f₁ f₂) (r : R₁), (d s).hom (g₁.hom r) = s.inl.hom r := fun s r => by
    simp only [d, CommRingCat.hom_ofHom]
    exact RingHom.liftOfRightInverse_comp_apply _ _ _ _ r
  refine IsPushout.of_isColimit (c := PushoutCocone.mk g₁ g₂ H.w) ?_
  refine PushoutCocone.IsColimit.mk _ d ?_ ?_ ?_
  · intro s
    ext r
    exact hd s r
  · intro s
    ext r₂
    obtain ⟨r₁, hr₁⟩ := hg₁ (g₂.hom r₂)
    obtain ⟨a, ha1, ha2⟩ := hex r₁ r₂ hr₁
    have e := congrArg (fun φ => φ.hom a) s.condition
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e
    change (d s).hom (g₂.hom r₂) = s.inr.hom r₂
    rw [← hr₁, hd, ← ha1, e, ha2]
  · intro s m h1 _
    ext y
    obtain ⟨r, rfl⟩ := hg₁ y
    have e := congrArg (fun φ => φ.hom r) h1
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e
    change m.hom (g₁.hom r) = (d s).hom (g₁.hom r)
    rw [hd]
    exact e

theorem spec_eq_of_artinian (P : CommRingCat.{0}) [IsLocalRing P] [IsArtinianRing P] (x y : Spec P) :
    x = y := by
  have h : ∀ z : PrimeSpectrum P, z.asIdeal = IsLocalRing.maximalIdeal P := fun z =>
    IsLocalRing.eq_maximalIdeal (IsArtinianRing.isMaximal_of_isPrime z.asIdeal)
  exact PrimeSpectrum.ext ((h x).trans (h y).symm)

end GlobalTheory.ArtinPatch

namespace GlobalTheory.ArtinPatch

theorem glues_spec {P R₁ R₂ R₀ : CommRingCat.{0}} {f₁ : P ⟶ R₁} {f₂ : P ⟶ R₂} {g₁ : R₁ ⟶ R₀} {g₂ : R₂ ⟶ R₀}
    (H : IsPullback f₁ f₂ g₁ g₂) (hP : ∀ x y : Spec P, x = y) :
    GlobalTheory.PinchLift.Glues (Spec.map f₂) (Spec.map f₁) (Spec.map g₂) (Spec.map g₁) := by
  obtain ⟨hinj, hex⟩ := elem_of_isPullback H
  have inj : ∀ {R : CommRingCat.{0}} (u v : Γ(Spec R, ⊤)),
      (Scheme.ΓSpecIso R).hom.hom u = (Scheme.ΓSpecIso R).hom.hom v → u = v := by
    intro R u v h
    simpa using congrArg (Scheme.ΓSpecIso R).inv.hom h
  have nat : ∀ {R S : CommRingCat.{0}} (f : R ⟶ S) (u : Γ(Spec R, ⊤)),
      (Scheme.ΓSpecIso S).hom.hom ((Spec.map f).appTop.hom u) = f.hom ((Scheme.ΓSpecIso R).hom.hom u) := by
    intro R S f u
    exact congrArg (fun φ => φ.hom u) (Scheme.ΓSpecIso_naturality f)
  refine GlobalTheory.PinchLift.glues_of_basis _ _ _ _ {⊤} ?_ ?_
  · intro W x hx
    refine ⟨⊤, rfl, trivial, fun y _ => ?_⟩
    rw [hP y x]
    exact hx
  · rintro W rfl a b hab
    set V := Spec.map g₂ ⁻¹ᵁ Spec.map f₂ ⁻¹ᵁ (⊤ : (Spec P).Opens) ⊓
      Spec.map g₁ ⁻¹ᵁ Spec.map f₁ ⁻¹ᵁ (⊤ : (Spec P).Opens) with hVdef
    have hV : V = ⊤ := top_le_iff.1 (fun x _ => ⟨trivial, trivial⟩)
    have hiso : IsIso (homOfLE (le_top : V ≤ ⊤)) := by
      rw [show homOfLE (le_top : V ≤ ⊤) = (eqToIso hV).hom from Subsingleton.elim _ _]
      infer_instance
    set ρ := (Spec R₀).presheaf.map (homOfLE (le_top : V ≤ ⊤)).op
    have hρ : ∀ u v, ρ.hom u = ρ.hom v → u = v := by
      intro u v h
      simpa using congrArg (inv ρ).hom h
    have e : (Spec.map g₂).appTop.hom a = (Spec.map g₁).appTop.hom b := by
      apply hρ
      exact hab
    have key : g₁.hom ((Scheme.ΓSpecIso R₁).hom.hom b) = g₂.hom ((Scheme.ΓSpecIso R₂).hom.hom a) := by
      rw [← nat g₁ b, ← nat g₂ a, e]
    obtain ⟨x, hx1, hx2⟩ := hex _ _ key
    refine ⟨(Scheme.ΓSpecIso P).inv.hom x, ⟨?_, ?_⟩, ?_⟩
    · apply inj
      change (Scheme.ΓSpecIso R₂).hom.hom ((Spec.map f₂).appTop.hom _) = _
      rw [nat]
      simpa using hx2
    · apply inj
      change (Scheme.ΓSpecIso R₁).hom.hom ((Spec.map f₁).appTop.hom _) = _
      rw [nat]
      simpa using hx1
    · rintro s ⟨hs2, hs1⟩
      apply inj
      simp only [Iso.inv_hom_id_apply]
      apply hinj
      · rw [← nat]
        change (Scheme.ΓSpecIso R₁).hom.hom (((Spec.map f₁).app ⊤).hom s) = _
        rw [hs1, hx1]
      · rw [← nat]
        change (Scheme.ΓSpecIso R₂).hom.hom (((Spec.map f₂).app ⊤).hom s) = _
        rw [hs2, hx2]

end GlobalTheory.ArtinPatch

namespace GlobalTheory.ArtinPatch

theorem exists_lb_glue : ∀ (P R₁ R₂ R₀ : CommRingCat.{0}) (f₁ : P ⟶ R₁) (f₂ : P ⟶ R₂) (g₁ : R₁ ⟶ R₀) (g₂ : R₂ ⟶ R₀), IsPullback f₁ f₂ g₁ g₂ → IsLocalRing P → IsArtinianRing P → Function.Surjective g₁ → Function.Surjective g₂ → ∀ (X : Over (Spec P)) (X₁ : Over (Spec R₁)) (X₂ : Over (Spec R₂)) (X₀ : Over (Spec R₀)) (j₁ : X₁.left ⟶ X.left) (j₂ : X₂.left ⟶ X.left) (i₁ : X₀.left ⟶ X₁.left) (i₂ : X₀.left ⟶ X₂.left), Flat X.hom → IsPullback j₁ X₁.hom X.hom (Spec.map f₁) → IsPullback j₂ X₂.hom X.hom (Spec.map f₂) → IsPullback i₁ X₀.hom X₁.hom (Spec.map g₁) → i₁ ≫ j₁ = i₂ ≫ j₂ → i₂ ≫ X₂.hom = X₀.hom ≫ Spec.map g₂ → ∀ (L₁ : LB X₁.left) (L₂ : LB X₂.left), L₁.IsLB → L₂.IsLB → LBIso (L₁.pull i₁) (L₂.pull i₂) → ∃ L : LB X.left, L.IsLB ∧ LBIso L₁ (L.pull j₁) ∧ LBIso L₂ (L.pull j₂) := by
  intro P R₁ R₂ R₀ f₁ f₂ g₁ g₂ hpb hloc hart hg₁ hg₂ X X₁ X₂ X₀ j₁ j₂ i₁ i₂ hflat h₁ h₂ h₀ hc hc₂ L₁ L₂ hL₁ hL₂ hiso
  haveI := hloc
  haveI := hart
  obtain ⟨-, hex⟩ := elem_of_isPullback hpb
  have hf₁ : Function.Surjective f₁.hom := fun r => by
    obtain ⟨r₂, hr₂⟩ := hg₂ (g₁.hom r)
    obtain ⟨a, ha, -⟩ := hex r r₂ hr₂.symm
    exact ⟨a, ha⟩
  have hw : Spec.map g₂ ≫ Spec.map f₂ = Spec.map g₁ ≫ Spec.map f₁ := by
    rw [← Spec.map_comp, ← Spec.map_comp, hpb.w]

  let O : Over (Spec P) := Over.mk (𝟙 (Spec P))
  let O₂ : Over (Spec P) := Over.mk (Spec.map f₂)
  let O₁ : Over (Spec P) := Over.mk (Spec.map f₁)
  let O₀ : Over (Spec P) := Over.mk (Spec.map g₁ ≫ Spec.map f₁)
  let q : O₂ ⟶ O := Over.homMk (Spec.map f₂) (Category.comp_id _)
  let r : O₁ ⟶ O := Over.homMk (Spec.map f₁) (Category.comp_id _)
  let r' : O₀ ⟶ O₂ := Over.homMk (Spec.map g₂) hw
  let q' : O₀ ⟶ O₁ := Over.homMk (Spec.map g₁) rfl
  have hcomm : r' ≫ q = q' ≫ r := by
    ext1
    simpa [q, r, q', r'] using hw
  have hsq : IsPullback r'.left q'.left q.left r.left :=
    (isPullback_SpecMap_of_isPushout _ _ _ _ (isPushout_of_isPullback hpb hg₁).flip)
  haveI hcl : IsClosedImmersion r.left := IsClosedImmersion.spec_of_surjective f₁ hf₁
  have haff : IsAffineHom q.left := by
    change IsAffineHom (Spec.map f₂)
    infer_instance
  have hgl : GlobalTheory.PinchLift.Glues q.left r.left r'.left q'.left :=
    glues_spec hpb (spec_eq_of_artinian P)
  obtain ⟨hpb', haff', hcl', hgl'⟩ :=
    GlobalTheory.PinchLift.glues_whiskerLeft (Spec P) X O O₂ O₁ O₀ q r r' q' hflat hcomm hsq haff hcl hgl

  have hT : ∀ U : Over (Spec P), IsPullback (fst X U).left (snd X U).left X.hom U.hom :=
    fun U => IsPullback.of_hasPullback X.hom U.hom
  have h₀' : IsPullback (i₁ ≫ j₁) X₀.hom X.hom (Spec.map g₁ ≫ Spec.map f₁) := h₀.paste_horiz h₁
  let ψ₂ := IsPullback.isoIsPullback _ _ h₂ (hT O₂)
  let ψ₁ := IsPullback.isoIsPullback _ _ h₁ (hT O₁)
  let ψ₀ := IsPullback.isoIsPullback _ _ h₀' (hT O₀)
  have p₂f : ψ₂.hom ≫ (fst X O₂).left = j₂ := IsPullback.isoIsPullback_hom_fst _ _ h₂ (hT O₂)
  have p₂s : ψ₂.hom ≫ (snd X O₂).left = X₂.hom := IsPullback.isoIsPullback_hom_snd _ _ h₂ (hT O₂)
  have p₁f : ψ₁.hom ≫ (fst X O₁).left = j₁ := IsPullback.isoIsPullback_hom_fst _ _ h₁ (hT O₁)
  have p₁s : ψ₁.hom ≫ (snd X O₁).left = X₁.hom := IsPullback.isoIsPullback_hom_snd _ _ h₁ (hT O₁)
  have p₀f : ψ₀.hom ≫ (fst X O₀).left = i₁ ≫ j₁ := IsPullback.isoIsPullback_hom_fst _ _ h₀' (hT O₀)
  have p₀s : ψ₀.hom ≫ (snd X O₀).left = X₀.hom := IsPullback.isoIsPullback_hom_snd _ _ h₀' (hT O₀)
  let s : X.left ⟶ (X ⊗ O).left := (hT O).lift (𝟙 _) X.hom (by simp [O])
  have wf : ∀ {U V : Over (Spec P)} (k : U ⟶ V), (X ◁ k).left ≫ (fst X V).left = (fst X U).left := by
    intro U V k
    rw [← Over.comp_left, whiskerLeft_fst]
  have ws : ∀ {U V : Over (Spec P)} (k : U ⟶ V), (X ◁ k).left ≫ (snd X V).left = (snd X U).left ≫ k.left := by
    intro U V k
    rw [← Over.comp_left, ← Over.comp_left, whiskerLeft_snd]
  have E₂ : j₂ ≫ s = ψ₂.hom ≫ (X ◁ q).left := by
    apply (hT O).hom_ext
    · rw [Category.assoc, Category.assoc, wf, (hT O).lift_fst, p₂f, Category.comp_id]
    · rw [Category.assoc, Category.assoc, ws, (hT O).lift_snd, ← Category.assoc, p₂s]
      exact h₂.w
  have E₁ : j₁ ≫ s = ψ₁.hom ≫ (X ◁ r).left := by
    apply (hT O).hom_ext
    · rw [Category.assoc, Category.assoc, wf, (hT O).lift_fst, p₁f, Category.comp_id]
    · rw [Category.assoc, Category.assoc, ws, (hT O).lift_snd, ← Category.assoc, p₁s]
      exact h₁.w
  have E₀₂ : ψ₀.hom ≫ (X ◁ r').left = i₂ ≫ ψ₂.hom := by
    apply (hT O₂).hom_ext
    · rw [Category.assoc, Category.assoc, wf, p₀f, p₂f, hc]
    · rw [Category.assoc, Category.assoc, ws, ← Category.assoc, p₀s, p₂s]
      exact hc₂.symm
  have E₀₁ : ψ₀.hom ≫ (X ◁ q').left = i₁ ≫ ψ₁.hom := by
    apply (hT O₁).hom_ext
    · rw [Category.assoc, Category.assoc, wf, p₀f, p₁f]
    · rw [Category.assoc, Category.assoc, ws, ← Category.assoc, p₀s, p₁s]
      exact h₀.w.symm

  have hab0 : GlobalTheory.CechPic.pull i₂ (GlobalTheory.CechPic.cls L₂ hL₂) = GlobalTheory.CechPic.pull i₁ (GlobalTheory.CechPic.cls L₁ hL₁) := by
    rw [← GlobalTheory.CechPic.cls_pull hL₂ i₂ (pull_isLB hL₂ i₂), ← GlobalTheory.CechPic.cls_pull hL₁ i₁ (pull_isLB hL₁ i₁)]
    exact ((GlobalTheory.CechPic.cls_eq_iff _ _).2 hiso).symm
  have e2 : (X ◁ r').left ≫ ψ₂.inv = ψ₀.inv ≫ i₂ := by
    rw [Iso.eq_inv_comp, ← Category.assoc, E₀₂, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have e1 : (X ◁ q').left ≫ ψ₁.inv = ψ₀.inv ≫ i₁ := by
    rw [Iso.eq_inv_comp, ← Category.assoc, E₀₁, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hab : GlobalTheory.CechPic.pull (X ◁ r').left (GlobalTheory.CechPic.pull ψ₂.inv (GlobalTheory.CechPic.cls L₂ hL₂)) =
      GlobalTheory.CechPic.pull (X ◁ q').left (GlobalTheory.CechPic.pull ψ₁.inv (GlobalTheory.CechPic.cls L₁ hL₁)) := by
    rw [← GlobalTheory.CechPic.pull_comp, ← GlobalTheory.CechPic.pull_comp, e2, e1, GlobalTheory.CechPic.pull_comp,
      GlobalTheory.CechPic.pull_comp, hab0]
  obtain ⟨e', he2, he1⟩ := GlobalTheory.PinchLift.exists_pic_patch _ _ _ _ _ _ _ _ hpb' haff' hcl' hgl' _ _ hab
  obtain ⟨L, hL, hLe⟩ := GlobalTheory.CechPic.cls_surj (GlobalTheory.CechPic.pull s e')
  refine ⟨L, hL, ?_, ?_⟩
  · have h : GlobalTheory.CechPic.cls (L.pull j₁) (pull_isLB hL j₁) = GlobalTheory.CechPic.cls L₁ hL₁ := by
      rw [GlobalTheory.CechPic.cls_pull hL j₁, hLe, ← GlobalTheory.CechPic.pull_comp, E₁, GlobalTheory.CechPic.pull_comp, he1,
        ← GlobalTheory.CechPic.pull_comp, Iso.hom_inv_id, GlobalTheory.CechPic.pull_id]
    exact LBIso.symm ((GlobalTheory.CechPic.cls_eq_iff _ _).1 h)
  · have h : GlobalTheory.CechPic.cls (L.pull j₂) (pull_isLB hL j₂) = GlobalTheory.CechPic.cls L₂ hL₂ := by
      rw [GlobalTheory.CechPic.cls_pull hL j₂, hLe, ← GlobalTheory.CechPic.pull_comp, E₂, GlobalTheory.CechPic.pull_comp, he2,
        ← GlobalTheory.CechPic.pull_comp, Iso.hom_inv_id, GlobalTheory.CechPic.pull_id]
    exact LBIso.symm ((GlobalTheory.CechPic.cls_eq_iff _ _).1 h)

end GlobalTheory.ArtinPatch
