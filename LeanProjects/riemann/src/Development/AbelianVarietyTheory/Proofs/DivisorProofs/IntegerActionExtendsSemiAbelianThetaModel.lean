import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SpecializesGenericImage
import Development.AbelianVarietyTheory.Definitions.Divisors.TorMatch
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsActionPullbackUniversalUnitaryStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeEndomorphismExtOfDensePointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralPullbackRationalSaturationModelOpenStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open GlobalTheory
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

theorem GlobalTheory.UPoinc.exists_endo_of_generic {Z W : Scheme.{0}} [IsIntegral W] {G : Over Z} [GrpObj G] {G₀ : Over W}
    [GrpObj G₀] (hab : IsAbelianScheme G₀) {q : W ⟶ Z} {Φ : G₀.left ⟶ G.left} (hΦ : IsGrpPullback G₀ G q Φ)
    {Ω : Type} [Field Ω] (pt : Sp Ω ⟶ W) (hd : Dense (Set.range pt)) (m : Sp Ω ⟶ Z) (hm : pt ≫ q = m)
    (hendo : ∀ f : (Over.pullback m).obj G ⟶ (Over.pullback m).obj G, IsMonHom f →
      ∃! F : G ⟶ G, IsMonHom F ∧ (Over.pullback m).map F = f)
    (f₀ : G₀ ⟶ G₀) (hf₀ : IsMonHom f₀) : ∃ F : G ⟶ G, IsMonHom F ∧ Φ ≫ F.left = f₀.left ≫ Φ := by
  have hgen := isGrpPullback_pullback G m
  have wk : pullback.fst G.hom m ≫ G.hom = (pullback.snd G.hom m ≫ pt) ≫ q := by
    rw [Category.assoc, hm, pullback.condition]
  let k : pullback G.hom m ⟶ G₀.left := hΦ.1.lift (pullback.fst _ _) (pullback.snd _ _ ≫ pt) wk
  have hk : IsGrpPullback ((Over.pullback m).obj G) G₀ pt k :=
    hΦ.cancel (hgen.congr hm.symm (hΦ.1.lift_fst _ _ _).symm) (hΦ.1.lift_snd _ _ _)
  obtain ⟨e, he, hek⟩ := GlobalTheory.Ex.Arch.exists_pull_endo hk f₀ hf₀
  obtain ⟨F, ⟨hF, hFe⟩, -⟩ := hendo e he
  obtain ⟨F₀, hF₀, hF₀e⟩ := GlobalTheory.Ex.Arch.exists_pull_endo hΦ F hF
  have wθ : (pullback.fst G₀.hom pt ≫ Φ) ≫ G.hom = pullback.snd G₀.hom pt ≫ m := by
    rw [Category.assoc, hΦ.1.w, ← Category.assoc, pullback.condition, Category.assoc, hm]
  let θ : pullback G₀.hom pt ⟶ pullback G.hom m := pullback.lift _ _ wθ
  have hθk : θ ≫ k = pullback.fst _ _ := by
    apply hΦ.1.hom_ext
    · rw [Category.assoc, hΦ.1.lift_fst, pullback.lift_fst]
    · rw [Category.assoc, hΦ.1.lift_snd, ← Category.assoc, pullback.lift_snd, pullback.condition]
  have hFm : ((Over.pullback m).map F).left ≫ pullback.fst G.hom m = pullback.fst G.hom m ≫ F.left := by
    first | exact pullback.lift_fst _ _ _ | (simp [Over.pullback, pullback.map]) | (erw [pullback.lift_fst])
  have key : F₀ = f₀ := by
    apply GlobalTheory.T.abelianScheme_endomorphism_ext_of_dense_point W G₀ hab Ω pt hd
    apply hΦ.1.hom_ext
    · calc (pullback.fst G₀.hom pt ≫ F₀.left) ≫ Φ = pullback.fst G₀.hom pt ≫ Φ ≫ F.left := by
            rw [Category.assoc, hF₀e]
        _ = θ ≫ pullback.fst G.hom m ≫ F.left := by rw [← Category.assoc θ, pullback.lift_fst, Category.assoc]
        _ = θ ≫ e.left ≫ pullback.fst G.hom m := by rw [← hFm, hFe]
        _ = θ ≫ e.left ≫ k ≫ Φ := by rw [hΦ.1.lift_fst]
        _ = θ ≫ k ≫ f₀.left ≫ Φ := by rw [← Category.assoc e.left, hek, Category.assoc]
        _ = (pullback.fst G₀.hom pt ≫ f₀.left) ≫ Φ := by rw [← Category.assoc θ, hθk, Category.assoc]
    · rw [Category.assoc, Category.assoc, Over.w F₀, Over.w f₀]
  exact ⟨F, hF, by rw [← hF₀e, key]⟩

theorem GlobalTheory.UPoinc.act_extends_ratModel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C) (M : RatModel X₁.o₁ X₁.Ω₁) (U₀ : M.Z.Opens) (EE : M.Lat X₁.S.J) (out : ZHOut X₁.ρ M U₀ EE), X₁.S.admitted M U₀ → ∃ f : 𝓞 E → (out.G ⟶ out.G), (∀ a, IsMonHom (f a)) ∧ ∀ (K : Type) [Field K] (ξ₀ : Sp K ⟶ U₀.toScheme) (y : Sp K ⟶ Xo.XF c), X₁.Lies (ξ₀ ≫ out.u₀) y → ∀ (tK : SAB H (Sp K)), Nonempty (SABMap tK Xo.univ.t (y ≫ pullback.fst _ _)) → ∃ γ : tK.G.left ⟶ out.G.left, IsGrpPullback tK.G out.G (ξ₀ ≫ U₀.ι) γ ∧ LBIso tK.PP.L (out.L.L.pull γ) ∧ ∀ a, (tK.act.act a).left ≫ γ = γ ≫ (f a).left := by
  intro E _ _ _ H Dw l Xo c C X₁ M U₀ EE out hAdm
  haveI := X₁.ar.char
  obtain ⟨hW, pt, hpt, hd⟩ := GlobalTheory.T.isIntegral_pullback_rationalSaturation_model_open X₁.o₁ X₁.Ω₁ M U₀ X₁.S.R out.u₀ hAdm.1.ne out.u₀_gen
  haveI := hW
  obtain ⟨G₁, _, α, β, hα, hβ, hL⟩ := X₁.pulled
  let s : pullback out.u₀ (spMap (toRat X₁.S.R)) ⟶ Sp (ratHull X₁.S.R) := pullback.snd _ _
  let G₀ : Over (pullback out.u₀ (spMap (toRat X₁.S.R))) := (Over.pullback s).obj G₁
  have h₀ : IsGrpPullback G₀ G₁ s (pullback.fst G₁.hom s) := isGrpPullback_pullback G₁ s
  let w : pullback out.u₀ (spMap (toRat X₁.S.R)) ⟶ Xo.XF c := s ≫ X₁.u
  have hβ₀ : IsGrpPullback G₀ Xo.univ.t.G (w ≫ pullback.fst _ _) (pullback.fst G₁.hom s ≫ β) :=
    (h₀.comp hβ).congr (Category.assoc _ _ _).symm rfl
  obtain ⟨f₀, hf₀, hT⟩ := GlobalTheory.T.exists_action_pullback_universalUnitary E H Dw l Xo c _ w G₀ _ hβ₀
  have hα₀ := h₀.comp hα
  have wψ : (pullback.fst G₁.hom s ≫ α) ≫ X₁.ρ.P.A.hom = (G₀.hom ≫ pullback.fst out.u₀ (spMap (toRat X₁.S.R))) ≫ out.u₀ := by
    rw [hα₀.1.w, Category.assoc, pullback.condition]
  let ψ : G₀.left ⟶ pullback X₁.ρ.P.A.hom out.u₀ := pullback.lift _ _ wψ
  have hψ : IsGrpPullback G₀ ((Over.pullback out.u₀).obj X₁.ρ.P.A) (pullback.fst out.u₀ (spMap (toRat X₁.S.R))) ψ :=
    (isGrpPullback_pullback X₁.ρ.P.A out.u₀).cancel (hα₀.congr pullback.condition.symm (pullback.lift_fst _ _ _).symm)
      (pullback.lift_snd _ _ _)
  have hΦ := hψ.comp out.cart
  have hm : pt ≫ pullback.fst out.u₀ (spMap (toRat X₁.S.R)) ≫ U₀.ι = M.pt := hpt
  have hab : IsAbelianScheme G₀ := PolPull.isAbelianScheme_of_isGrpPullback X₁.ρ.P.isAb hα₀
  choose F hF hFe using fun a => exists_endo_of_generic hab hΦ pt hd M.pt hm out.endo (f₀ a) (hf₀ a).1
  refine ⟨F, hF, ?_⟩
  intro K _ ξ₀ y hLies tK ⟨mm⟩
  obtain ⟨x', hx', hxy⟩ := hLies
  let x : Sp K ⟶ pullback out.u₀ (spMap (toRat X₁.S.R)) := pullback.lift ξ₀ x' hx'.symm
  have hxw : x ≫ w = y := by
    show x ≫ pullback.snd _ _ ≫ X₁.u = y
    rw [← Category.assoc, pullback.lift_snd, hxy]
  have mm' : SABMap tK Xo.univ.t ((x ≫ w) ≫ pullback.fst _ _) := by rw [hxw]; exact mm
  obtain ⟨γ₀, hγ₀, -, hLγ, hact⟩ := hT (Sp K) x tK mm'
  refine ⟨γ₀ ≫ ψ ≫ out.φ, (hγ₀.comp hΦ).congr (by rw [← Category.assoc, pullback.lift_fst]) rfl, ?_, fun a => ?_⟩
  · have hU := Xo.univ.t.PP.isLB
    have hP := X₁.ρ.P.isLB
    have hO := out.L.isLB
    have i1 : LBIso (out.L.L.pull out.φ) (X₁.ρ.P.L.pull (pullback.fst X₁.ρ.P.A.hom out.u₀)) := ⟨out.w, out.w_gen⟩
    have i2 : LBIso (out.L.L.pull (ψ ≫ out.φ)) (X₁.ρ.P.L.pull (pullback.fst G₁.hom s ≫ α)) :=
      GenSpread.lbIso_pull_comp ψ rfl (pullback.lift_fst _ _ _).symm i1
    have i3 : LBIso (X₁.ρ.P.L.pull (pullback.fst G₁.hom s ≫ α)) (Xo.univ.t.PP.L.pull (pullback.fst G₁.hom s ≫ β)) :=
      GenSpread.lbIso_pull_comp (pullback.fst G₁.hom s) rfl rfl hL
    have i4 := LBIso.trans (pull_isLB hO _) (pull_isLB hP _) (pull_isLB hU _) i2 i3
    have i5 : LBIso (out.L.L.pull (γ₀ ≫ ψ ≫ out.φ)) (Xo.univ.t.PP.L.pull (γ₀ ≫ pullback.fst G₁.hom s ≫ β)) :=
      GenSpread.lbIso_pull_comp γ₀ rfl rfl i4
    have i6 : LBIso (Xo.univ.t.PP.L.pull (γ₀ ≫ pullback.fst G₁.hom s ≫ β))
        ((Xo.univ.t.PP.L.pull (pullback.fst G₁.hom s ≫ β)).pull γ₀) := GenSpread.lbIso_pull_pull hU γ₀ rfl
    exact LBIso.trans tK.PP.isLB (pull_isLB (pull_isLB hU _) _) (pull_isLB hO _) hLγ
      (LBIso.trans (pull_isLB (pull_isLB hU _) _) (pull_isLB hU _) (pull_isLB hO _) i6.symm i5.symm)
  · rw [← Category.assoc, hact a, Category.assoc, Category.assoc, ← hFe a, Category.assoc]

end
