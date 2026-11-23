import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UOver
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.ZH GlobalTheory.UPoinc GlobalTheory.UCovSep
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UCovSep

theorem uAct_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (R R' : Subalgebra o Ω) (h : R ≤ R') (P : PolAV (Sp R)) (P' : PolAV (Sp R')) (φ : P'.A.left ⟶ P.A.left), IsGrpPullback P'.A P.A (spMap (Subalgebra.inclusion h).toRingHom) φ → LBIso P'.L (P.L.pull φ) → ∀ (act : 𝓞 E → (P.A ⟶ P.A)) (u : Sp (ratHull R) ⟶ Xo.XF c), (∀ a, IsMonHom (act a)) → GlobalTheory.UCovSep.UAct Xo c P act (toRat R) u → ∃ act' : 𝓞 E → (P'.A ⟶ P'.A), (∀ a, IsMonHom (act' a)) ∧ (∀ a, (act' a).left ≫ φ = φ ≫ (act a).left) ∧ GlobalTheory.UCovSep.UAct Xo c P' act' (toRat R') (spMap (Subalgebra.inclusion (ratHull_mono h)).toRingHom ≫ u) := by
  intro E _ _ _ H Dw l Xo c o Ω _ _ _ R R' h P P' φ hφ hL act u hact hU

  have inj : ∀ {T : Over (Sp R')} {x y : T ⟶ P'.A}, pushPt hφ.1.w x = pushPt hφ.1.w y → x = y := fun {T x y} e =>
    Over.OverMorphism.ext (hφ.1.hom_ext (congrArg (fun q => q.left) e) (by rw [Over.w, Over.w]))
  let act' : 𝓞 E → (P'.A ⟶ P'.A) := fun a => Over.homMk (hφ.1.lift (φ ≫ (act a).left) P'.A.hom
    (by rw [Category.assoc, Over.w, hφ.1.w])) (hφ.1.lift_snd _ _ _)
  have ha : ∀ a, (act' a).left ≫ φ = φ ≫ (act a).left := fun a => hφ.1.lift_fst _ _ _
  have pa : ∀ {T : Over (Sp R')} (x : T ⟶ P'.A) a, pushPt hφ.1.w (x ≫ act' a) = pushPt hφ.1.w x ≫ act a := fun x a =>
    Over.OverMorphism.ext (by
      show (x.left ≫ _) ≫ _ = (x.left ≫ _) ≫ _
      rw [Category.assoc, ha, Category.assoc])
  have pm : ∀ {T : Over (Sp R')} (x y : T ⟶ P'.A), pushPt hφ.1.w (x * y) = pushPt hφ.1.w x * pushPt hφ.1.w y :=
    fun x y => map_mul (pushHom hφ _) x y
  have hact' : ∀ a, IsMonHom (act' a) := fun a => isMonHom_of_mul _ fun T x y => inj (by
    have := hact a
    rw [pa, pm, pm, pa, pa, MonObj.mul_comp])
  refine ⟨act', hact', ha, ?_⟩

  obtain ⟨G, _, α, β, hα, hβ, hLG, hf⟩ := hU
  set g := (Subalgebra.inclusion (ratHull_mono h)).toRingHom with hg
  have hG := isGrpPullback_pullback G (spMap g)
  have e : spMap g ≫ spMap (toRat R) = spMap (toRat R') ≫ spMap (Subalgebra.inclusion h).toRingHom := by
    rw [← Spec.map_comp, ← Spec.map_comp]; rfl
  have hα₀ : IsGrpPullback ((Over.pullback (spMap g)).obj G) P.A
      (spMap (toRat R') ≫ spMap (Subalgebra.inclusion h).toRingHom) (pullback.fst _ _ ≫ α) := (hG.comp hα).congr e rfl
  have w : (pullback.fst G.hom (spMap g) ≫ α) ≫ P.A.hom =
      (((Over.pullback (spMap g)).obj G).hom ≫ spMap (toRat R')) ≫ spMap (Subalgebra.inclusion h).toRingHom := by
    rw [Category.assoc]; exact hα₀.1.w
  have e₁ := hφ.1.lift_fst _ _ w
  have hα' := hφ.cancel (hα₀.congr rfl e₁.symm) (hφ.1.lift_snd _ _ w)
  have hβ' := (hG.comp hβ).congr (Category.assoc _ _ _).symm rfl
  refine ⟨_, _, hφ.1.lift _ _ w, pullback.fst _ _ ≫ β, hα', hβ', ?_, fun a => ?_⟩
  · exact LBIso.trans (pull_isLB P'.isLB _) (pull_isLB P.isLB _) (pull_isLB Xo.univ.t.PP.isLB _)
      (GenSpread.lbIso_pull_of_lbIso hL _ e₁.symm) (GenSpread.lbIso_pull_comp _ rfl rfl hLG)
  · obtain ⟨f, hfα, hfβ⟩ := hf a
    have hfl : ((Over.pullback (spMap g)).map f).left ≫ pullback.fst G.hom (spMap g) = pullback.fst G.hom (spMap g) ≫ f.left :=
      pullback.lift_fst _ _ _
    refine ⟨(Over.pullback (spMap g)).map f, ?_, ?_⟩
    · apply hφ.1.hom_ext
      · rw [Category.assoc, e₁, Category.assoc, ha, ← Category.assoc (hφ.1.lift _ _ w), e₁,
          ← Category.assoc _ (pullback.fst _ _), hfl, Category.assoc, hfα, Category.assoc]
      · rw [Category.assoc, hφ.1.lift_snd, Category.assoc, Over.w, hφ.1.lift_snd, ← Category.assoc, Over.w]
    · rw [← Category.assoc, hfl, Category.assoc, hfβ, Category.assoc]

end GlobalTheory.UCovSep
