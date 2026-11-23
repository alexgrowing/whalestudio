import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.SlopeBoundSt
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelPullbackCorrespondence
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelComplexBaseChange
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeInnerProductMapIffStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeInnerProductOnSpanStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HodgeBC

open GroundTheory.Heights₂.Heights in

theorem span_one_tmul {L : Type} [Field L] (e : L →+* ℂ) (V : Type) [AddCommGroup V] [Module (𝓞 L) V] :
    Submodule.span ℂ {w : Fibre e V | ∃ y : V, w = (1 : ComplexAt e) ⊗ₜ[𝓞 L] y} = ⊤ := by
  rw [eq_top_iff]
  rintro w -
  change ComplexAt e ⊗[𝓞 L] V at w
  induction w using TensorProduct.induction_on with
  | zero => exact Submodule.zero_mem _
  | tmul c y =>
    have h : (c ⊗ₜ[𝓞 L] y : ComplexAt e ⊗[𝓞 L] V) = c • ((1 : ComplexAt e) ⊗ₜ[𝓞 L] y) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
    rw [h]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨y, rfl⟩)
  | add a b ha hb => exact Submodule.add_mem _ ha hb

private theorem isGrpPullback_one_left {S : Scheme.{0}} {G : Over S} [GrpObj G] (A : Over S) :
    (1 : A ⟶ G).left = A.hom ≫ (1 : Over.mk (𝟙 S) ⟶ G).left := by
  have h := LieSigma.comp_one_over (M := G) (Over.homMk A.hom (by simp) : A ⟶ Over.mk (𝟙 S))
  calc (1 : A ⟶ G).left
      = ((Over.homMk A.hom (by simp) : A ⟶ Over.mk (𝟙 S)) ≫ (1 : Over.mk (𝟙 S) ⟶ G)).left := by rw [h]
    _ = A.hom ≫ (1 : Over.mk (𝟙 S) ⟶ G).left := by rw [Over.comp_left]; rfl

private theorem one_left_comp_eq_comp_one_of_isGrpPullback {X X' : Scheme.{0}} (G' : Over X') [GrpObj G'] (G : Over X) [GrpObj G]
    (f : X' ⟶ X) (φ : G'.left ⟶ G.left) (hφ : IsGrpPullback G' G f φ) :
    (1 : Over.mk (𝟙 X') ⟶ G').left ≫ φ = f ≫ (1 : Over.mk (𝟙 X) ⟶ G).left := by
  have hε : (1 : Over.mk (𝟙 X') ⟶ G').left ≫ G'.hom = 𝟙 X' := Over.w (1 : Over.mk (𝟙 X') ⟶ G')
  have hw : ((1 : Over.mk (𝟙 X') ⟶ G').left ≫ φ) ≫ G.hom = (Over.mk ((Over.mk (𝟙 X')).hom ≫ f)).hom := by
    rw [Category.assoc, hφ.1.w, ← Category.assoc, hε]
    simp
  let x₀ : Over.mk ((Over.mk (𝟙 X')).hom ≫ f) ⟶ G := Over.homMk ((1 : Over.mk (𝟙 X') ⟶ G').left ≫ φ) hw
  have hmul := hφ.2 (Over.mk (𝟙 X')) 1 1 x₀ x₀ rfl rfl
  have hx : x₀ * x₀ = x₀ * 1 := by
    rw [_root_.mul_one]
    apply Over.OverMorphism.ext
    rw [hmul, _root_.mul_one]
    rfl
  have h1 : x₀ = 1 := _root_.mul_left_cancel hx
  have h2 : x₀.left = (1 : Over.mk ((Over.mk (𝟙 X')).hom ≫ f) ⟶ G).left := by rw [h1]
  rw [isGrpPullback_one_left] at h2
  simpa [x₀] using h2

private theorem exists_tanAt_comp_of_sabMap {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X X' : Scheme.{0}}
    {t : SAB H X} {t' : SAB H X'} {f : X' ⟶ X} (m : SABMap t' t f) (z : Sp ℂ ⟶ X')
    (v : epsAt z ⟶ t'.G) (hv : IsTanAt t'.G z v) :
    ∃ w : epsAt (z ≫ f) ⟶ t.G, w.left = v.left ≫ m.φ ∧ IsTanAt t.G (z ≫ f) w := by
  have hsq : m.φ ≫ t.G.hom = t'.G.hom ≫ f := m.cart.1.w
  refine ⟨Over.homMk (v.left ≫ m.φ) ?_, rfl, ?_⟩
  · rw [Category.assoc, hsq, ← Category.assoc, Over.w v]
    simp [epsAt]
  · have hv' : Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) ≫ v.left
        = (1 : Over.mk z ⟶ t'.G).left := hv
    show Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) ≫ (v.left ≫ m.φ)
        = (1 : Over.mk (z ≫ f) ⟶ t.G).left
    have h1 : (1 : Over.mk z ⟶ t'.G).left = (Over.mk z).hom ≫ (1 : Over.mk (𝟙 X') ⟶ t'.G).left :=
      isGrpPullback_one_left _
    have h2 : (1 : Over.mk (z ≫ f) ⟶ t.G).left = (Over.mk (z ≫ f)).hom ≫ (1 : Over.mk (𝟙 X) ⟶ t.G).left :=
      isGrpPullback_one_left _
    rw [h2, ← Category.assoc, hv', h1, Category.assoc, one_left_comp_eq_comp_one_of_isGrpPullback t'.G t.G f m.φ m.cart]
    simp [epsAt]

open LieMove in

theorem hodge_along {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X₀ X₁ X₂ : Scheme.{0}}
    {t₀ : SAB H X₀} {t₁ : SAB H X₁} {t₂ : SAB H X₂} {f₀ : X₀ ⟶ X₁} {f₁ : X₁ ⟶ X₂} (m₀ : SABMap t₀ t₁ f₀)
    (m₁ : SABMap t₁ t₂ f₁) (z : Sp ℂ ⟶ X₀) (p : Sp ℂ ⟶ X₂) (hp : p = (z ≫ f₀) ≫ f₁)
    {V : Type} [AddCommGroup V] [Module ℂ V] (Mp : LieModel t₂.G p V) (core : InnerProductSpace.Core ℂ V) (W : Set V)
    (h0 : (0 : V) ∈ W) (hs : Submodule.span ℂ W = ⊤)
    (hW : ∀ a ∈ W, ∀ b ∈ W, HodgeIP t₂.G t₂.PP.L p (Mp.pt a) (Mp.pt b) (core.inner a b))
    {V' : Type} (Tn : V' → (epsAt z ⟶ t₀.G)) (hT : ∀ x, IsTanAt t₀.G z (Tn x)) :
    ∃ D : V' → V, (∀ x x', HodgeIP t₀.G t₀.PP.L z (Tn x) (Tn x') (core.inner (D x) (D x'))) ∧
      ∀ x a, (Tn x).left ≫ m₀.φ ≫ m₁.φ = (Mp.pt a).left → D x = a := by
  subst hp
  have hall : ∀ a b : V, HodgeIP t₂.G t₂.PP.L ((z ≫ f₀) ≫ f₁) (Mp.pt a) (Mp.pt b) (core.inner a b) :=
    GlobalTheory.T.hodge_inner_product_on_span E H X₁ X₂ t₁ t₂ f₁ m₁ (z ≫ f₀) V Mp core W h0 hs hW
  have key : ∀ x, ∃ w₁ : epsAt (z ≫ f₀) ⟶ t₁.G, w₁.left = (Tn x).left ≫ m₀.φ ∧
      ∃ a : V, (Mp.pt a).left = w₁.left ≫ m₁.φ := by
    intro x
    obtain ⟨w₁, hw₁, ht₁⟩ := exists_tanAt_comp_of_sabMap m₀ z (Tn x) (hT x)
    obtain ⟨w₂, hw₂, ht₂⟩ := exists_tanAt_comp_of_sabMap m₁ (z ≫ f₀) w₁ ht₁
    obtain ⟨a, ha⟩ := Mp.onto w₂ ht₂
    exact ⟨w₁, hw₁, a, by rw [ha, hw₂]⟩
  choose w₁ hw₁ D hD using key
  refine ⟨D, fun x x' => ?_, fun x a h => ?_⟩
  · rw [GlobalTheory.T.hodge_inner_product_map_iff E H X₁ t₁ X₀ t₀ f₀ m₀ z (Tn x) (Tn x') (w₁ x) (w₁ x') _ (hw₁ x) (hw₁ x'),
      GlobalTheory.T.hodge_inner_product_map_iff E H X₂ t₂ X₁ t₁ f₁ m₁ (z ≫ f₀) (w₁ x) (w₁ x') (Mp.pt (D x)) (Mp.pt (D x')) _ (hD x) (hD x')]
    exact hall _ _
  · apply Mp.inj
    apply Over.OverMorphism.ext
    rw [hD x, hw₁ x]
    exact (Category.assoc _ _ _).trans h

theorem lifts_left {S : Scheme.{0}} {R R' : Type} [CommRing R] [CommRing R'] {G : Over S} [GrpObj G]
    {x : Spec (CommRingCat.of R) ⟶ S} {V : Type} [AddCommGroup V] [Module R V] (M : LieModel G x V) (c : R →+* R') (a : V)
    (v : epsAt (spMap c ≫ x) ⟶ G) (h : M.Lifts c (𝟙 G.left) a v) :
    v.left = spMap (dualMap c) ≫ (M.pt a).left := by
  have h' : v.left ≫ 𝟙 G.left = spMap (dualMap c) ≫ (M.pt a).left := h
  simpa using h'

open GroundTheory.Heights₂.Heights in

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] [NumberField L] (t' : SAB H (Sp (𝓞 L))) (tB : SAB H (Sp L)) (tC : SAB H (Sp ℂ)) (e : L →+* ℂ) (m' : SABMap tB t' (spMap (algebraMap (𝓞 L) L))) (mB : SABMap tC tB (spMap e)) (B : GroundTheory.Heights₂.Heights.HermitianBundle.{0} L) (MB : LieModel t'.G (𝟙 _) B.carrier), IsFibre (HodgeIP t'.G t'.PP.L) (𝟙 _) B MB → ∀ (V' : Type) (Tn : V' → (epsAt (𝟙 (Sp ℂ)) ⟶ tC.G)), (∀ x, IsTanAt tC.G (𝟙 _) (Tn x)) → ∃ hb : V' → V' → ℂ, (∀ x x', HodgeIP tC.G tC.PP.L (𝟙 _) (Tn x) (Tn x') (hb x x')) ∧ ∀ (x x' : V') (y y' : B.carrier), (Tn x).left ≫ mB.φ ≫ m'.φ = spMap (dualMap (e.comp (algebraMap (𝓞 L) L))) ≫ (MB.pt y).left → (Tn x').left ≫ mB.φ ≫ m'.φ = spMap (dualMap (e.comp (algebraMap (𝓞 L) L))) ≫ (MB.pt y').left → hb x x' = (B.metric.form e).inner ((1 : GroundTheory.Heights₂.Heights.ComplexAt e) ⊗ₜ[𝓞 L] y) ((1 : GroundTheory.Heights₂.Heights.ComplexAt e) ⊗ₜ[𝓞 L] y') := by
  intro E _ _ _ H L _ _ t' tB tC e m' mB B MB hF V' Tn hT
  haveI : Smooth t'.G.hom := @ReciprocityTheory.ChartRestriction.G.Semi.IsSemiAbelian.smooth _ _ _ t'.semi
  obtain ⟨Mσ, hMσ⟩ := LieSigma.lieModel_fibre (Sp (𝓞 L)) t'.G L (𝟙 _) B.carrier MB e
  have hp : spMap (e.comp (algebraMap (𝓞 L) L)) ≫ 𝟙 (Sp (𝓞 L))
      = (𝟙 (Sp ℂ) ≫ spMap e) ≫ spMap (algebraMap (𝓞 L) L) := by
    simp only [Category.comp_id, Category.id_comp]
    unfold spMap
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  obtain ⟨D, hD1, hD2⟩ := hodge_along mB m' (𝟙 _) _ hp Mσ (B.metric.form e)
    {w | ∃ y : B.carrier, w = (1 : ComplexAt e) ⊗ₜ[𝓞 L] y} ⟨0, by simp⟩ (span_one_tmul e B.carrier)
    (by
      rintro a ⟨y, rfl⟩ b ⟨y', rfl⟩
      exact hF e y y' _ _ (hMσ y) (hMσ y'))
    Tn hT
  refine ⟨fun x x' => (B.metric.form e).inner (D x) (D x'), hD1, ?_⟩
  intro x x' y y' hx hx'
  have e1 : D x = (1 : ComplexAt e) ⊗ₜ[𝓞 L] y :=
    hD2 x _ (hx.trans (lifts_left MB _ _ _ (hMσ y)).symm)
  have e2 : D x' = (1 : ComplexAt e) ⊗ₜ[𝓞 L] y' :=
    hD2 x' _ (hx'.trans (lifts_left MB _ _ _ (hMσ y')).symm)
  simp only [e1, e2]

end GlobalTheory.CompanionTheory.Ar.HodgeBC
