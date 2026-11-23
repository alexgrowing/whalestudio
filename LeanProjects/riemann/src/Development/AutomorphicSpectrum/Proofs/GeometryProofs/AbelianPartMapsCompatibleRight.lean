import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.SlopeBoundSt
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ArchBetween
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelPullbackEquivalence
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianPartBaseChangeStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeInnerProductPullbackUniqueStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeInnerProductOnSpanStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelComplexBaseChangeStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianPartMapsCompatibleLeftStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.SlopeNorm

open GroundTheory.Heights₂.Heights

theorem core_left {V : Type} [AddCommGroup V] [Module ℂ V] (c₁ c₂ : InnerProductSpace.Core ℂ V) (W : Set V)
    (hW : Submodule.span ℂ W = ⊤) (a : V) (h : ∀ b ∈ W, c₁.inner b a = c₂.inner b a) (b : V) :
    c₁.inner b a = c₂.inner b a := by
  have hb : b ∈ Submodule.span ℂ W := hW ▸ Submodule.mem_top
  induction hb using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero =>
    have e₁ := c₁.smul_left 0 a 0
    have e₂ := c₂.smul_left 0 a 0
    simp only [smul_zero, map_zero, zero_mul] at e₁ e₂
    rw [e₁, e₂]
  | add x y _ _ hx hy => rw [c₁.add_left, c₂.add_left, hx, hy]
  | smul r x _ hx => rw [c₁.smul_left, c₂.smul_left, hx]

theorem core_eq {V : Type} [AddCommGroup V] [Module ℂ V] (c₁ c₂ : InnerProductSpace.Core ℂ V) (W : Set V)
    (hW : Submodule.span ℂ W = ⊤) (h : ∀ a ∈ W, ∀ b ∈ W, c₁.inner a b = c₂.inner a b) (a b : V) :
    c₁.inner a b = c₂.inner a b := by
  refine core_left c₁ c₂ W hW b (fun x hx => ?_) a
  have e := core_left c₁ c₂ W hW x (fun y hy => h y hy x hx) b
  rw [← c₁.conj_inner_symm, ← c₂.conj_inner_symm, e]

variable {L : Type} [Field L]

theorem span_tmul (σ : L →+* ℂ) (V : Type) [AddCommGroup V] [Module (𝓞 L) V] :
    Submodule.span ℂ (Set.range fun e : V => (1 : ComplexAt σ) ⊗ₜ[𝓞 L] e) = ⊤ := by
  refine (Submodule.eq_top_iff'.2 fun x => ?_)
  induction x using TensorProduct.induction_on with
  | zero => exact Submodule.zero_mem _
  | tmul c e =>
    have hc : c ⊗ₜ[𝓞 L] e = ((ComplexAt.ofComplex σ).symm c : ℂ) • ((1 : ComplexAt σ) ⊗ₜ[𝓞 L] e) := by
      rw [TensorProduct.smul_tmul', ComplexAt.complex_smul_def]
      simp
    rw [hc]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨e, rfl⟩)
  | add a b ha hb => exact Submodule.add_mem _ ha hb

theorem spComp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (d : A →+* B) (c : B →+* C) :
    spMap c ≫ spMap d = spMap (c.comp d) := by
  simp only [spMap, ← Spec.map_comp]
  rfl

def lf {S : Scheme.{0}} {G : Over S} {R : Type} [CommRing R] {x : Sp R ⟶ S} (v : epsAt x ⟶ G) :
    Sp (DualNumber R) ⟶ G.left :=
  v.left

theorem exists_transport {S : Scheme.{0}} {G : Over S} [GrpObj G] {R : Type} [CommRing R] {x x' : Sp R ⟶ S}
    (h : x = x') {V : Type} [AddCommGroup V] [Module R V] (M : LieModel G x V) :
    ∃ M' : LieModel G x' V, ∀ e, lf (M'.pt e) = lf (M.pt e) := by
  subst h
  exact ⟨M, fun _ => rfl⟩

theorem exists_lift {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) {R : Type} [CommRing R] (x' : Sp R ⟶ S') {b : Sp R ⟶ S}
    (hb : x' ≫ f = b) {V : Type} [AddCommGroup V] [Module R V] (M : LieModel G b V) :
    ∃ M' : LieModel G' x' V, ∀ e, lf (M'.pt e) ≫ φ = lf (M.pt e) := by
  subst hb
  exact (LiePull.lieModel_pullback S S' G G' f φ h R x' V).1 M

theorem exists_push {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) {R : Type} [CommRing R] (x' : Sp R ⟶ S')
    (v : epsAt x' ⟶ G') : ∃ u : epsAt (x' ≫ f) ⟶ G, lf v ≫ φ = lf u :=
  ⟨LiePull.tanPts h x' v, rfl⟩

theorem hodge_congr {S : Scheme.{0}} {G : Over S} [GrpObj G] (Lb : LB G.left) {z z' : Sp ℂ ⟶ S} (h : z = z')
    {v w : epsAt z ⟶ G} {v' w' : epsAt z' ⟶ G} (hv : lf v = lf v') (hw : lf w = lf w') {c : ℂ}
    (hc : HodgeIP G Lb z v w c) : HodgeIP G Lb z' v' w' c := by
  subst h
  obtain rfl : v = v' := Over.OverMorphism.ext hv
  obtain rfl : w = w' := Over.OverMorphism.ext hw
  exact hc

theorem ip_congr {S : Scheme.{0}} {G : Over S}
    (ip : ∀ z : Sp ℂ ⟶ S, (epsAt z ⟶ G) → (epsAt z ⟶ G) → ℂ) {z z' : Sp ℂ ⟶ S} (h : z = z')
    {v w : epsAt z ⟶ G} {v' w' : epsAt z' ⟶ G} (hv : lf v = lf v') (hw : lf w = lf w') :
    ip z v w = ip z' v' w' := by
  subst h
  obtain rfl : v = v' := Over.OverMorphism.ext hv
  obtain rfl : w = w' := Over.OverMorphism.ext hw
  rfl

end GlobalTheory.CompanionTheory.Ar.SlopeNorm

open GroundTheory.Heights₂.Heights GlobalTheory.CompanionTheory.Ar.SlopeNorm GlobalTheory.CompanionTheory.Ar.LiePull in

theorem GlobalTheory.CompanionTheory.Ar.SlopeNorm.sqAt_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (L₁ L : Type) [Field L₁] [Field L] [NumberField L] (e₂ : L₁ →+* L) (z₁ : Sp L₁ ⟶ X) (z : Sp (𝓞 L) ⟶ X) (hz : spMap (algebraMap (𝓞 L) L) ≫ z = spMap e₂ ≫ z₁) (P₁ : AbPart t z₁) (P₂ : AbPart t (spMap e₂ ≫ z₁)) (mK2 : SABMap P₂.tK P₁.tK (spMap e₂)) (mB2 : SABMap P₂.tB P₁.tB (spMap e₂)) (c1 : mK2.φ ≫ P₁.m.φ = P₂.m.φ) (c2 : mK2.φ ≫ (P₁.τ.q ≫ P₁.e.hom).left = (P₂.τ.q ≫ P₂.e.hom).left ≫ mB2.φ) (t' : SAB H (Sp (𝓞 L))) (tK : SAB H (Sp L)) (m' : SABMap tK t' (spMap (algebraMap (𝓞 L) L))) (mP : SABMap tK P₁.tB (spMap e₂)) (w : P₂.tB.G.left ⟶ tK.G.left) (hw : w ≫ mP.φ = mB2.φ) (hw' : w ≫ tK.G.hom = P₂.tB.G.hom) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (Li : Type) [AddCommGroup Li] [Module Ω Li] (M₀ : LieModel t.G ξ Li) (K : Type) (J : K → Type) (y : (Σ k, J k) → Ω) (h : LieMetric M₀ y) (K₀ : ℝ) (hQ : ∀ (zc : Sp ℂ ⟶ X) (P : AbPart t zc) (v : epsAt (𝟙 (Sp ℂ)) ⟶ P.tK.G) (v₀ : epsAt zc ⟶ t.G) (c : ℂ), IsTanAt _ _ v → v.left ≫ P.m.φ = v₀.left → HodgeIP P.tB.G P.tB.PP.L (𝟙 _) (v ≫ P.τ.q ≫ P.e.hom) (v ≫ P.τ.q ≫ P.e.hom) c → c.re ≤ K₀ * (h.ip zc v₀ v₀).re) (B B' : GroundTheory.Heights₂.Heights.HermitianBundle.{0} L) (MB : LieModel t.G z B.carrier) (MB' : LieModel t'.G (𝟙 _) B'.carrier) (hB : IsFibre (fun z v w c => c = h.ip z v w) z B MB) (hB' : IsFibre (HodgeIP t'.G t'.PP.L) (𝟙 _) B' MB') (f : B.carrier →ₗ[𝓞 L] B'.carrier) (hf : ∀ (e : B.carrier) (v : epsAt (𝟙 (Sp L)) ⟶ P₂.tK.G), MB.Lifts (algebraMap (𝓞 L) L) P₂.m.φ e v → MB'.Lifts (algebraMap (𝓞 L) L) (P₂.e.hom.left ≫ w ≫ m'.φ) (f e) (v ≫ P₂.τ.q)) (σ : L →+* ℂ) (x : GroundTheory.Heights₂.Heights.Fibre σ B.carrier), sqAt B' σ (f.lTensor (GroundTheory.Heights₂.Heights.ComplexAt σ) x) ≤ K₀ * sqAt B σ x := by
  intro E _ _ _ H X t L₁ L _ _ _ e₂ z₁ z hz P₁ P₂ mK2 mB2 c1 c2 t' tK m' mP w hw hw' Ω _ ξ Li _ _ M₀ K J y h K₀ hQ
    B B' MB MB' hB hB' f hf σ x
  haveI : Smooth t.G.hom := t.semi.smooth
  haveI : Smooth t'.G.hom := t'.semi.smooth
  obtain ⟨Pσ, mKσ, mBσ, d1, d2⟩ := GlobalTheory.T.abelian_part_base_change E H X t L₁ ℂ z₁ P₁ (σ.comp e₂)
  obtain ⟨Mσ, hMσ⟩ := GlobalTheory.T.lie_model_complex_base_change X t.G L z B.carrier MB σ
  obtain ⟨Mσ', hMσ'⟩ := GlobalTheory.T.lie_model_complex_base_change (Sp (𝓞 L)) t'.G L (𝟙 _) B'.carrier MB' σ
  have hb : spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ z = spMap (σ.comp e₂) ≫ z₁ := by
    rw [← spComp (algebraMap (𝓞 L) L) σ, ← spComp e₂ σ, Category.assoc, Category.assoc, hz]
  have hb' : spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ 𝟙 _ = spMap σ ≫ spMap (algebraMap (𝓞 L) L) := by
    rw [Category.comp_id, spComp]
  have hb2 : spMap σ ≫ spMap e₂ = 𝟙 _ ≫ spMap (σ.comp e₂) := by
    rw [Category.id_comp, spComp]

  obtain ⟨core₁, hcore₁⟩ := h.herm _ (Fibre σ B.carrier) Mσ
  have h1 : ∀ a b, (B.metric.form σ).inner a b = h.ip _ (Mσ.pt a) (Mσ.pt b) := by
    intro a b
    rw [← hcore₁]
    refine core_eq _ _ _ (span_tmul σ _) ?_ a b
    rintro _ ⟨e, rfl⟩ _ ⟨e', rfl⟩
    rw [hcore₁]
    exact hB σ e e' _ _ (hMσ e) (hMσ e')

  obtain ⟨Mz, hMz⟩ := exists_transport hb' Mσ'
  have h2 : ∀ a b, HodgeIP t'.G t'.PP.L (spMap σ ≫ spMap (algebraMap (𝓞 L) L)) (Mz.pt a) (Mz.pt b)
      ((B'.metric.form σ).inner a b) := by
    refine GlobalTheory.T.hodge_inner_product_on_span E H (Sp L) (Sp (𝓞 L)) tK t' (spMap (algebraMap (𝓞 L) L)) m' (spMap σ)
      (Fibre σ B'.carrier) Mz (B'.metric.form σ) (Set.range fun e => (1 : ComplexAt σ) ⊗ₜ[𝓞 L] e)
      ⟨0, TensorProduct.tmul_zero _ _⟩ (span_tmul σ _) ?_
    rintro _ ⟨e, rfl⟩ _ ⟨e', rfl⟩
    exact hodge_congr t'.PP.L hb' (hMz _).symm (hMz _).symm (hB' σ e e' _ _ (hMσ' e) (hMσ' e'))

  obtain ⟨Mc, hMc⟩ := exists_transport hb Mσ
  obtain ⟨Mv, hMv⟩ := exists_lift Pσ.m.cart (𝟙 _) (by rw [Category.id_comp]; exact hb.symm) Mσ
  obtain ⟨Mu, hMu⟩ := exists_lift m'.cart (spMap σ) hb'.symm Mσ'
  have hv₀ : lf (Mv.pt x) ≫ Pσ.m.φ = lf (Mc.pt x) := (hMv x).trans (hMc x).symm
  have h3 := GlobalTheory.T.abelian_part_maps_compatible_left E H X t L₁ L e₂ z₁ z hz P₁ P₂ mK2 mB2 c1 c2 t' tK m' mP w hw hw' B.carrier B'.carrier
    MB MB' f hf σ Pσ mKσ mBσ d1 d2 Mσ hMσ Mσ' hMσ' x (Mv.pt x) (Mu.pt (f.lTensor (ComplexAt σ) x)) (hMv x) (hMu _)

  have hUz : lf (Mu.pt (f.lTensor (ComplexAt σ) x)) ≫ m'.φ = lf (Mz.pt (f.lTensor (ComplexAt σ) x)) :=
    (hMu _).trans (hMz _).symm
  have a1 := ((GlobalTheory.T.hodge_inner_product_pullback_unique E H (Sp L) (Sp (𝓞 L)) tK t' (spMap (algebraMap (𝓞 L) L)) m' (spMap σ)
    (Mu.pt (f.lTensor (ComplexAt σ) x)) (Mu.pt (f.lTensor (ComplexAt σ) x))
    (Mz.pt (f.lTensor (ComplexAt σ) x)) (Mz.pt (f.lTensor (ComplexAt σ) x)) hUz hUz).1 _).2
    (h2 (f.lTensor (ComplexAt σ) x) (f.lTensor (ComplexAt σ) x))
  obtain ⟨U, hU⟩ := exists_push mP.cart (spMap σ) (Mu.pt (f.lTensor (ComplexAt σ) x))
  obtain ⟨Vv, hV⟩ := exists_push mBσ.cart (𝟙 _) (Mv.pt x ≫ Pσ.τ.q ≫ Pσ.e.hom)
  have a2 := ((GlobalTheory.T.hodge_inner_product_pullback_unique E H (Sp L) (Sp L₁) tK P₁.tB (spMap e₂) mP (spMap σ)
    (Mu.pt (f.lTensor (ComplexAt σ) x)) (Mu.pt (f.lTensor (ComplexAt σ) x)) U U hU hU).1 _).1 a1
  have hUV : lf U = lf Vv := hU.symm.trans (Eq.trans h3 hV)
  have a3 := ((GlobalTheory.T.hodge_inner_product_pullback_unique E H (Sp ℂ) (Sp L₁) Pσ.tB P₁.tB (spMap (σ.comp e₂)) mBσ (𝟙 _)
    (Mv.pt x ≫ Pσ.τ.q ≫ Pσ.e.hom) (Mv.pt x ≫ Pσ.τ.q ≫ Pσ.e.hom) Vv Vv hV hV).1 _).2
    (hodge_congr P₁.tB.PP.L hb2 hUV hUV a2)
  have h5 := hQ (spMap (σ.comp e₂) ≫ z₁) Pσ (Mv.pt x) (Mc.pt x) _ (Mv.tan x) hv₀ a3
  have h6 : h.ip _ (Mc.pt x) (Mc.pt x) = (B.metric.form σ).inner x x := by
    rw [h1]
    exact ip_congr h.ip hb.symm (hMc x) (hMc x)
  rw [h6] at h5
  exact h5
