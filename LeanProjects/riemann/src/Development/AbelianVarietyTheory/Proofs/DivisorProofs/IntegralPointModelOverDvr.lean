import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecValAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralFrameExtensionExists
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SemiAbelianDvrExtensionsIsoCompatible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentFrameBaseChange
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartFlagBaseHolds

set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel

noncomputable section

namespace GlobalTheory.ModelFrameCompare

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem isCombAtG_push {S₀ S₁ : Scheme.{0}} {t' : SAB H S₁} {t : SAB H S₀} {f : S₁ ⟶ S₀} (mm : SABMap t' t f)
    {R : Type} [CommRing R] (x : Sp R ⟶ S₁) {n : ℕ} {v : Fin n → (Sp (DualNumber R) ⟶ t'.G.left)} {a : Fin n → R}
    {w : Sp (DualNumber R) ⟶ t'.G.left} (h : IsCombAtG t' x v a w) :
    IsCombAtG t (x ≫ f) (fun i => v i ≫ mm.φ) a (w ≫ mm.φ) := by
  obtain ⟨B, hB⟩ := GlobalTheory.Exist.FlagBaseChange.exists_pointEquiv mm.cart
    (spMap (algebraMap R (DualNumber R)) ≫ x) (spMap (algebraMap R (DualNumber R)) ≫ x ≫ f) (Category.assoc _ _ _)
  obtain ⟨u, hu, hw⟩ := h
  refine ⟨fun i => B (u i), fun i => ?_, ?_⟩
  · rw [hB, hu, Category.assoc]
  · have e : B (List.ofFn u).prod = (List.ofFn fun i => B (u i)).prod := by
      rw [map_list_prod, List.map_ofFn]
      rfl
    rw [← e, hB, hw]

theorem isCombAtG_reflect {S₀ S₁ : Scheme.{0}} {t' : SAB H S₁} {t : SAB H S₀} {f : S₁ ⟶ S₀} (mm : SABMap t' t f)
    {R : Type} [CommRing R] (x : Sp R ⟶ S₁) {n : ℕ} (v : Fin n → (Sp (DualNumber R) ⟶ t'.G.left))
    (hv : ∀ i, v i ≫ t'.G.hom = spMap (algebraMap R (DualNumber R)) ≫ x) {a : Fin n → R}
    {w : Sp (DualNumber R) ⟶ t.G.left} (h : IsCombAtG t (x ≫ f) (fun i => v i ≫ mm.φ) a w) :
    ∃ w' : Sp (DualNumber R) ⟶ t'.G.left, w' ≫ mm.φ = w ∧ IsCombAtG t' x v a w' := by
  obtain ⟨B, hB⟩ := GlobalTheory.Exist.FlagBaseChange.exists_pointEquiv mm.cart
    (spMap (algebraMap R (DualNumber R)) ≫ x) (spMap (algebraMap R (DualNumber R)) ≫ x ≫ f) (Category.assoc _ _ _)
  obtain ⟨u, hu, hw⟩ := h
  have hBs : ∀ z, (B.symm z).left ≫ mm.φ = z.left := fun z => by rw [← hB, B.apply_symm_apply]
  refine ⟨(B.symm (List.ofFn u).prod).left, by rw [hBs, hw], fun i => B.symm (u i), fun i => ?_, ?_⟩
  · refine mm.cart.1.hom_ext ?_ ?_
    · rw [hBs, hu, Category.assoc]
    · rw [Over.w (B.symm (u i)), Category.assoc, hv, ← Category.assoc, GlobalTheory.Exist.FlagBaseChange.epsMul_over]
      rfl
  · rw [map_list_prod, List.map_ofFn]
    rfl

theorem exists_sabMap_congr {S₀ S₁ : Scheme.{0}} {t' : SAB H S₁} {t : SAB H S₀} {f f' : S₁ ⟶ S₀} (mm : SABMap t' t f)
    (h : f = f') : ∃ mm' : SABMap t' t f', mm'.φ = mm.φ := by
  subst h
  exact ⟨mm, rfl⟩

end GlobalTheory.ModelFrameCompare

namespace GlobalTheory.ModelFrameCompare

set_option maxHeartbeats 1000000 in

theorem images_eigenBasis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l l' : Level H) (Xo : Moduli Dw l) (Xo' : Moduli Dw l') (c : Coeff l) (c' : Coeff l') (W : ValuationSubring ℂ) (Y : Model Xo' c' (c'.V W).subtype) (r : Xo'.XF c' ⟶ Xo.XF c) (ν : SABMap Y.oF.t Xo.univ.t (r ≫ pullback.fst _ _)) (σ : E →+* ℂ) (T : CDVR) (io : c.F →+* T.Fr) (y₀ : IntFr Xo c T io) (xV : Sp T.V ⟶ Y.X) (yy : Sp T.Fr ⟶ Xo'.XF c'), yy ≫ Y.j = spMap (algebraMap T.V T.Fr) ≫ xV → (letI := io.toAlgebra; GlobalTheory.AllWt.ptF y₀.1 = yy ≫ r) → ∃ v : Fin (Dw.mult σ) → (Sp (DualNumber T.V) ⟶ Y.t.G.left), (∀ j, IsTanAtG Y.t xV (v j)) ∧ (∀ u : Sp (DualNumber T.V) ⟶ Y.t.G.left, IsTanAtG Y.t xV u → (∀ (a : 𝓞 E) (z : T.V), algebraMap T.V T.Fr z = io (embK c σ a) → u ≫ (Y.t.act.act a).left = spMap (epsMul z) ≫ u) → ∃ cf : Fin (Dw.mult σ) → T.V, IsCombAtG Y.t xV v cf u) ∧ ∀ (cf : Fin (Dw.mult σ) → T.V) (u : Sp (DualNumber T.V) ⟶ Y.t.G.left) (w : Sp (DualNumber T.Fr) ⟶ Y.oF.t.G.left), IsCombAtG Y.t xV v cf u → w ≫ Y.m.φ = spMap (dualMap (algebraMap T.V T.Fr)) ≫ u → (letI := io.toAlgebra; IsCombAt y₀.1.x (y₀.1.u σ) (fun j => algebraMap T.V T.Fr (cf j)) (w ≫ ν.φ)) := by
  intro E _ _ _ H Dw l l' Xo Xo' c c' W Y r ν σ T io y₀ xV yy hxV hpt
  let _ := io.toAlgebra
  obtain ⟨G₂, ⟨m⟩⟩ : ∃ G : SAB H (Sp T.V), Nonempty (SABMap G Y.t xV) := by
    obtain ⟨PP', cub, sym, adj, prim, m, -⟩ := sabPull ReciprocityTheory.ChartRestriction.G.Out.CubePf.cubePull xV Y.t
    exact ⟨_, ⟨m⟩⟩
  obtain ⟨t₂, n₀, n₂, m', -, h2⟩ := GlobalTheory.ThetaFrameCheck.genFibre_tied Xo' c' T _ _ Y xV yy hxV G₂ m
  obtain ⟨n₁, hn₁⟩ := sabComp pullCubComp E H _ _ _ Xo.univ.t Y.oF.t t₂ _ yy ν m'
  obtain ⟨G, t', m1, m2, ⟨ub, ht, he, hb, hl⟩, -⟩ := y₀.2.2
  have hx : y₀.1.x = yy ≫ r ≫ pullback.fst _ _ := by
    rw [← Category.assoc, ← hpt]
    exact (pullback.lift_fst _ _ _).symm
  obtain ⟨m1', hm1'⟩ := exists_sabMap_congr m1 hx
  obtain ⟨k, n, hk1, hk2⟩ := GlobalTheory.sab_extensions_iso E H Dw l Xo T.V T.Fr _ G G₂ t' t₂ m1' m2 n₁ n₂
  obtain ⟨nm, hnm⟩ := sabComp pullCubComp E H _ _ _ Y.t G₂ G xV (𝟙 _) m n
  obtain ⟨q₀, hq₀⟩ := exists_sabMap_congr nm (Category.id_comp xV)
  rw [hnm] at hq₀
  obtain ⟨B, hB, hBt, hBe, hBc⟩ := GlobalTheory.FactorDepth.Extension.exists_tanEquiv q₀
  refine ⟨fun j => (B (ub σ j)).left, fun j => (hBt _).2 (ht σ j), ?_, ?_⟩
  · intro u hu hue
    obtain ⟨w', hw'⟩ := B.surjective (ovT hu)
    have e : u = (B w').left := by rw [hw']; rfl
    subst e
    obtain ⟨cf, hcf, -⟩ := hb σ w' ((hBt _).1 hu) fun a z hz => (hBe _ a z).1 (hue a z hz)
    exact ⟨cf, (hBc _ _ cf w').2 hcf⟩
  · intro cf u w hc hw
    have h3 := GlobalTheory.LocM.Cht.FlagBase.isCombAtG_bc Y.t (algebraMap T.V T.Fr) hc
    obtain ⟨q, hq⟩ := sabComp pullCubComp E H _ _ _ Y.t Y.oF.t t₂ _ yy Y.m m'
    choose u' hu1 hu2 using hl σ
    have hov : ∀ j, u' j ≫ t'.G.hom = spMap (algebraMap T.Fr (DualNumber T.Fr)) := by
      intro j
      apply spMap_frac_cancel (V := T.V)
      rw [Category.assoc, ← m2.cart.1.w, ← Category.assoc, hu2, Category.assoc, Over.w (ub σ j), spMap_comp',
        ← dualMap_comp_alg, ← spMap_comp']
      rfl
    have hov' : ∀ j, (u' j ≫ k.φ) ≫ t₂.G.hom = spMap (algebraMap T.Fr (DualNumber T.Fr)) ≫ 𝟙 _ := by
      intro j
      rw [Category.assoc, k.cart.1.w, ← Category.assoc, hov]
    have hvec : ∀ j, spMap (dualMap (algebraMap T.V T.Fr)) ≫ (B (ub σ j)).left = (u' j ≫ k.φ) ≫ q.φ := by
      intro j
      rw [hB, hq₀, hq, ← Category.assoc, ← hu2, Category.assoc, ← Category.assoc m2.φ, hk2]
      simp only [Category.assoc, h2]
    have hpt' : spMap (algebraMap T.V T.Fr) ≫ xV = 𝟙 _ ≫ yy ≫ Y.jQ ≫ pullback.fst _ _ := by
      rw [Category.id_comp, ← hxV]; rfl
    have h4 : IsCombAtG Y.t (𝟙 _ ≫ yy ≫ Y.jQ ≫ pullback.fst _ _) (fun j => (u' j ≫ k.φ) ≫ q.φ)
        (fun j => algebraMap T.V T.Fr (cf j)) (w ≫ Y.m.φ) := by
      rw [← hpt', hw]
      simpa only [hvec] using h3
    obtain ⟨w₂, hw₂, hc₂⟩ := isCombAtG_reflect q (𝟙 _) (fun j => u' j ≫ k.φ) hov' h4
    have hw₂' : w₂ ≫ m'.φ = w := by
      refine Y.m.cart.1.hom_ext ?_ ?_
      · rw [Category.assoc, ← hq, hw₂]
      · have := GlobalTheory.TriplesAlong.isOpenImmersion_j W Y
        have hmono : Mono Y.j := inferInstance
        have e2 : w₂ ≫ t₂.G.hom = spMap (algebraMap T.Fr (DualNumber T.Fr)) ≫ 𝟙 _ := by
          obtain ⟨uu, -, hh⟩ := hc₂
          rw [← hh]; exact Over.w _
        have e1 : u ≫ Y.t.G.hom = spMap (algebraMap T.V (DualNumber T.V)) ≫ xV := by
          obtain ⟨uu, -, hh⟩ := hc
          rw [← hh]; exact Over.w _
        rw [Category.assoc, m'.cart.1.w, ← Category.assoc, e2, Category.comp_id]
        apply hmono.right_cancellation
        have e3 : spMap (dualMap (algebraMap T.V T.Fr)) ≫ spMap (algebraMap T.V (DualNumber T.V)) ≫ xV =
            spMap (algebraMap T.Fr (DualNumber T.Fr)) ≫ yy ≫ Y.j := by
          rw [← Category.assoc, spMap_comp', dualMap_comp_alg, ← spMap_comp', Category.assoc, hxV]
        show (spMap _ ≫ yy) ≫ Y.j = w ≫ Y.oF.t.G.hom ≫ Y.jQ ≫ pullback.fst _ _
        rw [← Y.m.cart.1.w, ← Category.assoc w, hw, Category.assoc (spMap _) u, e1, e3, Category.assoc]
    have h5 := isCombAtG_push n₁ (𝟙 _) hc₂
    have hv5 : (fun j => (u' j ≫ k.φ) ≫ n₁.φ) = y₀.1.u σ := by
      funext j
      rw [Category.assoc, hk1, hm1', hu1]
    rw [hv5, hn₁, ← Category.assoc w₂, hw₂', Category.id_comp, ← hx] at h5
    exact h5

end GlobalTheory.ModelFrameCompare
