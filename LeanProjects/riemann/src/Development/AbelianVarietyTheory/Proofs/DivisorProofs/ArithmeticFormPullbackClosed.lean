import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsL2OnDiagonalOfIsL2Metric
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousAndExistsConjChart
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConjCompatibleLieMetric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointsMapHolomorphicStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolAtlasIsFormPullbackHolomorphicStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolAtlasPullbackEqChartExpressionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DelDbarCommPullbackOfSmoothDelDbarStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolAtlasIsFormDelDbarSmoothStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackPreservesFormTypeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackPreservesRealFormStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateChartDerivativeStatement

open CategoryTheory AlgebraicGeometry Set Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.CxForm
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.GoodMetric (coordVec)
open scoped ComplexConjugate

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.PullArForm

theorem swap_pull_conj {n m : ℕ} (L L' : V n →L[ℂ] V m)
    (hL : ∀ b a, L' (coordVec b) a = conj (L (coordVec b) a)) (α : Alt m) :
    swap (pull L' α) = pull L (swap α) := by
  have e : swap.comp (pull L') = (pull L).comp (swap (n := m)) := by
    refine ExteriorAlgebra.hom_ext (LinearMap.ext fun u => ?_)
    simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, AlgHom.comp_apply, swap, pull,
      ExteriorAlgebra.map_apply_ι]
    congr 1
    funext i
    rcases i with b | b <;>
      simp [LinearMap.funLeft_apply, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, hL]
  exact congrArg (fun φ : Alt m →ₐ[ℂ] Alt n => φ α) e

theorem emb_eq_conj {k : Type} [CommRing k] {Y : Scheme.{0}} {q : Y ⟶ Sp k} {σ σ' : k →+* ℂ} (x : CxPts q σ)
    (x' : CxPts q σ') (e : x'.1 = spMap (starRingEnd ℂ) ≫ x.1) : σ' = (starRingEnd ℂ).comp σ := by
  have h1 : spMap σ' = spMap (starRingEnd ℂ) ≫ spMap σ := by
    rw [← x'.2, e, Category.assoc, x.2]
  have h2 : spMap (starRingEnd ℂ) ≫ spMap σ = spMap ((starRingEnd ℂ).comp σ) := by
    simp only [spMap, ← Spec.map_comp]; rfl
  have h3 := Spec.map_injective (h1.trans h2)
  exact congrArg CommRingCat.Hom.hom h3

theorem pullFld_isArForm (k : Type) [CommRing k] (X Y : Scheme.{0}) (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (D D' : ℕ)
    (h : IsRegVar p D) (h' : IsRegVar q D') (f : Y ⟶ X) (hf : f ≫ p = q) (j : ℕ) (κ : h.Fld) :
    h.IsArForm j κ → h'.IsArForm j (h.pullFld h' f hf κ) ∧ ∀ σ,
      ((h.atlas σ).del (κ σ) = 0 → (h'.atlas σ).del (h.pullFld h' f hf κ σ) = 0) ∧
      ((h.atlas σ).dbar (κ σ) = 0 → (h'.atlas σ).dbar (h.pullFld h' f hf κ σ) = 0) := by
  intro hκ
  haveI := h.isIntegral
  have hol : ∀ σ, (h.atlas σ).IsHolo (h'.atlas σ) (Points.PtsOver.map f hf (spMap σ)) := fun σ =>
    GlobalTheory.T.points_map_holomorphic k X p D h σ Y q D' h' f hf
  have loc : ∀ σ (x : (h'.atlas σ).Pt) (c : AlgChart p σ D)
      (hc : Points.PtsOver.map f hf (spMap σ) x.pt ∈ c.e.source),
      h.pullFld h' f hf κ σ x = pull (fderiv ℂ (c.e ∘ Points.PtsOver.map f hf (spMap σ) ∘ x.ch.symm) x.crd)
        (κ σ ⟨(c, _), hc⟩) :=
    fun σ x c hc => GlobalTheory.T.holAtlas_pullback_eq_chart_expression _ _ _ _ (h.atlas σ) (h'.atlas σ) _ (κ σ) (hol σ) (hκ.1 σ).1 x c hc
  refine ⟨⟨fun σ => ⟨GlobalTheory.T.holAtlas_isForm_pullback_holomorphic _ _ _ _ _ _ _ _ (hol σ) (hκ.1 σ).1, fun x => ?_⟩, ?_⟩, fun σ => ?_⟩
  · obtain ⟨c, hc⟩ := (h.atlas σ).cover (Points.PtsOver.map f hf (spMap σ) x.pt)
    rw [loc σ x c hc]
    exact ⟨GlobalTheory.T.pullback_preserves_form_type _ _ _ _ _ _ ((hκ.1 σ).2 _).1, GlobalTheory.T.pullback_preserves_real_form _ _ _ _ ((hκ.1 σ).2 _).2⟩
  · intro σ σ' x x' e hch
    obtain rfl := emb_eq_conj x.pt x'.pt e
    set F := Points.PtsOver.map f hf (spMap σ) with hFdef
    set F' := Points.PtsOver.map f hf (spMap ((starRingEnd ℂ).comp σ)) with hF'def
    obtain ⟨c, hc⟩ := (h.atlas σ).cover (F x.pt)
    change AlgChart p σ D at c
    let cP : CxPts p σ ≃ₜ CxPts p ((starRingEnd ℂ).comp σ) := ConjChart.conjPts p rfl
    let cQ : CxPts q σ ≃ₜ CxPts q ((starRingEnd ℂ).comp σ) := ConjChart.conjPts q rfl
    let c' : AlgChart p ((starRingEnd ℂ).comp σ) D := ConjChart.conjChart rfl c
    have conjPoint_val : ∀ y, (cP y).1 = spMap (starRingEnd ℂ) ≫ y.1 := fun _ => rfl
    have cQ_val : ∀ y, (cQ y).1 = spMap (starRingEnd ℂ) ≫ y.1 := fun _ => rfl
    have c'_apply : ∀ y, c'.e (cP y) = ConjChart.conjCoord D (c.e y) := fun y => by
      change ConjChart.conjCoord D (c.e (cP.symm (cP y))) = _
      rw [Homeomorph.symm_apply_apply]
    have c'_src : ∀ y, cP y ∈ c'.e.source ↔ y ∈ c.e.source := fun y => by
      change cP.symm (cP y) ∈ c.e.source ↔ _
      rw [Homeomorph.symm_apply_apply]
    have hFc : ∀ z, F' (cQ z) = cP (F z) := fun z => Subtype.ext (by
      rw [Points.PtsOver.map_val, conjPoint_val, Points.PtsOver.map_val, cQ_val, Category.assoc])
    have hx' : x'.pt = cQ x.pt := Subtype.ext e
    have hc' : F' x'.pt ∈ c'.e.source := by rw [hx', hFc, c'_src]; exact hc
    rw [loc _ x' c' hc', loc σ x c hc]
    have hκc := hκ.2 σ ((starRingEnd ℂ).comp σ) ⟨(c, F x.pt), hc⟩ ⟨(c', F' x'.pt), hc'⟩
      (by change (F' x'.pt).1 = _; rw [hx', hFc]; rfl)
      (fun z _ z' _ ez a => by
        obtain rfl : z' = cP z := Subtype.ext ez
        change c'.e (cP z) a = _
        rw [c'_apply]; rfl)
    have hv : ConjChart.conjCoord D' x'.crd = x.crd := by
      ext a
      have := hch x.pt x.2 x'.pt x'.2 e a
      simp [ConjChart.conjCoord, this]
    have hdiff : DifferentiableAt ℂ (c.e ∘ F ∘ x.ch.symm) x.crd := by
      have hs : IsOpen (x.ch.target ∩ x.ch.symm ⁻¹' (F ⁻¹' c.e.source)) :=
        x.ch.isOpen_inter_preimage_symm (c.e.open_source.preimage (hol σ).1)
      refine ((hol σ).2 x.1.1 c).differentiableAt (hs.mem_nhds ⟨x.ch.map_source x.2, ?_⟩)
      change F (x.ch.symm x.crd) ∈ c.e.source
      rw [x.ch.left_inv x.2]; exact hc
    have heq : (c'.e ∘ F' ∘ x'.ch.symm) =ᶠ[𝓝 x'.crd]
        fun w => ConjChart.conjCoord D ((c.e ∘ F ∘ x.ch.symm) (ConjChart.conjCoord D' w)) := by
      have hS : IsOpen (F' ⁻¹' c'.e.source ∩ cQ.symm ⁻¹' x.ch.source) :=
        (c'.e.open_source.preimage (hol _).1).inter (x.ch.open_source.preimage cQ.symm.continuous)
      have hN := x'.ch.isOpen_inter_preimage_symm hS
      have hmem : x'.crd ∈ x'.ch.target ∩ x'.ch.symm ⁻¹' (F' ⁻¹' c'.e.source ∩ cQ.symm ⁻¹' x.ch.source) := by
        refine ⟨x'.ch.map_source x'.2, ?_⟩
        change x'.ch.symm (x'.ch x'.pt) ∈ F' ⁻¹' c'.e.source ∩ cQ.symm ⁻¹' x.ch.source
        rw [x'.ch.left_inv x'.2]
        refine ⟨hc', ?_⟩
        change cQ.symm x'.pt ∈ x.ch.source
        rw [hx', Homeomorph.symm_apply_apply]; exact x.2
      filter_upwards [hN.mem_nhds hmem] with w hw
      obtain ⟨hwt, hw1, hw2⟩ := hw
      have hz'src : x'.ch.symm w ∈ x'.ch.source := x'.ch.map_target hwt
      generalize hzz : x'.ch.symm w = z' at hw1 hw2 hz'src
      obtain ⟨z, rfl⟩ : ∃ z, z' = cQ z := ⟨cQ.symm z', (cQ.apply_symm_apply z').symm⟩
      have hzs : z ∈ x.ch.source := by
        have : cQ.symm (cQ z) ∈ x.ch.source := hw2
        rwa [Homeomorph.symm_apply_apply] at this
      have hwz : x'.ch (cQ z) = w := by rw [← hzz, x'.ch.right_inv hwt]
      have hxz : x.ch z = ConjChart.conjCoord D' w := by
        ext a
        have := hch z hzs (cQ z) hz'src rfl a
        rw [hwz] at this
        simp [ConjChart.conjCoord, this]
      have hsymm : x.ch.symm (ConjChart.conjCoord D' w) = z := by rw [← hxz, x.ch.left_inv hzs]
      simp only [Function.comp_apply]
      rw [hsymm, hzz, hFc, c'_apply]
    have hT : ∀ b a, fderiv ℂ (c'.e ∘ F' ∘ x'.ch.symm) x'.crd (coordVec b) a =
        conj (fderiv ℂ (c.e ∘ F ∘ x.ch.symm) x.crd (coordVec b) a) := fun b a => by
      have := GlobalTheory.T.conjugate_chart_derivative _ _ _ _ x'.crd (by rw [hv]; exact hdiff) heq b a
      rwa [hv] at this
    rw [swap_pull_conj _ _ hT]
    exact (congrArg (pull _) hκc).trans (map_smul _ _ _)
  · have hF := (hκ.1 σ).1
    obtain ⟨hd, hdb⟩ := GlobalTheory.T.holAtlas_isForm_del_dbar_smooth _ _ _ (κ σ) hF
    obtain ⟨e1, e2⟩ := GlobalTheory.T.del_dbar_comm_pullback_of_smooth_del_dbar _ _ _ _ (h.atlas σ) (h'.atlas σ) _ (κ σ) (hol σ) hF hd hdb
    have z : (h.atlas σ).pullback (h'.atlas σ) (Points.PtsOver.map f hf (spMap σ)) 0 = 0 := by
      funext x; exact map_zero _
    refine ⟨fun h0 => ?_, fun h0 => ?_⟩
    · change (h'.atlas σ).del ((h.atlas σ).pullback _ _ _) = 0
      rw [e1, h0, z]
    · change (h'.atlas σ).dbar ((h.atlas σ).pullback _ _ _) = 0
      rw [e2, h0, z]

end GlobalTheory.PullArForm
