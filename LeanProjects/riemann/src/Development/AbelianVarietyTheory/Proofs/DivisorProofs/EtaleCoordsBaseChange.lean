import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasBoundedPolesGlobalData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulBoundAtBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsConjFsBasisOfUnitary

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField Set MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX isPushout_sections)
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.ChowHt GlobalTheory.Vanishing GlobalTheory.TopForm GlobalTheory.ChartGlue

namespace GlobalTheory

section BaseChange

variable {k k' : Type} [CommRing k] [CommRing k'] {ρ : k →+* k'} {Y Y' : Scheme.{0}} {p : Y ⟶ Sp k}
  {p' : Y' ⟶ Sp k'} {r : Y' ⟶ Y} {σ : k →+* ℂ} {τ : k' →+* ℂ} {D : ℕ} {m : CxPts p' τ → CxPts p σ}

theorem CxPts.ev_appLE_of_comp (hm : ∀ z, (m z).1 = z.1 ≫ r) {U : Y.Opens} {W : Y'.Opens} (h : W ≤ r ⁻¹ᵁ U)
    (g : Γ(Y, U)) {z : CxPts p' τ} (hz : z ∈ ptsIn p' τ W) :
    ev p' τ W ((r.appLE U W h).hom g) z = ev p σ U g (m z) :=
  (ev_res h hz _).trans (ev_of_comp hm U g z).symm

def CxPts.bcMap (w : r ≫ p = p' ≫ spMap ρ) (τ : k' →+* ℂ) (z : CxPts p' τ) : CxPts p (τ.comp ρ) :=
  ⟨z.1 ≫ r, by
    rw [Category.assoc, w, ← Category.assoc, z.2, spMap, spMap, spMap, ← Spec.map_comp]
    rfl⟩

theorem CxPts.bijective_bcMap (H : IsPullback r p' p (spMap ρ)) (τ : k' →+* ℂ) :
    Function.Bijective (bcMap H.w τ) := by
  refine ⟨fun z z' h => Subtype.ext (H.hom_ext (congrArg Subtype.val h) (z.2.trans z'.2.symm)), fun y => ?_⟩
  have e : y.1 ≫ p = spMap τ ≫ spMap ρ := by
    rw [y.2, spMap, spMap, spMap, ← Spec.map_comp]
    rfl
  exact ⟨⟨H.lift y.1 (spMap τ) e, H.lift_snd _ _ _⟩, Subtype.ext (H.lift_fst _ _ _)⟩

theorem etale_coords_baseChange (H : IsPullback r p' p (spMap ρ)) {U : Y.Opens} (hU : IsAffineOpen U)
    {x : Fin D → Γ(Y, U)} (hx : (MvPolynomial.eval₂Hom (algX p U) x).Etale) :
    (MvPolynomial.eval₂Hom (algX p' (r ⁻¹ᵁ U ⊓ p' ⁻¹ᵁ ⊤))
      fun a => (r.appLE U _ inf_le_left).hom (x a)).Etale := by
  letI := ρ.toAlgebra
  letI := MvPolynomial.algebraMvPolynomial (R := k) (S := k') (σ := Fin D)
  have h₁ := (CommRingCat.isPushout_of_isPushout k k' (MvPolynomial (Fin D) k) (MvPolynomial (Fin D) k')).flip
  have h₂ := isPushout_sections p p' r H U hU
  have e₁ : CommRingCat.ofHom (algX p U) = CommRingCat.ofHom (algebraMap k (MvPolynomial (Fin D) k)) ≫
      CommRingCat.ofHom (MvPolynomial.eval₂Hom (algX p U) x) := by
    ext a
    exact (MvPolynomial.eval₂Hom_C _ _ a).symm
  have e₂ : CommRingCat.ofHom (algX p' (r ⁻¹ᵁ U ⊓ p' ⁻¹ᵁ ⊤)) =
      CommRingCat.ofHom (algebraMap k' (MvPolynomial (Fin D) k')) ≫
      CommRingCat.ofHom (MvPolynomial.eval₂Hom (algX p' (r ⁻¹ᵁ U ⊓ p' ⁻¹ᵁ ⊤))
        fun a => (r.appLE U _ inf_le_left).hom (x a)) := by
    ext a
    exact (MvPolynomial.eval₂Hom_C _ _ a).symm
  rw [e₁, e₂] at h₂
  have h₃ := h₂.of_left (CommRingCat.hom_ext (MvPolynomial.ringHom_ext (fun a => ?_) fun a => ?_)) h₁
  · have := RingHom.isStableUnderCobaseChange_toMorphismProperty_iff.2 RingHom.Etale.isStableUnderBaseChange
    exact MorphismProperty.of_isPushout (P := RingHom.toMorphismProperty RingHom.Etale) h₃.flip hx
  · change (r.appLE U _ _).hom (MvPolynomial.eval₂Hom _ _ (MvPolynomial.C a)) =
      MvPolynomial.eval₂Hom _ _ (MvPolynomial.map ρ (MvPolynomial.C a))
    rw [MvPolynomial.map_C, MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_C]
    exact RingHom.congr_fun (appLE_comp_algX H.w (inf_le_left : r ⁻¹ᵁ U ⊓ p' ⁻¹ᵁ ⊤ ≤ _)) a
  · change (r.appLE U _ _).hom (MvPolynomial.eval₂Hom _ _ (MvPolynomial.X a)) =
      MvPolynomial.eval₂Hom _ _ (MvPolynomial.map ρ (MvPolynomial.X a))
    rw [MvPolynomial.map_X, MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_X']

theorem AlgChart.exists_baseChange (H : IsPullback r p' p (spMap ρ)) (hm : ∀ z, (m z).1 = z.1 ≫ r)
    (c : AlgChart p σ D) {z : CxPts p' τ} (hz : m z ∈ c.e.source) :
    ∃ c' : AlgChart p' τ D, z ∈ c'.e.source ∧ ∃ h : c'.U ≤ r ⁻¹ᵁ c.U,
      ∀ a, c'.x a = (r.appLE c.U c'.U h).hom (c.x a) := by
  have hU : IsAffineOpen (r ⁻¹ᵁ c.U ⊓ p' ⁻¹ᵁ ⊤) := by
    rw [show r ⁻¹ᵁ c.U ⊓ p' ⁻¹ᵁ ⊤ = r ⁻¹ᵁ c.U from inf_top_eq _]
    exact isAffineOpen_preimage_of_isPullback H c.affine
  obtain ⟨⟨e, U, hU', x, hx, h₁, h₂, h₃⟩, hy, hU', hx'⟩ := AlgChart.exists_of_etale hU _
    (etale_coords_baseChange H c.affine c.etale)
    (mem_ptsIn_inf.2 ⟨(mem_ptsIn_preimage hm).2 (c.source_subset hz), mem_ptsIn_top⟩ : z ∈ ptsIn p' τ _)
  dsimp only at hU'
  subst hU'
  dsimp only at hx'
  subst hx'
  exact ⟨_, hy, inf_le_left, fun _ => rfl⟩

variable [SmoothOfRelativeDimension D p] [SmoothOfRelativeDimension D p']

theorem AlgChart.rv_baseChange (H : IsPullback r p' p (spMap ρ)) (hm : ∀ z, (m z).1 = z.1 ≫ r) (K : CanonLB p D)
    {c : AlgChart p σ D} {c' : AlgChart p' τ D} (h : c'.U ≤ r ⁻¹ᵁ c.U)
    (hx : ∀ a, c'.x a = (r.appLE c.U c'.U h).hom (c.x a)) {a : (K.baseChange H).bundle.ι} {z : CxPts p' τ}
    (hz : z ∈ ptsIn p' τ c'.U) (ha : z ∈ ptsIn p' τ ((K.baseChange H).bundle.U a)) :
    rv τ c'.isFrame ((K.baseChange H).isFrame a) z = rv σ c.isFrame (K.isFrame (a PUnit.unit)) (m z) := by
  have hl : (K.baseChange H).bundle.U a ≤ r ⁻¹ᵁ K.bundle.U (a PUnit.unit) := (GlobalTheory.chartPullPull K.bundle r).le a
  have e := c.rv_mul_jacobian K ((mem_ptsIn_preimage hm).1 (ptsIn_mono h hz))
    ((mem_ptsIn_preimage hm).1 (ptsIn_mono hl ha))
  have e' := c'.rv_mul_jacobian (K.baseChange H) hz ha
  have hW : (K.baseChange H).bundle.U a ⊓ c'.U ≤ r ⁻¹ᵁ (K.bundle.U (a PUnit.unit) ⊓ c.U) := inf_le_inf hl h
  have e₂ := K.jacobian_baseChange H a inf_le_left (W := (K.baseChange H).bundle.U a ⊓ c'.U) inf_le_left hW
    fun i => resG Y inf_le_right (c.x i)
  rw [← ev_appLE_of_comp hm hW _ (mem_ptsIn_inf.2 ⟨ha, hz⟩), ← e₂] at e
  simp only [hx, LB.resG_appLE] at e'
  simp only [LB.appLE_resG] at e
  exact left_inv_eq_right_inv e' ((mul_comm _ _).trans e)

variable {B : LB Y} {B' : LB Y'}

theorem AnRead.topInt_baseChange [SecondCountableTopology (CxPts p σ)] [SecondCountableTopology (CxPts p' τ)]
    (H : IsPullback r p' p (spMap ρ)) (hm : ∀ z, (m z).1 = z.1 ≫ r) (hb : Function.Bijective m)
    (R : AnRead p σ D) (R' : AnRead p' τ D) (K : CanonLB p D) (b : ChartPull B' B r)
    {φ : Weight p σ B} {φ' : Weight p' τ B'}
    (hφ : ∀ i z, z ∈ ptsIn p' τ (B'.U i) → φ'.φ i z = φ.φ (b.idx i) (m z))
    {f : (tens K.bundle B).ι → CxPts p σ → ℂ} (hf : f ∈ fibSec p σ _)
    {f' : (tens (K.baseChange H).bundle B').ι → CxPts p' τ → ℂ}
    (hf' : ∀ a i z, z ∈ ptsIn p' τ ((K.baseChange H).bundle.U a) → z ∈ ptsIn p' τ (B'.U i) →
      f' (a, i) z = f (a PUnit.unit, b.idx i) (m z)) :
    R'.topInt (K.baseChange H) φ' f' = R.topInt K φ f := by
  have hc := continuous_of_comp hm
  have key (z : CxPts p' τ) : ∃ S, IsOpen S ∧ m z ∈ S ∧ ∀ A, MeasurableSet A → A ⊆ S →
      R'.topMeasure (K.baseChange H) φ' f' (m ⁻¹' A) = R.topMeasure K φ f A := by
    obtain ⟨c, hz⟩ := AlgChart.exists_mem_source (D := D) (m z)
    obtain ⟨c', hz', h, hx⟩ := c.exists_baseChange H hm hz
    have he (w) (h₁ : w ∈ c'.e.source) (h₂ : m w ∈ c.e.source) : c.e (m w) = c'.e w := by
      ext a
      rw [c.apply_eq _ h₂, c'.apply_eq _ h₁, hx, ev_appLE_of_comp hm h _ (c'.source_subset h₁)]
    have ho := isOpen_over c'.e (c.e.open_source.preimage hc)
    refine ⟨_, c.e.isOpen_inter_preimage ho, ⟨hz, ?_⟩, fun A hA hAS => ?_⟩
    · rw [mem_preimage, he z hz' hz]
      exact mem_over c'.e hz' hz
    have hs (w) (hw : m w ∈ A) : w ∈ c'.e.source := by
      obtain ⟨h₁, h₂, h₃⟩ := hAS hw
      have h₄ := c'.e.map_target h₂
      rw [hb.1 (c.e.injOn h₁ h₃ ((he _ h₄ h₃).trans (c'.e.right_inv h₂)).symm)]
      exact h₄
    have hA' : MeasurableSet (m ⁻¹' A) := hc.measurable hA
    have hi : c.e '' A = c'.e '' (m ⁻¹' A) := by
      conv_lhs => rw [← image_preimage_eq A hb.2, image_image]
      exact image_congr fun w hw => he w (hs w hw) (hAS hw).1
    rw [R'.topMeasure_apply _ _ _ c' hA' hs, R.topMeasure_apply _ _ _ c hA (hAS.trans inter_subset_left), hi]
    refine setLIntegral_congr_fun (measurableSet_image c'.e hA' hs) ?_
    rintro _ ⟨w, hw, rfl⟩
    have h₁ := hs w hw
    have h₂ := (hAS hw).1
    have ha := mem_pick (K.baseChange H).isLB w
    have hi := mem_pick φ'.isLB w
    dsimp only
    rw [c'.e.left_inv h₁, ← he w h₁ h₂, c.e.left_inv h₂, c.topDens_eq K φ hf h₂
      ((mem_ptsIn_preimage hm).1 (ptsIn_mono ((GlobalTheory.chartPullPull K.bundle r).le _) ha))
      ((mem_ptsIn_preimage hm).1 (ptsIn_mono (b.le _) hi)), AlgChart.topDens, AlgChart.topCoeff,
      hφ _ _ hi, hf' _ _ _ ha hi, AlgChart.rv_baseChange H hm K h hx (c'.source_subset h₁) ha]
    rfl
  choose S hS hzS hμ using key
  have e : (R'.topMeasure (K.baseChange H) φ' f').map m = R.topMeasure K φ f :=
    ext_of_cover S hS (fun y => by obtain ⟨z, rfl⟩ := hb.2 y; exact ⟨z, hzS z⟩) fun z A hA h =>
      (Measure.map_apply hc.measurable hA).trans (hμ z A hA h)
  rw [topInt, topInt, ← e, Measure.map_apply hc.measurable MeasurableSet.univ, preimage_univ]

omit [SmoothOfRelativeDimension D p] [SmoothOfRelativeDimension D p'] in

theorem Vanishing.cval_pullChart (hm : ∀ z, (m z).1 = z.1 ≫ r) (b : ChartPull B' B r) (w : r ≫ p = p' ≫ spMap ρ)
    (f : H0 p B ⊤) {i : B'.ι} {z : CxPts p' τ} (hz : z ∈ ptsIn p' τ (B'.U i)) :
    cval τ (pullChart (W := ⊤) b w le_top f) i z = cval σ f (b.idx i) (m z) :=
  ev_appLE_of_comp hm (inf_le_inf le_top (b.le i)) _ (mem_ptsIn_inf.2 ⟨mem_ptsIn_top, hz⟩)

end BaseChange

variable {F : Type} [Field F] [NumberField F] (E : Type) [Field E] [NumberField E] [Algebra F E]

theorem Adelic.HermSys.weight_baseChange (T : Adelic.HermSys F) (hb : T.BasePointFree) (hh : T.Hermitian)
    (hb' : (T.baseChange E).BasePointFree) (hh' : (T.baseChange E).Hermitian) {τ : E →+* ℂ}
    {m : CxPts (T.baseChange E).str τ → CxPts T.str (τ.comp (algebraMap F E))}
    (hm : ∀ z, (m z).1 = z.1 ≫ T.bcFst E) (i : (T.baseChange E).L.ι) {z : CxPts (T.baseChange E).str τ}
    (hz : z ∈ ptsIn _ τ ((T.baseChange E).L.U i)) :
    ((T.baseChange E).weight hb' hh' τ).φ i z =
      (T.weight hb hh (τ.comp (algebraMap F E))).φ (i PUnit.unit) (m z) := by
  rw [Adelic.HermSys.weight_φ, Adelic.HermSys.weight_φ]
  exact congrArg (fun v => Real.log (archSize (T.A (τ.comp (algebraMap F E))) v ^ 2)) (funext fun j =>
    ev_appLE_of_comp hm ((GlobalTheory.chartPullPull T.L (T.bcFst E)).le i) _ hz)

namespace HilbertSamuel

theorem Geo.sqInt_baseChange (G : Geo F) (j : ℕ) (τ : E →+* ℂ) {ι : Type*} [Fintype ι] (c : ι → ℂ)
    (f : ι → H0 G.str (G.adj₂ j) ⊤) :
    (G.baseChange E).sqInt j τ (∑ i, c i • cval τ (G.toExt₂ E j (f i))) =
      G.sqInt j (τ.comp (algebraMap F E)) (∑ i, c i • cval (τ.comp (algebraMap F E)) (f i)) := by
  have H := G.isPullback_fst E
  have hm : ∀ z, (bcMap H.w τ z).1 = z.1 ≫ G.fst E := fun _ => rfl
  have : SmoothOfRelativeDimension G.D (G.baseChange E).str := (G.baseChange E).smooth
  refine AnRead.topInt_baseChange H hm (bijective_bcMap H τ) _ _ G.K
    (chartPullTwist (GlobalTheory.chartPullPull G.L₂ _) (GlobalTheory.chartPullPull G.L _) (j + G.D)) (fun i z hz => ?_)
    (assocVal_mem_holSec (R := AnRead.all _ _ G.D)
      (Submodule.sum_mem _ fun _ _ => Submodule.smul_mem _ _ (cval_mem_holSec _ _ _))).1 fun a i z ha hi => ?_
  · have h := mem_ptsIn_inf.1 hz
    refine congrArg₂ (· + ·) (G.second.weight_baseChange E _ _ _ _ hm _ h.1)
      ((Weight.zpow_φ _ _ _ _).trans (Eq.trans (congrArg _ ?_) (Weight.zpow_φ _ _ _ _).symm))
    exact G.toHermSys.weight_baseChange E _ _ _ _ hm _ (mem_pow_iff.1 h.2)
  · have h := mem_ptsIn_inf.1 hi
    have hz : z ∈ ptsIn _ τ (((G.baseChange E).adj₂ j).U ((a, i.1), i.2)) :=
      mem_ptsIn_inf.2 ⟨mem_ptsIn_inf.2 ⟨ha, h.1⟩, h.2⟩
    change (∑ l, c l • cval τ (G.toExt₂ E j (f l))) ((a, i.1), i.2) z =
      (∑ l, c l • cval _ (f l)) ((G.chartAdj₂ E j).idx ((a, i.1), i.2)) (bcMap H.w τ z)
    simp only [Finset.sum_apply, Pi.smul_apply]
    exact ((congrFun (Finset.sum_apply _ _ _) z).trans (Finset.sum_apply _ _ _)).trans
      (Finset.sum_congr rfl fun l _ => congrArg (c l • ·) (cval_pullChart hm (G.chartAdj₂ E j) H.w (f l) hz))

theorem Data.IntegralBound.baseChange {X : Data F} {β κ : (F →+* ℂ) → ℝ} (h : X.IntegralBound β κ) :
    (X.baseChange E).IntegralBound (fun τ => β (τ.comp (algebraMap F E))) fun τ => κ (τ.comp (algebraMap F E)) := by
  intro j hj τ m c f
  have := finite_top X.geom.alg.variety.proj (isLB_tw (isLB_tens X.K.isLB X.isLB₂) X.isLB ((j : ℤ) + X.D))
  let b := Module.finBasis F (H0 X.str (X.adj₂ j) ⊤)
  let b' := (X.isExtension_toExt₂ E j).basis b
  obtain ⟨a, rfl⟩ : ∃ a : Fin m → Fin _ → E, f = fun i => ∑ l, a i l • X.toExt₂ E j (b l) :=
    ⟨fun i l => b'.repr (f i) l, funext fun i => (b'.sum_repr (f i)).symm.trans
      (Finset.sum_congr rfl fun l _ => congrArg _ (IsExtension.basis_apply _ _ _))⟩
  have e₁ : (fun i => (X.baseChange E).inclE hj (∑ l, a i l • X.toExt₂ E j (b l))) =
      fun i => ∑ l, a i l • X.toExtV E j (X.inclE hj (b l)) := funext fun i =>
    (map_sum _ _ _).trans (Finset.sum_congr rfl fun l _ =>
      (map_smul _ _ _).trans (congrArg _ (X.toExtV_inclE E hj _).symm))
  have e₂ : ∑ i, c i • cval τ (∑ l, a i l • X.toExt₂ E j (b l)) =
      ∑ l, (∑ i, c i * τ (a i l)) • cval τ (X.toExt₂ E j (b l)) := by
    simp only [map_sum, map_smulₛₗ, Finset.smul_sum, Finset.sum_smul, smul_smul]
    exact Finset.sum_comm
  refine (congrArg (csq _ τ c) e₁).trans_le (((csq_comb _ _ _ _ _).trans
    (csq_extend (X.isExtension_extMap E j) _ τ _ _)).trans_le ((h j hj _ _ _ b).trans_eq (congrArg _ ?_)))
  exact congrArg ENNReal.toReal ((congrArg _ e₂).trans (X.sqInt_baseChange E j τ _ b)).symm

end HilbertSamuel

end GlobalTheory
