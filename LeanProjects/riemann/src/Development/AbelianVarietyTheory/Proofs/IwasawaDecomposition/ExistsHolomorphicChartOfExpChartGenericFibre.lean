import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLieBase
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgePeriodGram
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeChartBoundsOfSchurLemW
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PerValNeZero
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LieBase

open GlobalTheory.Points Filter Topology

section Transfer

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}
  {F : Type} [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) {X : Var F} {j : X.X ⟶ gen Z}
  (hj : j ≫ genStr Z ≫ spMap e.toRingHom = X.str)

theorem isOpenEmbedding_cxOf [IsOpenImmersion j] : IsOpenEmbedding (cxOf e σ hj) := by
  have hc : Continuous (cxOf e σ hj) :=
    continuous_induced_rng.2 ((continuous_comp (C := ℂ) j).comp continuous_subtype_val)
  refine ⟨IsEmbedding.of_comp hc continuous_subtype_val
    (((isOpenEmbedding_comp (C := ℂ) j).isEmbedding).comp IsEmbedding.subtypeVal), ?_⟩
  have hr : Set.range (cxOf e σ hj) = Subtype.val ⁻¹' Set.range fun x : Sp ℂ ⟶ X.X => x ≫ j := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x.1, rfl⟩
    · rintro ⟨x, hx⟩
      replace hx : x ≫ j = y.1 := hx
      refine ⟨⟨x, ?_⟩, Subtype.ext hx⟩
      rw [← hj, ← Category.assoc, hx, ← Category.assoc, y.2, ← Spec.map_comp]
      rfl
  rw [hr]
  exact (isOpenEmbedding_comp (C := ℂ) j).isOpen_range.preimage continuous_subtype_val

variable [IsOpenImmersion j]

theorem le_preimage_cxOf (W : X.X.Opens) {z : CxPts X.str (σ.comp e.toRingHom)}
    (hz : z ∈ ptsIn X.str (σ.comp e.toRingHom) W) : ⊤ ≤ (cxOf e σ hj z).1 ⁻¹ᵁ (j ''ᵁ W) :=
  le_preimage_comp z.1 j (j.preimage_image_eq W).ge hz

theorem ev_eq_valAt'_cxOf (W : X.X.Opens) (g : Γ(X.X, W)) {z : CxPts X.str (σ.comp e.toRingHom)}
    (hz : z ∈ ptsIn X.str (σ.comp e.toRingHom) W) :
    ev X.str (σ.comp e.toRingHom) W g z = valAt' (cxOf e σ hj z).1 (j ''ᵁ W) ((j.appIso W).inv.hom g) := by
  have hle : W ≤ j ⁻¹ᵁ j ''ᵁ W := (j.preimage_image_eq W).ge
  change valR z.1 W g = valR (z.1 ≫ j) (j ''ᵁ W) _
  rw [← valR_appLE z.1 j hle hz, ← CommRingCat.comp_apply, Scheme.Hom.appIso_inv_appLE]
  exact (valR_res z.1 le_rfl hz g).symm

end Transfer

open GlobalTheory.Points Filter Topology

theorem finrank_eq_of_differentiableAt {E₁ E₂ : Type} [NormedAddCommGroup E₁] [NormedSpace ℂ E₁]
    [NormedAddCommGroup E₂] [NormedSpace ℂ E₂] (Φ : OpenPartialHomeomorph E₁ E₂) {x : E₁} (hx : x ∈ Φ.source)
    (h₁ : DifferentiableAt ℂ Φ x) (h₂ : DifferentiableAt ℂ Φ.symm (Φ x)) :
    Module.finrank ℂ E₁ = Module.finrank ℂ E₂ := by
  have hl : (fderiv ℂ Φ.symm (Φ x)).comp (fderiv ℂ Φ x) = ContinuousLinearMap.id ℂ E₁ :=
    ((h₂.hasFDerivAt.comp x h₁.hasFDerivAt).congr_of_eventuallyEq
      (EventuallyEq.symm (Φ.eventually_left_inverse hx : Φ.symm ∘ Φ =ᶠ[𝓝 x] id))).unique (hasFDerivAt_id x)
  have h₁' : HasFDerivAt Φ (fderiv ℂ Φ x) (Φ.symm (Φ x)) := by
    rw [Φ.left_inv hx]
    exact h₁.hasFDerivAt
  have hr : (fderiv ℂ Φ x).comp (fderiv ℂ Φ.symm (Φ x)) = ContinuousLinearMap.id ℂ E₂ :=
    ((h₁'.comp (Φ x) h₂.hasFDerivAt).congr_of_eventuallyEq
      (EventuallyEq.symm (Φ.eventually_right_inverse' hx : Φ ∘ Φ.symm =ᶠ[𝓝 (Φ x)] id))).unique (hasFDerivAt_id (Φ x))
  exact (ContinuousLinearEquiv.equivOfInverse (fderiv ℂ Φ x) (fderiv ℂ Φ.symm (Φ x))
    (fun v => DFunLike.congr_fun hl v) (fun v => DFunLike.congr_fun hr v)).toLinearEquiv.finrank_eq

section Transfer

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}
  {σ : c.F →+* ℂ}

theorem differentiableAt_valAt'_symm {n g : ℕ} {ch₀ : OpenPartialHomeomorph (CxPts (genStr Z) σ) (Fin n → ℂ)}
    {ex : ExpMaps Z σ g} (h : IsExpChart ch₀ ex) (U : (gen Z).Opens) (f : Γ(gen Z, U)) {b : Fin n → ℂ}
    (hb : b ∈ ch₀.target) (hU : ⊤ ≤ (ch₀.symm b).1 ⁻¹ᵁ U) :
    DifferentiableAt ℂ (fun b => valAt' (ch₀.symm b).1 U f) b :=
  (h.2.2.1 U f).2.differentiableAt ((h.2.2.1 U f).1.mem_nhds ⟨hb, hU⟩)

end Transfer

theorem exists_holoChart_of_expChart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (X : Var F) (j : X.X ⟶ gen T.Z) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsOpenImmersion j → ∀ (y : GlobalTheory.CxPts X.str (σ.comp e.toRingHom)) (n g : ℕ) (ch₀ : OpenPartialHomeomorph (GlobalTheory.CxPts (genStr T.Z) σ) (Fin n → ℂ)) (ex : ExpMaps T.Z σ g), IsExpChart ch₀ ex → cxOf e σ hj y ∈ ch₀.source → ch₀ (cxOf e σ hj y) = 0 → ∀ r : ℝ, 0 < r → ∃ (hn : n = X.dim) (r' : ℝ) (ch : OpenPartialHomeomorph (GlobalTheory.CxPts X.str (σ.comp e.toRingHom)) (ReciprocityTheory.L2DbarEstimates.V X.dim)), 0 < r' ∧ r' < r ∧ r' < 1 ∧ IsHoloChart ch ∧ y ∈ ch.source ∧ ch y = 0 ∧ (∀ z ∈ ch.source, (ch z).ofLp ∈ GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.polydisc X.dim 1) ∧ ∀ z ∈ ch.source, cxOf e σ hj z ∈ ch₀.source ∧ ch₀ (cxOf e σ hj z) = fun k => (r' : ℂ) * (ch z).ofLp (Fin.cast hn k) := by
  intro E _ _ _ H Dw l Xo c O _ β Y T F _ e σ X j hj hji y n g ch₀ ex hex hy0 hy00 r hr
  set κ := cxOf e σ hj with hκdef
  have hκ : IsOpenEmbedding κ := isOpenEmbedding_cxOf e σ hj
  haveI : Nonempty (GlobalTheory.CxPts X.str (σ.comp e.toRingHom)) := ⟨y⟩
  set χ := (hκ.toOpenPartialHomeomorph κ).trans ch₀ with hχdef
  have hχ : ∀ u ∈ χ.target, κ (χ.symm u) = ch₀.symm u := fun u hu => by
    have h2 : ch₀.symm u ∈ Set.range κ := by
      have := hu.2
      rwa [Set.mem_preimage, IsOpenEmbedding.toOpenPartialHomeomorph_target] at this
    rw [OpenPartialHomeomorph.coe_trans_symm, Function.comp_apply]
    exact hκ.toOpenPartialHomeomorph_right_inv κ h2
  have hyχ : y ∈ χ.source := ⟨trivial, hy0⟩
  have hχy : χ y = 0 := hy00
  obtain ⟨c₁, hc₁⟩ := GlobalTheory.AlgChart.exists_mem_source (p := X.str) (σ := σ.comp e.toRingHom) (D := X.dim) y
  have hn : n = X.dim := by
    set Φ := χ.symm.trans c₁.e with hΦ
    have h0 : (0 : Fin n → ℂ) ∈ Φ.source := by
      refine ⟨?_, ?_⟩
      · rw [← hχy]
        exact χ.map_source hyχ
      · show χ.symm 0 ∈ c₁.e.source
        rw [← hχy, χ.left_inv hyχ]
        exact hc₁
    have h0t : (0 : Fin n → ℂ) ∈ χ.target := h0.1
    have h1 : DifferentiableAt ℂ Φ 0 := by
      rw [differentiableAt_euclidean]
      intro a
      have hev : (fun u => Φ u a) =ᶠ[𝓝 0]
          fun u => valAt' (ch₀.symm u).1 (j ''ᵁ c₁.U) ((j.appIso c₁.U).inv.hom (c₁.x a)) := by
        filter_upwards [Φ.open_source.mem_nhds h0] with u hu
        have hs : χ.symm u ∈ c₁.e.source := hu.2
        show c₁.e (χ.symm u) a = _
        rw [c₁.apply_eq _ hs a, ev_eq_valAt'_cxOf e σ hj _ _ (c₁.source_subset hs),
          show cxOf e σ hj (χ.symm u) = ch₀.symm u from hχ u hu.1]
      refine DifferentiableAt.congr_of_eventuallyEq ?_ hev
      refine differentiableAt_valAt'_symm hex _ _ h0t.1 ?_
      rw [← hχ 0 h0t]
      exact le_preimage_cxOf e σ hj _ (c₁.source_subset h0.2)
    have h2 : DifferentiableAt ℂ Φ.symm (Φ 0) := by
      have hB : IsOpen Φ.target := Φ.open_target
      have hΦ0 : Φ 0 ∈ Φ.target := Φ.map_source h0
      have hsub : Φ.target ⊆ c₁.e.target := fun w hw => hw.1
      have hmaps : Set.MapsTo (fun w => κ (c₁.e.symm w)) Φ.target ch₀.source := fun w hw => hw.2.2
      have hhol : IsHolTo Φ.target (fun w => (κ (c₁.e.symm w)).1) := by
        intro U f
        have hset : {b ∈ Φ.target | ⊤ ≤ (κ (c₁.e.symm b)).1 ⁻¹ᵁ U} =
            Φ.target ∩ c₁.e.symm ⁻¹' ptsIn X.str (σ.comp e.toRingHom) (j ⁻¹ᵁ U) := rfl
        refine ⟨?_, ?_⟩
        · rw [hset]
          exact (c₁.e.continuousOn_symm.mono hsub).isOpen_inter_preimage hB (isOpen_ptsIn _)
        · rw [hset]
          refine ((c₁.holo (j ⁻¹ᵁ U) ((j.app U).hom f)).mono fun w hw => ⟨hsub hw.1, hw.2⟩).congr
            fun w _ => ?_
          exact valR_comp (c₁.e.symm w).1 j U f
      rw [differentiableAt_pi]
      intro k
      have hd := (hex.2.1 k (ReciprocityTheory.L2DbarEstimates.V X.dim) Φ.target (fun w => κ (c₁.e.symm w)) hB hhol hmaps).differentiableAt
        (hB.mem_nhds hΦ0)
      exact hd
    have := finrank_eq_of_differentiableAt Φ h0 h1 h2
    simpa [finrank_euclideanSpace_fin] using this
  subst hn
  have hr1 : 0 < min r 1 := lt_min hr one_pos
  set r' : ℝ := min r 1 / 2 with hr'
  have hr'0 : 0 < r' := half_pos hr1
  have hr'r : r' < min r 1 := half_lt_self hr1
  have hr'c : (r' : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hr'0.ne'
  let L : (Fin X.dim → ℂ) ≃L[ℂ] ReciprocityTheory.L2DbarEstimates.V X.dim :=
    (ContinuousLinearEquiv.smulLeft (Units.mk0 ((r' : ℂ)⁻¹) (inv_ne_zero hr'c))).trans
      (EuclideanSpace.equiv (Fin X.dim) ℂ).symm
  have hL : ∀ u k, (L u).ofLp k = (r' : ℂ)⁻¹ * u k := by
    intro u k
    simp [L]
  let ch := (χ.trans (OpenPartialHomeomorph.ofSet (Metric.ball (0 : Fin X.dim → ℂ) r') Metric.isOpen_ball)).trans
    L.toHomeomorph.toOpenPartialHomeomorph
  have hchs : ∀ v, ch.symm v = χ.symm (L.symm v) := fun v => rfl
  have hch : ∀ z, ch z = L (χ z) := fun z => rfl
  have hsrc : ∀ z ∈ ch.source, z ∈ χ.source ∧ χ z ∈ Metric.ball (0 : Fin X.dim → ℂ) r' := fun z hz => hz.1
  have htgt : ∀ v ∈ ch.target, L.symm v ∈ χ.target := fun v hv => hv.2.2
  refine ⟨rfl, r', ch, hr'0, hr'r.trans_le (min_le_left _ _), hr'r.trans_le (min_le_right _ _), ?_,
    ⟨⟨hyχ, ?_⟩, trivial⟩, ?_, ?_, ?_⟩
  · intro W f v hv
    have hopen : IsOpen (ch.target ∩ ch.symm ⁻¹' ptsIn X.str (σ.comp e.toRingHom) W) :=
      ch.continuousOn_symm.isOpen_inter_preimage ch.open_target (isOpen_ptsIn W)
    refine DifferentiableAt.differentiableWithinAt ?_
    have hev : (ev X.str (σ.comp e.toRingHom) W f ∘ ch.symm) =ᶠ[𝓝 v]
        fun w => valAt' (ch₀.symm (L.symm w)).1 (j ''ᵁ W) ((j.appIso W).inv.hom f) := by
      filter_upwards [hopen.mem_nhds hv] with w hw
      rw [Function.comp_apply, ev_eq_valAt'_cxOf e σ hj W f hw.2, hchs,
        show cxOf e σ hj (χ.symm (L.symm w)) = ch₀.symm (L.symm w) from hχ _ (htgt w hw.1)]
    refine DifferentiableAt.congr_of_eventuallyEq ?_ hev
    have hb := htgt v hv.1
    refine (differentiableAt_valAt'_symm hex (j ''ᵁ W) _ hb.1 ?_).comp v L.symm.differentiableAt
    rw [← hχ _ hb]
    exact le_preimage_cxOf e σ hj W hv.2
  · show χ y ∈ Metric.ball 0 r'
    rw [hχy]
    exact Metric.mem_ball_self hr'0
  · rw [hch, hχy, map_zero]
  · intro z hz
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.polydisc, Set.mem_setOf_eq]
    intro k
    rw [hch, hL, norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hr'0.le]
    have h1 := (hsrc z hz).2
    rw [mem_ball_zero_iff] at h1
    have h2 : ‖χ z k‖ < r' := (norm_le_pi_norm (χ z) k).trans_lt h1
    calc r'⁻¹ * ‖χ z k‖ < r'⁻¹ * r' := mul_lt_mul_of_pos_left h2 (inv_pos.2 hr'0)
      _ = 1 := inv_mul_cancel₀ hr'0.ne'
  · intro z hz
    refine ⟨hz.1.1.2, ?_⟩
    funext k
    show χ z k = _
    rw [hch, hL, Fin.cast_eq_self, ← mul_assoc, mul_inv_cancel₀ hr'c, one_mul]

end GlobalTheory.LieBase
