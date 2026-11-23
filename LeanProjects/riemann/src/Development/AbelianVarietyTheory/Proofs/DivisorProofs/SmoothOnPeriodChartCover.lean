import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsTateZero
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsHolToOfOpenImmersion
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsHolToFibPtAndCompFibre
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopologicalKrullDimEqSucc
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GenericallySmoothModel
open CategoryTheory AlgebraicGeometry Set Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.ArInt GlobalTheory.TorsionForm GlobalTheory.ThetaRR
open GlobalTheory.LB (toMod)
open GlobalTheory.LieVB (omega)
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe (Fl Pt stdLat symMat tauU siegel symPart ChernIsFlat IsMetric InducesPolarisation cov)
open ReciprocityTheory.L2DbarEstimates (V)
open Filter Topology
open scoped ContDiff
open scoped ComplexOrder
open CategoryTheory.Limits CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ThetaRR.CInfChart

theorem continuous_and_holo : ∀ (k : Type) [CommRing k] (S : Scheme.{0}) (p : S ⟶ Sp k) (P : PPAS S) (h : VMetric p (omega P.A) P.g) (σ : k →+* ℂ) (D D' : ℕ) (c : AlgChart p σ D) (τ : V D → Matrix (Fin P.g) (Fin P.g) ℂ) (ex : Pt (V D) P.g → CxPts (P.A.hom ≫ p) σ), IsPeriodChart h c τ ex → ContinuousOn ex (cov c.e.target P.g) ∧ ∀ (c' : AlgChart (P.A.hom ≫ p) σ D'), ∀ q ∈ cov c.e.target P.g, ex q ∈ c'.e.source → DifferentiableAt ℂ (fun x => c'.e (ex x)) q := by
  intro k _ S p P h σ D D' c τ ex HP
  have hB : IsOpen (cov c.e.target P.g) := c.e.open_target.prod isOpen_univ
  exact ⟨GlobalTheory.TrueCx.TorHolo.continuousOn_of_isHolTo HP.2.1,
    fun c' q hq hs => GlobalTheory.TrueCx.TorHolo.differentiableAt_chart hB HP.2.1 c' hq hs⟩

theorem exists_chart_total : ∀ (k : Type) [CommRing k] (S : Scheme.{0}) (p : S ⟶ Sp k), IsRegSurf p → ∀ (P : PPAS S) (σ : k →+* ℂ) (y : CxPts (P.A.hom ≫ p) σ), ∃ c' : AlgChart (P.A.hom ≫ p) σ (P.g + 1), y ∈ c'.e.source := by
  intro k _ S p hp P σ y
  obtain ⟨-, hU⟩ := GlobalTheory.RegGenSmooth.genSmooth_of_isRegSurf k S p hp
  obtain ⟨U, hyU, hsm⟩ := hU σ (Points.PtsOver.map P.A.hom rfl _ y)
  haveI : SmoothOfRelativeDimension P.g (P.A.hom ∣_ U) := (smoothOfRelativeDimension_isStableUnderBaseChange (n := P.g)).of_isPullback (isPullback_morphismRestrict P.A.hom U).flip P.smoothDim
  haveI : SmoothOfRelativeDimension (P.g + 1) ((P.A.hom ⁻¹ᵁ U).ι ≫ P.A.hom ≫ p) := by
    have e : (P.A.hom ⁻¹ᵁ U).ι ≫ P.A.hom ≫ p = (P.A.hom ∣_ U) ≫ (U.ι ≫ p) := by
      rw [← Category.assoc, ← morphismRestrict_ι, Category.assoc]
    rw [e]
    infer_instance
  have hmem : y.1 (IsLocalRing.closedPoint ℂ) ∈ P.A.hom ⁻¹ᵁ U := mem_ptsIn.1 hyU
  obtain ⟨V', x, hV, hz, hx⟩ := GlobalTheory.ModelCharts.exists_etale_coords_of_opens (P.A.hom ≫ p) (P.g + 1) (P.A.hom ⁻¹ᵁ U) hmem
  obtain ⟨c, hc, -⟩ := AlgChart.exists_of_etale hV x hx (mem_ptsIn.2 hz)
  exact ⟨c, hc⟩

theorem exists_frame_cot : ∀ (k : Type) [CommRing k] (S : Scheme.{0}) (p : S ⟶ Sp k) (P : PPAS S) (h : VMetric p (omega P.A) P.g) (σ : k →+* ℂ) (D : ℕ) (c : AlgChart p σ D) (τ : V D → Matrix (Fin P.g) (Fin P.g) ℂ) (ex : Pt (V D) P.g → CxPts (P.A.hom ≫ p) σ), IsPeriodChart h c τ ex → ∀ v ∈ c.e.target, ∃ (W : P.A.left.Opens) (f : Fin P.g → Γ(P.A.left, W)), ex (v, 0) ∈ ptsIn (P.A.hom ≫ p) σ W ∧ IsUnit (Matrix.of fun a b => cot ex W (f a) v b).det := by
  intro k _ S p P h σ D c τ ex HP v hv
  have hs := LieVB.sec_hom (MonObj.one (X := P.A))
  obtain ⟨U, W, hx, hle, ch⟩ := Conormal.exists_isChart hs (mem_ptsIn.1 (h.isVB.mem_pick (p := p) (σ := σ) (c.e.symm v)))
  have hU : c.e.symm v ∈ ptsIn p σ U := mem_ptsIn.2 hx
  let c₀ : VB.Chart (omega P.A) P.g := ⟨U, _, (h.isVB.pick (c.e.symm v)).isFrame.res hle⟩
  choose f hf using fun a => ch.d_surjective hs (c₀.e a)
  have hG : (h.met σ).G c₀ (c.e.symm v) =
      HermFrame.chg (Matrix.of fun a b => cot ex W (f b) v a) ((2 : ℂ) • imPart τ v) := by
    ext a b
    rw [← (h.met σ).form_frame c₀ hU, ← hf, ← hf, HermFrame.chg_apply]
    exact (HP.2.2 v hv).2.2.2.2 U W ch.le _ _ hU
  have hP := (h.met σ).posDef c₀ _ hU
  rw [hG] at hP
  have hu := hP.det_pos.ne'.isUnit
  rw [HermFrame.chg, det_mul, det_mul] at hu
  have e : (ex (v, 0)).1 = (c.e.symm v).1 ≫ LieVB.unitSec P.A :=
    ((HP.2.2 v hv).2.2.2.1 0).2 ⟨0, zero_mem _, by funext i; simp [GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe.per, vecMul, dotProduct]⟩
  refine ⟨W, f, ?_, ?_⟩
  · change ⊤ ≤ (ex (v, 0)).1 ⁻¹ᵁ W
    rw [e]
    exact fun x hx' => ch.le (hU hx')
  · have ht : (Matrix.of fun a b => cot ex W (f a) v b) = (Matrix.of fun a b => cot ex W (f b) v a)ᵀ := by
      ext; rfl
    rw [ht]
    exact isUnit_of_mul_isUnit_left (isUnit_of_mul_isUnit_left hu)

theorem exists_transl_fn : ∀ (k : Type) [CommRing k] (S : Scheme.{0}) (p : S ⟶ Sp k) (P : PPAS S) (h : VMetric p (omega P.A) P.g) (σ : k →+* ℂ) (D D' : ℕ) (c : AlgChart p σ D) (τ : V D → Matrix (Fin P.g) (Fin P.g) ℂ) (ex : Pt (V D) P.g → CxPts (P.A.hom ≫ p) σ), IsPeriodChart h c τ ex → ∀ (c' : AlgChart (P.A.hom ≫ p) σ D') (v : V D) (z₀ : Fin P.g → ℂ), v ∈ c.e.target → ex (v, z₀) ∈ c'.e.source → ∀ (W : P.A.left.Opens) (f : Γ(P.A.left, W)), ex (v, 0) ∈ ptsIn (P.A.hom ≫ p) σ W → ∃ M : V D' → ℂ, DifferentiableAt ℂ M (c'.e (ex (v, z₀))) ∧ ∀ᶠ q in 𝓝 ((v, 0) : Pt (V D) P.g), ev (P.A.hom ≫ p) σ W f (ex q) = M (c'.e (ex (q + ((0 : V D), z₀)))) := by
  intro k _ S p P h σ D D' c τ ex HP c' v z₀ hv hs W f hW
  classical
  have hB : IsOpen (cov c.e.target P.g) := c.e.open_target.prod isOpen_univ
  have hcont : ContinuousOn ex (cov c.e.target P.g) := GlobalTheory.TrueCx.TorHolo.continuousOn_of_isHolTo HP.2.1
  let π : CxPts (P.A.hom ≫ p) σ → CxPts p σ := Points.PtsOver.map P.A.hom rfl _
  have hover : ∀ w ∈ c.e.target, ∀ z, π (ex (w, z)) = c.e.symm w := fun w hw z =>
    Subtype.ext ((HP.2.2 w hw).1 z)
  let β : V D' → V D := fun ξ => c.e (π (c'.e.symm ξ))
  let a : V D' → (Sp ℂ ⟶ P.A.left) := fun ξ => (ex (β ξ, -z₀)).1
  let b : V D' → (Sp ℂ ⟶ P.A.left) := fun ξ => (c'.e.symm ξ).1
  let m : V D' → (Sp ℂ ⟶ pullback P.A.hom P.A.hom) := fun ξ =>
    if hξ : a ξ ≫ P.A.hom = b ξ ≫ P.A.hom then pullback.lift (a ξ) (b ξ) hξ
    else pullback.lift (b ξ) (b ξ) rfl
  let μl : pullback P.A.hom P.A.hom ⟶ P.A.left := (MonObj.mul : P.A ⊗ P.A ⟶ P.A).left
  have hkey : ∀ w ∈ c.e.target, ∀ z, ex (w, z) ∈ c'.e.source →
      m (c'.e (ex (w, z))) ≫ μl = (ex (w, -z₀ + z)).1 := by
    intro w hw z hz
    have e1 : c'.e.symm (c'.e (ex (w, z))) = ex (w, z) := c'.e.left_inv hz
    have e2 : β (c'.e (ex (w, z))) = w := by
      change c.e (π (c'.e.symm (c'.e (ex (w, z))))) = w
      rw [e1, hover w hw, c.e.right_inv hw]
    have ha : a (c'.e (ex (w, z))) = (ex (w, -z₀)).1 := by
      change (ex (β (c'.e (ex (w, z))), -z₀)).1 = _
      rw [e2]
    have hb : b (c'.e (ex (w, z))) = (ex (w, z)).1 := by
      change (c'.e.symm (c'.e (ex (w, z)))).1 = _
      rw [e1]
    have ho := (HP.2.2 w hw).1
    have hab : a (c'.e (ex (w, z))) ≫ P.A.hom = b (c'.e (ex (w, z))) ≫ P.A.hom := by
      rw [ha, hb, ho, ho]
    have hm : m (c'.e (ex (w, z))) = pullback.lift (a (c'.e (ex (w, z)))) (b (c'.e (ex (w, z)))) hab :=
      dif_pos hab
    let x : Over.mk (c.e.symm w).1 ⟶ P.A := Over.homMk (ex (w, -z₀)).1 (ho _)
    let y : Over.mk (c.e.symm w).1 ⟶ P.A := Over.homMk (ex (w, z)).1 (ho _)
    have hxy := (HP.2.2 w hw).2.1 (-z₀) z x y rfl rfl
    rw [← hxy, CategoryTheory.Hom.mul_def, Over.comp_left, Over.lift_left, hm]
    congr 1
    exact pullback.hom_ext (by rw [pullback.lift_fst, pullback.lift_fst, ha]; rfl)
      (by rw [pullback.lift_snd, pullback.lift_snd, hb]; rfl)
  have congrH : ∀ {X : Scheme.{0}} {B : Set (V D')} {c₁ c₂ : V D' → (Sp ℂ ⟶ X)}, IsHolTo B c₁ →
      (∀ ξ ∈ B, c₂ ξ = c₁ ξ) → IsHolTo B c₂ := by
    intro X B c₁ c₂ hc he U g
    have e : {ξ ∈ B | ⊤ ≤ c₂ ξ ⁻¹ᵁ U} = {ξ ∈ B | ⊤ ≤ c₁ ξ ⁻¹ᵁ U} := by
      ext ξ
      exact and_congr_right fun hξ => by rw [he ξ hξ]
    rw [e]
    exact ⟨(hc U g).1, (hc U g).2.congr fun ξ hξ => by rw [he ξ hξ.1]⟩
  have hyπ : IsHolTo c'.e.target fun ξ => (π (c'.e.symm ξ)).1 :=
    GlobalTheory.HolFibre.isHolTo_comp (GlobalTheory.TrueCx.TorHolo.isHolTo_symm c') P.A.hom
  have hπc : ContinuousOn (fun ξ => π (c'.e.symm ξ)) c'.e.target :=
    GlobalTheory.TrueCx.TorHolo.continuousOn_of_isHolTo hyπ
  let T := c'.e.target ∩ (fun ξ => π (c'.e.symm ξ)) ⁻¹' c.e.source
  have hT : IsOpen T := hπc.isOpen_inter_preimage c'.e.open_target c.e.open_source
  have hβ : ∀ ξ ∈ T, DifferentiableAt ℂ β ξ := fun ξ hξ =>
    GlobalTheory.TrueCx.TorHolo.differentiableAt_chart c'.e.open_target hyπ c hξ.1 hξ.2
  have hβT : ∀ ξ ∈ T, β ξ ∈ c.e.target := fun ξ hξ => c.e.map_source hξ.2
  have haH : IsHolTo T a := by
    intro U g
    obtain ⟨ho, hd⟩ := HP.2.1 U g
    let kk : V D' → Pt (V D) P.g := fun ξ => (β ξ, -z₀)
    have hkc : ContinuousOn kk T := fun ξ hξ =>
      ((hβ ξ hξ).continuousAt.prodMk continuousAt_const).continuousWithinAt
    have e : {ξ ∈ T | ⊤ ≤ a ξ ⁻¹ᵁ U} =
        T ∩ kk ⁻¹' {P' ∈ cov c.e.target P.g | ⊤ ≤ (ex P').1 ⁻¹ᵁ U} := by
      ext ξ
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨h1, ⟨hβT ξ h1, trivial⟩, h2⟩
      · rintro ⟨h1, -, h2⟩
        exact ⟨h1, h2⟩
    rw [e]
    refine ⟨hkc.isOpen_inter_preimage hT ho, fun ξ hξ => ?_⟩
    have hk : DifferentiableAt ℂ kk ξ := (hβ ξ hξ.1).prodMk (differentiableAt_const _)
    exact ((hd.differentiableAt (ho.mem_nhds hξ.2)).comp ξ hk).differentiableWithinAt
  have hbH : IsHolTo T b := by
    intro U g
    obtain ⟨ho, hd⟩ := GlobalTheory.TrueCx.TorHolo.isHolTo_symm c' U g
    have e : {ξ ∈ T | ⊤ ≤ b ξ ⁻¹ᵁ U} = T ∩ {ξ ∈ c'.e.target | ⊤ ≤ (c'.e.symm ξ).1 ⁻¹ᵁ U} := by
      ext ξ
      exact ⟨fun h => ⟨h.1, h.1.1, h.2⟩, fun h => ⟨h.1, h.2.2⟩⟩
    rw [e]
    exact ⟨hT.inter ho, hd.mono inter_subset_right⟩
  have habT : ∀ ξ ∈ T, a ξ ≫ P.A.hom = b ξ ≫ P.A.hom := by
    intro ξ hξ
    have h1 : a ξ ≫ P.A.hom = (c.e.symm (β ξ)).1 := (HP.2.2 _ (hβT ξ hξ)).1 _
    have h2 : c.e.symm (β ξ) = π (c'.e.symm ξ) := c.e.left_inv hξ.2
    rw [h1, h2]
    rfl
  have hmH : IsHolTo T m := by
    refine GlobalTheory.HolFibre.isHolTo_of_isPullback (IsPullback.of_hasPullback P.A.hom P.A.hom) ?_ ?_
    · exact congrH haH fun ξ hξ => by
        change m ξ ≫ pullback.fst _ _ = a ξ
        rw [show m ξ = pullback.lift (a ξ) (b ξ) (habT ξ hξ) from dif_pos (habT ξ hξ), pullback.lift_fst]
    · exact congrH hbH fun ξ hξ => by
        change m ξ ≫ pullback.snd _ _ = b ξ
        rw [show m ξ = pullback.lift (a ξ) (b ξ) (habT ξ hξ) from dif_pos (habT ξ hξ), pullback.lift_snd]
  have hmu : IsHolTo T fun ξ => m ξ ≫ μl := GlobalTheory.HolFibre.isHolTo_comp hmH μl
  have hξ0 : c'.e (ex (v, z₀)) ∈ T := by
    refine ⟨c'.e.map_source hs, ?_⟩
    change π (c'.e.symm (c'.e (ex (v, z₀)))) ∈ c.e.source
    rw [c'.e.left_inv hs, hover v hv]
    exact c.e.map_target hv
  have hm0 : m (c'.e (ex (v, z₀))) ≫ μl = (ex (v, 0)).1 := by
    rw [hkey v hv z₀ hs, neg_add_cancel]
  refine ⟨fun ξ => valAt' (m ξ ≫ μl) W f, ?_, ?_⟩
  · obtain ⟨ho, hd⟩ := hmu W f
    have hmem : c'.e (ex (v, z₀)) ∈ {ξ ∈ T | ⊤ ≤ (m ξ ≫ μl) ⁻¹ᵁ W} := by
      refine ⟨hξ0, ?_⟩
      rw [hm0]
      exact hW
    exact hd.differentiableAt (ho.mem_nhds hmem)
  · have hQ : ((v, z₀) : Pt (V D) P.g) ∈ cov c.e.target P.g := ⟨hv, trivial⟩
    have ht : Tendsto (fun q : Pt (V D) P.g => q + ((0 : V D), z₀)) (𝓝 (v, 0)) (𝓝 (v, z₀)) := by
      have e : ((v, 0) : Pt (V D) P.g) + ((0 : V D), z₀) = (v, z₀) := by ext <;> simp
      exact (continuous_id.add continuous_const : Continuous fun q : Pt (V D) P.g => q + ((0 : V D), z₀)).tendsto' _ _ e
    have h1 : ∀ᶠ q in 𝓝 ((v, 0) : Pt (V D) P.g), ex (q + ((0 : V D), z₀)) ∈ c'.e.source :=
      ht.eventually ((hcont.continuousAt (hB.mem_nhds hQ)).preimage_mem_nhds (c'.e.open_source.mem_nhds hs))
    have h2 : ∀ᶠ q in 𝓝 ((v, 0) : Pt (V D) P.g), q.1 ∈ c.e.target :=
      continuous_fst.continuousAt.preimage_mem_nhds (c.e.open_target.mem_nhds hv)
    filter_upwards [h1, h2] with q hq1 hq2
    have e2 : q + ((0 : V D), z₀) = (q.1, q.2 + z₀) := by ext <;> simp
    rw [e2] at hq1 ⊢
    change valAt' (ex q).1 W f = valAt' (m (c'.e (ex (q.1, q.2 + z₀))) ≫ μl) W f
    rw [hkey q.1 hq2 _ hq1]
    have e3 : ((q.1, -z₀ + (q.2 + z₀)) : Pt (V D) P.g) = q := by ext <;> simp
    rw [e3]

theorem exists_base_fn : ∀ (k : Type) [CommRing k] (S : Scheme.{0}) (p : S ⟶ Sp k) (P : PPAS S) (h : VMetric p (omega P.A) P.g) (σ : k →+* ℂ) (D D' : ℕ) (c : AlgChart p σ D) (τ : V D → Matrix (Fin P.g) (Fin P.g) ℂ) (ex : Pt (V D) P.g → CxPts (P.A.hom ≫ p) σ), IsPeriodChart h c τ ex → ∀ (c' : AlgChart (P.A.hom ≫ p) σ D') (v : V D) (z₀ : Fin P.g → ℂ), v ∈ c.e.target → ex (v, z₀) ∈ c'.e.source → ∃ M : V D' → V D, DifferentiableAt ℂ M (c'.e (ex (v, z₀))) ∧ ∀ᶠ q in 𝓝 ((v, 0) : Pt (V D) P.g), q.1 = M (c'.e (ex (q + ((0 : V D), z₀)))) := by
  intro k _ S p P h σ D D' c τ ex HP c' v z₀ hv hs
  have hB : IsOpen (cov c.e.target P.g) := c.e.open_target.prod isOpen_univ
  have hcont : ContinuousOn ex (cov c.e.target P.g) := GlobalTheory.TrueCx.TorHolo.continuousOn_of_isHolTo HP.2.1
  let π : CxPts (P.A.hom ≫ p) σ → CxPts p σ := Points.PtsOver.map P.A.hom rfl _
  have hover : ∀ w ∈ c.e.target, ∀ z, π (ex (w, z)) = c.e.symm w := fun w hw z =>
    Subtype.ext ((HP.2.2 w hw).1 z)
  refine ⟨fun ξ => c.e (π (c'.e.symm ξ)), ?_, ?_⟩
  · have hy : IsHolTo c'.e.target fun ξ => (π (c'.e.symm ξ)).1 :=
      GlobalTheory.HolFibre.isHolTo_comp (GlobalTheory.TrueCx.TorHolo.isHolTo_symm c') P.A.hom
    have h0 : c'.e.symm (c'.e (ex (v, z₀))) = ex (v, z₀) := c'.e.left_inv hs
    have hsrc : π (c'.e.symm (c'.e (ex (v, z₀)))) ∈ c.e.source := by
      rw [h0, hover v hv]; exact c.e.map_target hv
    exact GlobalTheory.TrueCx.TorHolo.differentiableAt_chart c'.e.open_target hy c (c'.e.map_source hs) hsrc
  · have hQ : ((v, z₀) : Pt (V D) P.g) ∈ cov c.e.target P.g := ⟨hv, trivial⟩
    have ht : Tendsto (fun q : Pt (V D) P.g => q + ((0 : V D), z₀)) (𝓝 (v, 0)) (𝓝 (v, z₀)) := by
      have e : ((v, 0) : Pt (V D) P.g) + ((0 : V D), z₀) = (v, z₀) := by ext <;> simp
      exact (continuous_id.add continuous_const : Continuous fun q : Pt (V D) P.g => q + ((0 : V D), z₀)).tendsto' _ _ e
    have h1 : ∀ᶠ q in 𝓝 ((v, 0) : Pt (V D) P.g), ex (q + ((0 : V D), z₀)) ∈ c'.e.source :=
      ht.eventually ((hcont.continuousAt (hB.mem_nhds hQ)).preimage_mem_nhds (c'.e.open_source.mem_nhds hs))
    have h2 : ∀ᶠ q in 𝓝 ((v, 0) : Pt (V D) P.g), q.1 ∈ c.e.target :=
      continuous_fst.continuousAt.preimage_mem_nhds (c.e.open_target.mem_nhds hv)
    filter_upwards [h1, h2] with q hq1 hq2
    have e1 : c'.e.symm (c'.e (ex (q + ((0 : V D), z₀)))) = ex (q + ((0 : V D), z₀)) := c'.e.left_inv hq1
    have e2 : q + ((0 : V D), z₀) = (q.1, q.2 + z₀) := by ext <;> simp
    show q.1 = c.e (π (c'.e.symm (c'.e (ex (q + ((0 : V D), z₀))))))
    rw [e1, e2, hover q.1 hq2, c.e.right_inv hq2]

theorem cInfAt_of_periodChart : ∀ (k : Type) [CommRing k] (S : Scheme.{0}) (p : S ⟶ Sp k), IsRegSurf p → ∀ (P : PPAS S) (h : VMetric p (omega P.A) P.g) (σ : k →+* ℂ) (c : AlgChart p σ 1) (τ : V 1 → Matrix (Fin P.g) (Fin P.g) ℂ) (ex : Pt (V 1) P.g → CxPts (P.A.hom ≫ p) σ), IsPeriodChart h c τ ex → ∀ u : CxPts (P.A.hom ≫ p) σ → ℝ, ContDiffOn ℝ ∞ (fun Q => u (ex Q)) (cov c.e.target P.g) → ∀ Q ∈ cov c.e.target P.g, CInfAt u (ex Q) := by
  intro k _ S p hp P h σ c τ ex HP u hu Q hQ
  obtain ⟨v, z₀⟩ := Q
  have hv : v ∈ c.e.target := hQ.1
  have hcovO : IsOpen (cov c.e.target P.g) := c.e.open_target.prod isOpen_univ
  obtain ⟨c', hc'⟩ := exists_chart_total k S p hp P σ (ex (v, z₀))
  obtain ⟨hcont, hdiff⟩ := continuous_and_holo k S p P h σ 1 (P.g + 1) c τ ex HP
  obtain ⟨W, f, hW, hdet⟩ := exists_frame_cot k S p P h σ 1 c τ ex HP v hv
  choose M hM hMe using fun a => exists_transl_fn k S p P h σ 1 (P.g + 1) c τ ex HP c' v z₀ hv hc' W (f a) hW
  obtain ⟨M₀, hM₀, hM₀e⟩ := exists_base_fn k S p P h σ 1 (P.g + 1) c τ ex HP c' v z₀ hv hc'
  let Ψ : Pt (V 1) P.g → V (P.g + 1) := fun x => c'.e (ex x)
  let N := cov c.e.target P.g ∩ ex ⁻¹' c'.e.source
  have hNo : IsOpen N := hcont.isOpen_inter_preimage hcovO c'.e.open_source
  have hQN : ((v, z₀) : Pt (V 1) P.g) ∈ N := ⟨hQ, hc'⟩
  have hΨN : DifferentiableOn ℂ Ψ N := fun x hx => (hdiff c' x hx.1 hx.2).differentiableWithinAt
  have hCω : ContDiffAt ℂ ω Ψ (v, z₀) := GlobalTheory.SCV.contDiffAt_of_differentiableOn hΨN (hNo.mem_nhds hQN) ω
  have hΨd : HasFDerivAt Ψ (fderiv ℂ Ψ (v, z₀)) (v, z₀) := (hdiff c' _ hQ hc').hasFDerivAt
  let F : Pt (V 1) P.g → (Fin P.g → ℂ) := fun x a => ev (P.A.hom ≫ p) σ W (f a) (ex x)
  let Φ : Pt (V 1) P.g → Pt (V 1) P.g := fun x => (x.1, F x)
  let Mt : V (P.g + 1) → Pt (V 1) P.g := fun ξ => (M₀ ξ, fun a => M a ξ)
  have hMt : DifferentiableAt ℂ Mt (Ψ (v, z₀)) := hM₀.prodMk (differentiableAt_pi.2 hM)
  have hsh : ((v, 0) : Pt (V 1) P.g) + ((0 : V 1), z₀) = (v, z₀) := by ext <;> simp
  have hΨd' : HasFDerivAt Ψ (fderiv ℂ Ψ (v, z₀)) (((v, 0) : Pt (V 1) P.g) + ((0 : V 1), z₀)) := by
    rw [hsh]; exact hΨd
  have hΨ' : HasFDerivAt (fun x : Pt (V 1) P.g => Ψ (x + ((0 : V 1), z₀))) (fderiv ℂ Ψ (v, z₀)) (v, 0) := by
    have := hΨd'.comp ((v, 0) : Pt (V 1) P.g) ((hasFDerivAt_id ((v, 0) : Pt (V 1) P.g)).add_const ((0 : V 1), z₀))
    rw [ContinuousLinearMap.comp_id] at this
    exact this
  have hev : Φ =ᶠ[𝓝 ((v, 0) : Pt (V 1) P.g)] Mt ∘ fun x => Ψ (x + ((0 : V 1), z₀)) := by
    filter_upwards [hM₀e, Filter.eventually_all.2 hMe] with x h0 h1
    exact Prod.ext h0 (funext h1)
  have hMt' : HasFDerivAt Mt (fderiv ℂ Mt (Ψ (v, z₀))) (Ψ (((v, 0) : Pt (V 1) P.g) + ((0 : V 1), z₀))) := by
    rw [hsh]; exact hMt.hasFDerivAt
  have hΦ : HasFDerivAt Φ ((fderiv ℂ Mt (Ψ (v, z₀))).comp (fderiv ℂ Ψ (v, z₀))) (v, 0) :=
    (hMt'.comp ((v, 0) : Pt (V 1) P.g) hΨ').congr_of_eventuallyEq hev
  have hF : DifferentiableAt ℂ F (v, 0) := by
    refine differentiableAt_pi.2 fun a => ?_
    obtain ⟨ho, hd⟩ := HP.2.1 W (f a)
    have hm : ((v, 0) : Pt (V 1) P.g) ∈ {b ∈ cov c.e.target P.g | ⊤ ≤ (ex b).1 ⁻¹ᵁ W} := ⟨⟨hv, trivial⟩, hW⟩
    exact hd.differentiableAt (ho.mem_nhds hm)
  have hΦ2 : HasFDerivAt Φ ((ContinuousLinearMap.fst ℂ (V 1) (Fin P.g → ℂ)).prod (fderiv ℂ F (v, 0))) (v, 0) :=
    hasFDerivAt_fst.prodMk hF.hasFDerivAt
  have huq := hΦ.unique hΦ2
  let G : (Fin P.g → ℂ) →L[ℂ] (Fin P.g → ℂ) := (fderiv ℂ F (v, 0)).comp (ContinuousLinearMap.inr ℂ (V 1) (Fin P.g → ℂ))
  have hinc : HasFDerivAt (fun z : Fin P.g → ℂ => F (v, z)) G 0 :=
    hF.hasFDerivAt.comp (0 : Fin P.g → ℂ) (hasFDerivAt_prodMk_right v 0)
  have hcot : ∀ a b, cot ex W (f a) v b = G (Pi.single b 1) a := by
    intro a b
    have := (hasFDerivAt_apply a (F (v, 0))).comp (0 : Fin P.g → ℂ) hinc
    exact congrArg (· (Pi.single b 1)) this.fderiv
  have hinj : Function.Injective (fderiv ℂ Ψ (v, z₀)) := by
    refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
    have e1 := congrArg (· x) huq
    simp only [ContinuousLinearMap.comp_apply, hx, map_zero, ContinuousLinearMap.prod_apply,
      ContinuousLinearMap.coe_fst'] at e1
    have hx1 : x.1 = 0 := (congrArg Prod.fst e1).symm
    have hx2 : fderiv ℂ F (v, 0) x = 0 := (congrArg Prod.snd e1).symm
    have hxe : x = ((0 : V 1), x.2) := Prod.ext hx1 rfl
    have hG : G x.2 = 0 := by
      rw [hxe] at hx2
      exact hx2
    have hx2s : x.2 = ∑ b, x.2 b • (Pi.single b (1 : ℂ) : Fin P.g → ℂ) := by
      ext j; simp [Finset.sum_apply, Pi.single_apply]
    have hmv : (Matrix.of fun a b => cot ex W (f a) v b) *ᵥ x.2 = 0 := by
      funext a
      have := congrArg (· a) hG
      rw [hx2s] at this
      simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
      simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, hcot, Pi.zero_apply]
      rw [← this]
      exact Finset.sum_congr rfl fun b _ => mul_comm _ _
    have hx2' : x.2 = 0 := Matrix.mulVec_injective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det _).2 hdet)
      (hmv.trans (Matrix.mulVec_zero _).symm)
    exact Prod.ext hx1 hx2'
  have hdim : Module.finrank ℂ (Pt (V 1) P.g) = Module.finrank ℂ (V (P.g + 1)) := by
    simp [Module.finrank_prod, add_comm]
  let e := (LinearMap.linearEquivOfInjective ((fderiv ℂ Ψ (v, z₀) : Pt (V 1) P.g →L[ℂ] V (P.g + 1)) : Pt (V 1) P.g →ₗ[ℂ] V (P.g + 1)) hinj hdim).toContinuousLinearEquiv
  have he : ((e : Pt (V 1) P.g →L[ℂ] V (P.g + 1))) = fderiv ℂ Ψ (v, z₀) :=
    ContinuousLinearMap.ext fun x => rfl
  have hf' : HasFDerivAt Ψ (e : Pt (V 1) P.g →L[ℂ] V (P.g + 1)) (v, z₀) := he ▸ hΨd
  have hn : (ω : WithTop ℕ∞) ≠ 0 := by simp
  let ψ := hCω.localInverse hf' hn
  have hψ : ContDiffAt ℂ ω ψ (Ψ (v, z₀)) := hCω.to_localInverse hf' hn
  have hri : ∀ᶠ ξ in 𝓝 (Ψ (v, z₀)), Ψ (ψ ξ) = ξ := (hCω.hasStrictFDerivAt' hf' hn).eventually_right_inverse
  have hψQ : ψ (Ψ (v, z₀)) = (v, z₀) := hCω.localInverse_apply_image hf' hn
  have hψN : ∀ᶠ ξ in 𝓝 (Ψ (v, z₀)), ψ ξ ∈ N :=
    hψ.continuousAt.preimage_mem_nhds (by rw [hψQ]; exact hNo.mem_nhds hQN)
  have hψω : ∀ᶠ ξ in 𝓝 (Ψ (v, z₀)), ContDiffAt ℂ ω ψ ξ := hψ.eventually (by simp)
  let O := interior {ξ | ContDiffAt ℂ ω ψ ξ ∧ Ψ (ψ ξ) = ξ ∧ ψ ξ ∈ N}
  have hO : IsOpen O := isOpen_interior
  have hξO : Ψ (v, z₀) ∈ O := mem_interior_iff_mem_nhds.2 (hψω.and (hri.and hψN))
  have hOsub : O ⊆ {ξ | ContDiffAt ℂ ω ψ ξ ∧ Ψ (ψ ξ) = ξ ∧ ψ ξ ∈ N} := interior_subset
  have hS : IsOpen (c'.e.source ∩ c'.e ⁻¹' O) := c'.e.continuousOn.isOpen_inter_preimage c'.e.open_source hO
  refine cInfAt_of_chart hS c' ?_ hc' ⟨hc', hξO⟩
  intro ξ hξ
  have hξO' : ξ ∈ O := by
    have := hξ.2.2
    rwa [mem_preimage, c'.e.right_inv hξ.1] at this
  have key : ∀ ξ' ∈ O, (u ∘ c'.e.symm) ξ' = u (ex (ψ ξ')) := by
    intro ξ' h'
    obtain ⟨-, h2, h3⟩ := hOsub h'
    have e2 : c'.e.symm (c'.e (ex (ψ ξ'))) = ex (ψ ξ') := c'.e.left_inv h3.2
    have e3 : c'.e (ex (ψ ξ')) = ξ' := h2
    rw [e3] at e2
    simp only [Function.comp_apply, e2]
  have hcd : ContDiffAt ℝ ∞ (fun ξ' => u (ex (ψ ξ'))) ξ := by
    obtain ⟨h1, -, h3⟩ := hOsub hξO'
    have hu' : ContDiffAt ℝ ∞ (fun x => u (ex x)) (ψ ξ) := hu.contDiffAt (hcovO.mem_nhds h3.1)
    exact hu'.comp ξ ((h1.restrict_scalars ℝ).of_le le_top)
  exact (hcd.congr_of_eventuallyEq (eventually_of_mem (hO.mem_nhds hξO') key)).contDiffWithinAt

end GlobalTheory.ThetaRR.CInfChart
