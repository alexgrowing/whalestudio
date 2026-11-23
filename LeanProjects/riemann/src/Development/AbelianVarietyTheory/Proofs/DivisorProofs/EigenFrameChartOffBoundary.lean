import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgeFrameGram
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFramedChartExponentialToroidalModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelHodgeGram
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HodgeMetricGramHolomorphicFrameForm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DivisorDecompositionFlagSteps
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalFlagCoordinatesStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHoloFrameChart
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHolomorphicFrameSliceComponentUniformisati
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HolomorphicFrameFamilyChartCoordinatesHolomorphi
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DimOpenlyImmersedVarietyEqCmTypeCardMulPq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHolomorphicLocalInverseOfInjOn
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AlgebraicEigenvectorCoordinatesHolomorphicUnifor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsConjFsBasisOfUnitary

set_option autoImplicit false

noncomputable section

section Free

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.LieBase
open GlobalTheory GlobalTheory.CxPts Matrix Filter
open scoped ComplexOrder Topology
open ReciprocityTheory.L2DbarEstimates (V)
open ReciprocityTheory.ChartRestriction.G.FD (Frame mat)

namespace GlobalTheory.HodgeFlagModel

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}

theorem exists_holo_frame (T : TorModel Y) {σ : c.F →+* ℂ} (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q))
    (hσ : Formalism.L2.PjFree.GoodEmb c σ) (hU : Formalism.L2.PjFree.IsUnf U) (y : CxPts (genStr T.Z) σ)
    (hy : ¬ LiesIn y (genBd T.Z)) (ch : AlgChart (genStr T.Z) σ Dw.dim) (hyc : y ∈ ch.e.source) :
    ∃ (k : U.Comp) (Fr : V Dw.dim → Frame (U.X k).Ψ (Dw.p + Dw.q)), ∀ᶠ u in 𝓝 (ch.e y),
      ∃ h : Fr u ∈ (U.X k).dom, cxPt T.Z (U.un k ⟨Fr u, h⟩) = ch.e.symm u ∧ DifferentiableAt ℂ Fr u := by
  classical
  obtain ⟨k, x₀, hx₀⟩ := GlobalTheory.LieBase.HoloFrame.exists_un E H Dw l Xo c O β Y T σ _ U hU _ hy
  have hcard : (U.X k).Ψ.card = Module.finrank ℚ E / 2 := by
    rw [← Fintype.card_coe]; exact ReciprocityTheory.ChartRestriction.G.FD.QuadraticCoefficientForms.card_Psi (U.X k)
  have hn : Dw.dim = (U.X k).Ψ.card * (Dw.p * Dw.q) := by rw [Datum.dim, hcard, mul_assoc]
  obtain ⟨W, a, ψ, hWo, haW, hψW, hψd, hψa, hinj⟩ := GlobalTheory.UnifSlice.exists_slice E H Dw l Xo c σ U hσ hU k x₀ Dw.dim hn
  have hU' : Formalism.L2.Pj.IsUnf U.toPj := (Formalism.L2.PjFree.isUnf_ofPj U.toPj).1 hU
  let sf : Frame (U.X k).Ψ (Dw.p + Dw.q) → (U.X k).dom := fun x =>
    if h : x ∈ (U.X k).dom then ⟨x, h⟩ else x₀
  have hsf : ∀ x (h : x ∈ (U.X k).dom), sf x = ⟨x, h⟩ := fun x h => dif_pos h
  have h1 := BdArc.Leave.isHolTo_ptC (U := U.toPj) hU' k sf fun x h => by rw [hsf x h]
  have h2 := LocLift.isHolTo_comp_hom h1 T.Z.jQ
  have hψ : DifferentiableOn ℂ ψ W :=
    differentiableOn_pi.2 fun τ => differentiableOn_pi.2 fun a => differentiableOn_pi.2 fun b => hψd τ a b
  have h3 := LocLift.isHolTo_comp h2 hWo hψ hψW
  let P : V Dw.dim → CxPts (genStr T.Z) σ := fun w => cxPt T.Z (U.un k (sf (ψ w)))
  have h4 : IsHolTo W fun w => (P w).1 := h3
  have hP : ∀ w, ∀ h : ψ w ∈ (U.X k).dom, cxPt T.Z (U.un k ⟨ψ w, h⟩) = P w := fun w h => by
    simp only [P, hsf _ h]
  have hc : ContinuousOn P W := GlobalTheory.TrueCx.TorHolo.continuousOn_of_isHolTo h4
  have hOo : IsOpen (W ∩ P ⁻¹' ch.e.source) := hc.isOpen_inter_preimage hWo ch.e.open_source
  have hqd : DifferentiableOn ℂ (fun w => ch.e (P w)) (W ∩ P ⁻¹' ch.e.source) := by
    rw [differentiableOn_euclidean]
    intro i
    have hd := (h4 ch.U (ch.x i)).2
    refine (hd.mono fun w hw => ⟨hw.1, ch.source_subset hw.2⟩).congr fun w hw => ?_
    show ch.e (P w) i = valAt' (P w).1 _ _
    rw [ch.apply_eq _ hw.2 i]
    have hq : ⊤ ≤ (P w).1 ⁻¹ᵁ ch.U := ch.source_subset hw.2
    rw [ev_eq (ch.source_subset hw.2), valAt', dif_pos hq]
    rfl
  have hPa : P a = y := by
    rw [← hP a (hψW a haW), ← hx₀]
    exact cxPt_congr (hψa _)
  have haO : a ∈ W ∩ P ⁻¹' ch.e.source := ⟨haW, by rw [Set.mem_preimage, hPa]; exact hyc⟩
  have hinjg : Set.InjOn (fun w => ch.e (P w)) (W ∩ P ⁻¹' ch.e.source) := by
    rintro w ⟨hw, hw'⟩ w' ⟨hw2, hw2'⟩ hg
    have hqq : P w = P w' := ch.e.injOn hw' hw2' hg
    refine hinj w hw w' hw2 (hψW w hw) (hψW w' hw2) (x_eq_of_cxPt (Z := T.Z) (congrArg Subtype.val ?_))
    rw [hP, hP, hqq]
  obtain ⟨h, hev⟩ := GlobalTheory.InjHol.exists_local_inverse_of_injOn Dw.dim _ _ a hOo haO hqd hinjg
  refine ⟨k, fun u => ψ (h u), ?_⟩
  rw [show ch.e y = ch.e (P a) by rw [hPa]]
  filter_upwards [hev] with u ⟨⟨huW, hux⟩, hgu, hdu⟩
  refine ⟨hψW _ huW, ?_, ?_⟩
  · rw [hP]
    exact (ch.e.left_inv hux).symm.trans (congrArg ch.e.symm hgu)
  · exact ((hψ _ huW).differentiableAt (hWo.mem_nhds huW)).comp u hdu

theorem isHodgeFrame_unfFam_iff {Z : Model Xo c β} {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Formalism.L2.PjFree.Unf Xo c σ r)
    {σ : c.F →+* ℂ} (hσ : Formalism.L2.PjFree.GoodEmb c σ) (y : CxPts (genStr Z) σ) (g : EigFrame Z σ (y.1 ≫ genι Z)) :
    IsHodgeFrame (unfFam (U σ)) y g ↔ IsHodgeFrame U y g := by
  have key : ∀ U₁ U₂ : ∀ σ : c.F →+* ℂ, Formalism.L2.PjFree.Unf Xo c σ r, U₁ σ = U₂ σ →
      IsHodgeFrame U₁ y g → IsHodgeFrame U₂ y g := by
    rintro U₁ U₂ e ⟨ψ, σ', k, x, rfl | rfl, h2, h3, h4⟩
    · obtain rfl : σ' = σ := h2
      have h : ∃ (k : (U₁ σ').Comp) (x : ((U₁ σ').X k).dom), ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth ((U₁ σ').X k) x.1 ∧
        (cxPt Z ((U₁ σ').un k x)).1 = spMap (RingHom.id ℂ) ≫ y.1 ∧
          g.IsMap (RingHom.id ℂ) (cxFrame Z ((U₁ σ').un k x)) := ⟨k, x, h4⟩
      rw [e] at h
      obtain ⟨k', x', h'⟩ := h
      exact ⟨_, σ', k', x', .inl rfl, rfl, hσ, h'⟩
    · exact (not_good_conj c (σ := σ) hσ (h2 ▸ h3)).elim
  have e : unfFam (U σ) σ = U σ := dif_pos rfl
  exact ⟨key _ _ e, key _ _ e.symm⟩

theorem eventually_analyticAt {d : ℕ} {g : V d → ℂ} {v₀ : Fin d → ℂ}
    (h : ∀ᶠ u in 𝓝 ((EuclideanSpace.equiv (Fin d) ℂ).symm v₀), DifferentiableAt ℂ g u) :
    ∀ᶠ v in 𝓝 v₀, AnalyticAt ℂ (fun w => g ((EuclideanSpace.equiv (Fin d) ℂ).symm w)) v := by
  have h1 : ∀ᶠ v in 𝓝 v₀, DifferentiableAt ℂ (fun w => g ((EuclideanSpace.equiv (Fin d) ℂ).symm w)) v :=
    (((EuclideanSpace.equiv (Fin d) ℂ).symm.continuous.tendsto v₀).eventually h).mono fun v hv =>
      hv.comp v (EuclideanSpace.equiv (Fin d) ℂ).symm.differentiableAt
  obtain ⟨S, hS, hSo, hv⟩ := eventually_nhds_iff.1 h1
  filter_upwards [hSo.mem_nhds hv] with v hvS
  exact (SCV.analyticOnNhd_iff_differentiableOn hSo).2 (fun w hw => (hS w hw).differentiableWithinAt) v hvS

theorem model_free (T : TorModel Y) {σ : c.F →+* ℂ} {r : ℕ} (hr : Dw.p + Dw.q = r) (U : Formalism.L2.PjFree.Unf Xo c σ r)
    (hσ : Formalism.L2.PjFree.GoodEmb c σ) (hU : Formalism.L2.PjFree.IsUnf U) {k' : Type} [CommRing k'] {Y' : Scheme.{0}}
    {p' : Y' ⟶ Sp k'} {σ' : k' →+* ℂ} {d : ℕ} {f : Y' ⟶ gen T.Z} {m : CxPts p' σ' → CxPts (genStr T.Z) σ}
    (hm : ∀ z, (m z).1 = z.1 ≫ f) (c' : AlgChart p' σ' d) (p0 : CxPts p' σ') (hp0 : p0 ∈ c'.e.source)
    (hb : ¬ LiesIn (m p0) (genBd T.Z)) (W : (gen T.Z).affineOpens) (φ : c.F →+* Γ(gen T.Z, W.1))
    (Fr : EigFrame T.Z φ (LogKS.chart W ≫ genι T.Z)) (hW : LogKS.chart W ≫ genStr T.Z = spMap φ)
    (h0 : m p0 ∈ ptsIn (genStr T.Z) σ W.1) :
    ∃ (G : V d → GlobalTheory.FlagBundle.Mat Dw.mult ℂ) (z : V d → GlobalTheory.AllWt.Psi H → Matrix (Fin Dw.p) (Fin Dw.q) ℂ)
      (cc : (E →+* ℂ) → ℝ), (∀ τ, 0 < cc τ) ∧
      ∀ᶠ u in 𝓝 (c'.e p0), (∀ τ a b, DifferentiableAt ℂ (fun w => G w τ a b) u) ∧
        (∀ τ a b, DifferentiableAt ℂ (fun w => z w τ a b) u) ∧ (∀ τ, IsUnit (G u τ).det) ∧
        GlobalTheory.PointChern.InDom (z u) ∧ ¬ LiesIn (m (c'.e.symm u)) (genBd T.Z) ∧
        ∃ hv : m (c'.e.symm u) ∈ ptsIn (genStr T.Z) σ W.1,
          ∀ g : EigFrame T.Z σ ((m (c'.e.symm u)).1 ≫ genι T.Z), Fr.IsMap (evHom hv) g → ∀ τ,
            ((hodgeMet T.Z U).gram (m (c'.e.symm u)) g τ)ᵀ =
              (cc τ : ℂ) • (G u τ * GlobalTheory.PointChern.modelGram H Dw (z u) τ * (G u τ)ᴴ) := by
  classical
  subst hr
  haveI := T.smooth
  obtain ⟨i, hi⟩ := (manifold T.Z σ).cover (m p0)
  set ch : AlgChart (genStr T.Z) σ Dw.dim := (manifold T.Z σ).chart i with hch
  obtain ⟨k, F₀, hF₀⟩ := exists_holo_frame T U hσ hU (m p0) hb ch hi
  have hmc : Continuous m := continuous_of_comp hm
  have hover : ∀ S : Set (CxPts (genStr T.Z) σ), IsOpen S → IsOpen (c'.e.target ∩ c'.e.symm ⁻¹' (m ⁻¹' S)) :=
    fun S hS => c'.e.continuousOn_symm.isOpen_inter_preimage c'.e.open_target (hS.preimage hmc)
  have hmem : ∀ S : Set (CxPts (genStr T.Z) σ), m p0 ∈ S → c'.e p0 ∈ c'.e.target ∩ c'.e.symm ⁻¹' (m ⁻¹' S) :=
    fun S hS => ⟨c'.e.map_source hp0, by rw [Set.mem_preimage, c'.e.left_inv hp0]; exact hS⟩
  let w : V d → V Dw.dim := ch.e ∘ m ∘ c'.e.symm
  have hS1 := (hover _ ch.e.open_source).mem_nhds (hmem _ hi)
  have hwd : ∀ᶠ u in 𝓝 (c'.e p0), DifferentiableAt ℂ w u := by
    filter_upwards [hS1] with u hu
    exact (AlgChart.holo_map hm c' ch).differentiableAt ((hover _ ch.e.open_source).mem_nhds hu)
  have hw0 : w (c'.e p0) = ch.e (m p0) := by simp only [w, Function.comp_apply, c'.e.left_inv hp0]
  have hwt : Tendsto w (𝓝 (c'.e p0)) (𝓝 (ch.e (m p0))) := hw0 ▸ hwd.self_of_nhds.continuousAt
  let F : V d → Frame (U.X k).Ψ (Dw.p + Dw.q) := fun u => F₀ (w u)
  have hF : ∀ᶠ u in 𝓝 (c'.e p0), ∃ h : F u ∈ (U.X k).dom,
      cxPt T.Z (U.un k ⟨F u, h⟩) = m (c'.e.symm u) ∧ DifferentiableAt ℂ F u := by
    filter_upwards [hwt.eventually hF₀, hwd, hS1] with u ⟨h, h1, h2⟩ h3 h4
    exact ⟨h, h1.trans (ch.e.left_inv h4.2), h2.comp u h3⟩
  let evv : V d → (Γ(gen T.Z, W.1) →+* ℂ) := fun u =>
    if h : m (c'.e.symm u) ∈ ptsIn (genStr T.Z) σ W.1 then evHom h else evHom h0
  have hev : ∀ u (h : m (c'.e.symm u) ∈ ptsIn (genStr T.Z) σ W.1), evv u = evHom h := fun u h => dif_pos h
  have hSo := hover _ (isOpen_ptsIn (p := genStr T.Z) (σ := σ) W.1)
  have hSn := hSo.mem_nhds (hmem _ h0)
  have hevd : ∀ t, ∀ᶠ u in 𝓝 (c'.e p0), DifferentiableAt ℂ (fun u => evv u t) u := by
    intro t
    filter_upwards [hSn] with u hu
    have hd := ((c'.holo (f ⁻¹ᵁ W.1) (f.app W.1 t)).mono fun v (hv : v ∈ c'.e.target ∩ c'.e.symm ⁻¹'
      (m ⁻¹' ptsIn (genStr T.Z) σ W.1)) => ⟨hv.1, (mem_ptsIn_preimage hm).2 hv.2⟩).differentiableAt (hSo.mem_nhds hu)
    refine hd.congr_of_eventuallyEq ?_
    filter_upwards [hSo.mem_nhds hu] with v hv
    rw [hev v hv.2, ← ev_eq hv.2, ev_of_comp hm]
    rfl
  have hfac : ∀ (y : CxPts (genStr T.Z) σ) (h : y ∈ ptsIn (genStr T.Z) σ W.1),
      spMap (evHom h) ≫ LogKS.chart W = y.1 := fun y h => GlobalTheory.Points.specMap_valMap_fromSpec W.2 y.1 h
  have hφ' : ∀ (y : CxPts (genStr T.Z) σ) (h : y ∈ ptsIn (genStr T.Z) σ W.1), (evHom h).comp φ = σ := by
    intro y h
    refine EigLoc.spMap_inj ?_
    rw [← y.2, ← hfac y h, Category.assoc, hW, ← Spec.map_comp]
    rfl
  have hφ : ∀ᶠ u in 𝓝 (c'.e p0), (evv u).comp φ = σ := by
    filter_upwards [hSn] with u hu
    rw [hev u hu.2]; exact hφ' _ _
  have hpt : ∀ᶠ u in 𝓝 (c'.e p0), ∃ h : F u ∈ (U.X k).dom, (cxPt T.Z (U.un k ⟨F u, h⟩)).1 ≫ genι T.Z =
      spMap (evv u) ≫ LogKS.chart W ≫ genι T.Z := by
    filter_upwards [hSn, hF] with u hu ⟨h, hc, _⟩
    refine ⟨h, ?_⟩
    rw [hc, hev u hu.2, ← Category.assoc, hfac]
  have hFd : ∀ τ' a b, ∀ᶠ u in 𝓝 (c'.e p0), DifferentiableAt ℂ (fun u => mat (F u) τ' a b) u := fun τ' a b =>
    hF.mono fun u ⟨_, _, h⟩ => differentiableAt_pi.1 (differentiableAt_pi.1 (differentiableAt_pi.1 h τ') a) b
  choose M hMd hMc using fun τ => GlobalTheory.HolCoordEv.coords_holomorphic E H Dw l Xo c O β T.Z σ U hσ hU d (c'.e p0)
    Γ(gen T.Z, W.1) φ _ Fr evv k F τ hevd hFd hφ hpt
  obtain ⟨G₀, z₀, cc, hcc, hG₀⟩ := GlobalTheory.HodgeGramGen.hodge_gram_frame E H Dw l Xo c O β T.Z σ U hσ hU k
  refine ⟨fun u τ => (M τ u)ᵀ * G₀ (F u) τ, fun u => z₀ (F u), cc, hcc, ?_⟩
  filter_upwards [hF, hSn, eventually_all.2 hMc,
    eventually_all.2 fun τ => eventually_all.2 fun a => eventually_all.2 fun b => hMd τ a b] with u ⟨h, hx, hd⟩ hu hc hM
  obtain ⟨g1, g2, g3, g4, g5⟩ := hG₀ (F u) h
  have hcomb : ∀ g : EigFrame T.Z σ ((m (c'.e.symm u)).1 ≫ genι T.Z), Fr.IsMap (evHom hu.2) g → ∀ τ i,
      IsCombAtG T.Z.t ((cxPt T.Z (U.un k ⟨F u, h⟩)).1 ≫ genι T.Z) ((cxFrame T.Z (U.un k ⟨F u, h⟩)).v τ)
        (fun b => M τ u b i) (g.v τ i) := by
    intro g hg τ i
    obtain ⟨_, h'⟩ := hc τ
    rw [hg τ i, ← hev u hu.2]
    exact h' i
  refine ⟨fun τ a b => ?_, fun τ a b => (g2 τ a b).differentiableAt.comp u hd, fun τ => ?_, g4,
    hx ▸ not_liesIn_cxPt _, hu.2, fun g hg τ => ?_⟩
  · simp only [Matrix.mul_apply, Matrix.transpose_apply]
    exact DifferentiableAt.fun_sum fun e _ => (hM τ e a).mul ((g1 τ e b).differentiableAt.comp u hd)
  · rw [Matrix.det_mul, Matrix.det_transpose]
    refine IsUnit.mul ?_ (g3 τ)
    have key : ∀ {x x' : Sp ℂ ⟶ T.Z.X} (hx : x = x') (g : EigFrame T.Z σ x) (G' : EigFrame T.Z σ x')
        (N : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ),
        (∀ i, IsCombAtG T.Z.t x' (G'.v τ) (fun b => N b i) (g.v τ i)) → IsUnit N.det := by
      intro x x' hx g G' N h
      subst hx
      rw [← EigFrame.co_eq (f := G') (g := g) h]
      exact EigFrame.isUnit_det_co _ _ _
    obtain ⟨g, hg⟩ := Fr.exists_isMap (evHom hu.2) (φ' := σ) (x' := (m (c'.e.symm u)).1 ≫ genι T.Z)
      (hφ' _ _).symm (by rw [← Category.assoc, hfac])
    exact key (by rw [hx]) g _ _ (hcomb g hg τ)
  · rw [GlobalTheory.HodgeOnDomain.eigGram_transport (hodgeMet T.Z U) hx.symm g (cxFrame T.Z (U.un k ⟨F u, h⟩)) τ
      (M τ u) (hcomb g hg τ), Matrix.transpose_mul, Matrix.transpose_mul, g5 τ]
    have e : (M τ u)ᴴᵀ = (M τ u)ᵀᴴ := rfl
    rw [e, Matrix.conjTranspose_mul]
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]

end GlobalTheory.HodgeFlagModel

end Free

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry ReciprocityTheory.AnForm.M GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam
open Filter Topology
open Matrix
open scoped ComplexOrder
open GlobalTheory.HodgeLocGeo
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Mean4O GlobalTheory.Mean4 ReciprocityTheory.AnForm GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ProjVar GlobalTheory GlobalTheory.CxPts

theorem GlobalTheory.HodgeFlagModel.hodge_gram_model_good : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (x : ToroidalCompactificationData s) (Φ : s.Flag) (k : s.Comp) (σ : D.what₂.LL →+* ℂ), Formalism.L2.PjFree.GoodEmb κ.c (embOf κ.e σ) → ∀ (d : ℕ) (c' : AlgChart (Φ.C k).Y.str σ d) (p0 : (Φ.C k).Y.pts σ), p0 ∈ c'.finChart.source → (Φ.C k).π (under p0) ∉ genBd s.T.Z →
    ∀ (V : (gen s.T.Z).affineOpens) (φ : κ.c.F →+* Γ(gen s.T.Z, V.1)) (Fr : EigFrame s.T.Z φ (LogKS.chart V ≫ genι s.T.Z)),
    LogKS.chart V ≫ genStr s.T.Z = spMap φ → (Φ.C k).down p0 ∈ ptsIn (genStr s.T.Z) (embOf κ.e σ) V.1 →
    ∃ (G : (Fin d → ℂ) → GlobalTheory.FlagBundle.Mat S.Dw.mult ℂ) (z : (Fin d → ℂ) → GlobalTheory.AllWt.Psi A.H → Matrix (Fin S.Dw.p) (Fin S.Dw.q) ℂ)
      (cc : (D.host.E →+* ℂ) → ℝ), (∀ τ, 0 < cc τ) ∧
      ∀ᶠ v in 𝓝 (c'.finChart p0), (∀ τ a b, AnalyticAt ℂ (fun w => G w τ a b) v) ∧
        (∀ τ a b, AnalyticAt ℂ (fun w => z w τ a b) v) ∧ (∀ τ, IsUnit (G v τ).det) ∧ GlobalTheory.PointChern.InDom (z v) ∧
        ∃ hv : (Φ.C k).down (c'.finChart.symm v) ∈ ptsIn (genStr s.T.Z) (embOf κ.e σ) V.1,
          ∀ f : (Φ.C k).FrameAt (c'.finChart.symm v), Fr.IsMap (evHom hv) f → ∀ τ,
            ((x.hodge (embOf κ.e σ)).gram ((Φ.C k).down (c'.finChart.symm v)) f τ)ᵀ =
              (cc τ : ℂ) • (G v τ * GlobalTheory.PointChern.modelGram A.H S.Dw (z v) τ * (G v τ)ᴴ) := by
  intro D A N j S κ s x Φ k σ hσ d c' p0 hp0 hb W φ Fr hW h0
  have hU := (s.unf _ hσ).1
  obtain ⟨G, z, cc, hcc, h⟩ := GlobalTheory.HodgeFlagModel.model_free s.T S.rank_eq (s.U (embOf κ.e σ)) hσ hU
    (f := (Φ.C k).π) (m := (Φ.C k).down) (fun _ => rfl) c' p0 hp0 hb W φ Fr hW h0
  let L := (EuclideanSpace.equiv (Fin d) ℂ).symm
  have hL : Tendsto L (𝓝 (c'.finChart p0)) (𝓝 (c'.e p0)) := L.continuous.tendsto (c'.finChart p0)
  refine ⟨fun v => G (L v), fun v => z (L v), fun τ => xiR D * cc τ, fun τ => mul_pos (xiR_pos D) (hcc τ), ?_⟩
  have hG : ∀ τ a b, ∀ᶠ v in 𝓝 (c'.finChart p0), AnalyticAt ℂ (fun w => G (L w) τ a b) v := fun τ a b =>
    GlobalTheory.HodgeFlagModel.eventually_analyticAt (g := fun u => G u τ a b) (h.mono fun u hu => hu.1 τ a b)
  have hz : ∀ τ a b, ∀ᶠ v in 𝓝 (c'.finChart p0), AnalyticAt ℂ (fun w => z (L w) τ a b) v := fun τ a b =>
    GlobalTheory.HodgeFlagModel.eventually_analyticAt (g := fun u => z u τ a b) (h.mono fun u hu => hu.2.1 τ a b)
  filter_upwards [hL.eventually h,
    eventually_all.2 fun τ => eventually_all.2 fun a => eventually_all.2 fun b => hG τ a b,
    eventually_all.2 fun τ => eventually_all.2 fun a => eventually_all.2 fun b => hz τ a b] with v hv h1 h2
  obtain ⟨-, -, h3, h4, h5, h6, h7⟩ := hv
  refine ⟨h1, h2, h3, h4, h6, fun f hf τ => ?_⟩
  have h8 := h7 f hf τ
  have hex : ∃ g, IsHodgeFrame (GlobalTheory.LieBase.unfFam (s.U (embOf κ.e σ))) ((Φ.C k).down (c'.e.symm (L v))) g := by
    obtain ⟨g, hg⟩ := FinalTheorems.exists_isHodgeFrame_iff.2 h5
    exact ⟨g, (GlobalTheory.HodgeFlagModel.isHodgeFrame_unfFam_iff s.U hσ _ g).2 hg⟩
  have h9 : (GlobalTheory.LieBase.hodgeMet s.T.Z (s.U (embOf κ.e σ))).gram ((Φ.C k).down (c'.e.symm (L v))) f τ =
      ((2 * Real.pi : ℝ) : ℂ) • ((hex.choose.co f τ)ᴴ * hex.choose.co f τ) := dif_pos hex
  have h10 := x.hodge_gram ((GlobalTheory.HodgeFlagModel.isHodgeFrame_unfFam_iff s.U hσ _ _).1 hex.choose_spec) f τ
  refine (congrArg Matrix.transpose h10).trans ?_
  rw [h9] at h8
  rw [Complex.ofReal_mul (xiR D), mul_smul, ← h8, ← Matrix.transpose_smul, smul_smul]
  congr 2
  push_cast
  ring
