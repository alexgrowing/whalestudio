import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondChernDensity
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsContinuousOnFrameDirectionsInverse
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineStableLieEigenspaceFrame
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalEquationComplexPoints
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EigenMetricOnSet
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsHolToOfOpenImmersion
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsHolomorphicLieFrame
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.ExpRowsPf

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GramSmooth

section General

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.ShFam GlobalTheory.ShFam.Hor
open ReciprocityTheory.ChartRestriction.G.PullbackSections Filter
open scoped ContDiff CategoryTheory.Obj Topology

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

theorem snd_valR_comb {X : Scheme.{0}} {t : SAB H X} {x : Sp ℂ ⟶ X} {m : ℕ}
    {v : Fin m → (Sp (DualNumber ℂ) ⟶ t.G.left)} (ht : ∀ i, IsTanAtG t x (v i)) {a : Fin m → ℂ}
    {v' : Sp (DualNumber ℂ) ⟶ t.G.left} (ht' : IsTanAtG t x v') (hc : IsCombAtG t x v a v') (U : t.G.left.Opens)
    (h : ⊤ ≤ v' ⁻¹ᵁ U) (f : Γ(t.G.left, U)) :
    (valR (A := DualNumber ℂ) v' U f).snd = ∑ i, a i * (valR (A := DualNumber ℂ) (v i) U f).snd := by
  have hU : ∀ i, ⊤ ≤ v i ⁻¹ᵁ U := fun i => DerLin.le_of_fst_eq ((ht i).2.trans ht'.2.symm) h
  let b : Fin m → TanMod.TanSp x t.G := fun i =>
    TanMod.TanSp.mk (Over.homMk (v i) (ht i).1) (TanMod.smT_zero_of x _ (ht i).2)
  have key : (TanDeriv.evAt v' U h f).snd = ∑ i, a i * (TanDeriv.evAt (v i) U (hU i) f).snd := by
    refine TanDeriv.derivAt_sum b a v' ?_ U h hU f
    obtain ⟨u, hu, rfl⟩ := hc
    have hub : u = fun i => (a i • b i).pt := funext fun i => Over.OverMorphism.ext (hu i)
    subst hub
    rw [List.prod_ofFn, ← TanMod.TanSp.pt_sum]
  have e0 : valR (A := DualNumber ℂ) v' U f = TanDeriv.evAt v' U h f := dif_pos h
  have e1 : ∀ i, valR (A := DualNumber ℂ) (v i) U f = TanDeriv.evAt (v i) U (hU i) f := fun i => dif_pos (hU i)
  simp only [e0, e1]
  exact key

theorem differentiableAt_coord {X : Scheme.{0}} {t : SAB H X} {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]
    {B : Set W} {x : W → (Sp ℂ ⟶ X)} (hx : IsHolTo B x) {m : ℕ}
    {u : Fin m → W → (Sp (DualNumber ℂ) ⟶ t.G.left)} {w : W → (Sp (DualNumber ℂ) ⟶ t.G.left)}
    (hu : ∀ i, HolTan B (u i)) (hw : HolTan B w) (tu : ∀ b ∈ B, ∀ i, IsTanAtG t (x b) (u i b))
    (tw : ∀ b ∈ B, IsTanAtG t (x b) (w b)) {C : W → Fin m → ℂ}
    (hC : ∀ b ∈ B, IsCombAtG t (x b) (fun i => u i b) (C b) (w b)) {b₀ : W} (hb₀ : b₀ ∈ B)
    (hli : LinearIndependent ℂ fun i => tanOf (tu b₀ hb₀ i)) : DifferentiableAt ℂ C b₀ := by
  classical
  have hone : ∀ y : Sp ℂ ⟶ X, (1 : Over.mk y ⟶ t.G).left = y ≫ (1 : Over.mk (𝟙 X) ⟶ t.G).left := fun y => by
    let K : Over.mk y ⟶ Over.mk (𝟙 X) := Over.homMk y (by simp)
    exact (congrArg (·.left) (MonObj.comp_one K (M := t.G))).symm
  refine HolLieFrame.differentiableAt_of_forms _ b₀ fun a ha => ?_
  have key : ∀ a' : Fin m → ℂ, (∀ (U : t.G.left.Opens) (f : Γ(t.G.left, U)),
      ⊤ ≤ (show Sp ℂ ⟶ t.G.left from (1 : Over.mk (x b₀) ⟶ t.G).left) ⁻¹ᵁ U →
        ∑ i, a' i * (valR (A := DualNumber ℂ) (u i b₀) U f).snd = 0) →
      IsDerivAt0 (fun _ : Fin 0 → ℂ => (show Sp ℂ ⟶ t.G.left from (1 : Over.mk (x b₀) ⟶ t.G).left)) 0
        (tv (∑ i, a' i • tanOf (tu b₀ hb₀ i))).left := fun a' h' => by
    have ht := isTan_tv (∑ i, a' i • tanOf (tu b₀ hb₀ i))
    refine ⟨ht.2, fun U h f => ?_⟩
    have h1 := snd_valR_comb (tu b₀ hb₀) ht ((isComb_iff (fun i => tanOf (tu b₀ hb₀ i)) a' _).2 rfl) U h f
    rw [h' U f (by rw [← ht.2]; exact TanDeriv.comp_top_le _ _ U h), valR, dif_pos h] at h1
    rw [map_zero]
    exact h1
  have e := tan_ext (ExpRows.isDerivAt0_unique (key a fun U f hU => ?_) (key 0 fun U f _ => by simp))
  · simp only [Pi.zero_apply, zero_smul, Finset.sum_const_zero] at e
    exact funext (Fintype.linearIndependent_iff.1 hli a e)
  have hn : ∀ᶠ b in 𝓝 b₀, b ∈ B ∧ ∀ v, IsTanAtG t (x b) v → ⊤ ≤ v ⁻¹ᵁ U := by
    rw [hone] at hU
    filter_upwards [(hx ((show X ⟶ t.G.left from (1 : Over.mk (𝟙 X) ⟶ t.G).left) ⁻¹ᵁ U) 0).1.mem_nhds ⟨hb₀, hU⟩]
      with b hb
    refine ⟨hb.1, fun v hv => (TangentOrigin.top_le_preimage_iff _ U).2 ?_⟩
    have h2 := hv.2
    rw [hone] at h2
    exact h2 ▸ hb.2
  let L : W → ((Fin m → ℂ) →L[ℂ] ℂ) := fun b =>
    ∑ i, (valR (A := DualNumber ℂ) (u i b) U f).snd • ContinuousLinearMap.proj i
  have hL : ∀ b z, L b z = ∑ i, z i * (valR (A := DualNumber ℂ) (u i b) U f).snd := fun b z => by
    simp [L, mul_comm]
  rw [← hL]
  refine ha L (DifferentiableAt.fun_sum fun i _ => DifferentiableAt.smul_const ?_ _) ?_
  · exact (hu i U f).differentiableAt (hn.mono fun b hb => ⟨hb.1, hb.2 _ (tu b hb.1 i)⟩)
  · refine ((hw U f).differentiableAt (hn.mono fun b hb => ⟨hb.1, hb.2 _ (tw b hb.1)⟩)).congr_of_eventuallyEq ?_
    filter_upwards [hn] with b hb
    rw [hL]
    exact (snd_valR_comb (tu b hb.1) (tw b hb.1) (hC b hb.1) U (hb.2 _ (tw b hb.1)) f).symm

theorem contDiffAt_comp {K : Type} [CommRing K] {Y : Scheme.{0}} {p : Y ⟶ Sp K} {σ : K →+* ℂ} {D : ℕ}
    (R : AnRead p σ D) {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W] {B : Set W}
    (hB : IsOpen B) {y : W → CxPts p σ} (hy : IsHolTo B fun b => (y b).1) {S : Set (CxPts p σ)} (hS : IsOpen S)
    {f : CxPts p σ → ℝ} (hf : R.SmoothOn S f) {z : W} (hz : z ∈ B) (hzS : y z ∈ S) :
    ContDiffAt ℝ ∞ (fun v => f (y v)) z := by
  obtain ⟨i, hi⟩ := R.cover (y z)
  have hB0 : IsOpen (B ∩ y ⁻¹' (R.chart i).e.source) :=
    (TrueCx.TorHolo.continuousOn_of_isHolTo hy).isOpen_inter_preimage hB (R.chart i).e.open_source
  have hd : DifferentiableOn ℂ (fun v => (R.chart i).e (y v)) (B ∩ y ⁻¹' (R.chart i).e.source) := fun w hw =>
    (TrueCx.TorHolo.differentiableAt_chart hB hy (R.chart i) hw.1 hw.2).differentiableWithinAt
  have h1 : ContDiffAt ℝ ∞ (fun v => (R.chart i).e (y v)) z :=
    (SCV.contDiffAt_of_differentiableOn hd (hB0.mem_nhds ⟨hz, hi⟩) _).restrict_scalars ℝ
  have hO : IsOpen ((R.chart i).e.target ∩ (R.chart i).e.symm ⁻¹' S) := (R.chart i).e.isOpen_inter_preimage_symm hS
  have h2 : ContDiffAt ℝ ∞ (f ∘ (R.chart i).e.symm) ((R.chart i).e (y z)) :=
    (hf i).contDiffAt (hO.mem_nhds ⟨(R.chart i).e.map_source hi, by
      rw [Set.mem_preimage, (R.chart i).e.left_inv hi]; exact hzS⟩)
  refine (h2.comp z h1).congr_of_eventuallyEq ?_
  filter_upwards [hB0.mem_nhds ⟨hz, hi⟩] with w hw
  simp only [Function.comp_apply, (R.chart i).e.left_inv hw.2]

variable {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  {Z : Model Xo c β} {σ : c.F →+* ℂ}

theorem contDiffAt_gram {D : ℕ} (R : AnRead (genStr Z) σ D) (G : EigMet Z σ) {T : Set (CxPts (genStr Z) σ)}
    (hT : IsOpen T) (hG : G.SmoothOn R T) {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]
    {U : Set W} {a : W → CxFr Z σ} (hU : IsOpen U) (ha : HolFam U a) {u : W} (hu : u ∈ U) (huT : (a u).1 ∈ T)
    (τ : E →+* ℂ) (i k : Fin (Dw.mult τ)) : ContDiffAt ℝ ∞ (fun v => G.gram (a v).1 (a v).2 τ i k) u := by
  classical
  obtain ⟨V₀, hV₀, φ, F₀, hzV, hφ, -⟩ :=
    EigSpread.exists_stable_eigFrame E H Dw l Xo c O β Z ((a u).1.1 (IsLocalRing.closedPoint ℂ))
  let V : (gen Z).affineOpens := ⟨V₀, hV₀⟩
  let F : EigFrame Z φ (LogKS.chart V ≫ genι Z) := F₀
  have hφ' : LogKS.chart V ≫ genStr Z = spMap φ := hφ
  have huV : (a u).1 ∈ ptsIn (genStr Z) σ V.1 := CxPts.mem_ptsIn.2 hzV
  have hfr : ∀ (y : CxPts (genStr Z) σ) (hy : y ∈ ptsIn (genStr Z) σ V.1),
      ∃ f : EigFrame Z σ (y.1 ≫ genι Z), F.IsMap (evHom hy) f := fun y hy =>
    F.exists_isMap (evHom hy) (EigMet.eq_comp_evHom hφ' hy) (by rw [← Category.assoc, spMap_evHom hy])
  choose fr hfr using hfr
  let f : ∀ b : W, EigFrame Z σ ((a b).1.1 ≫ genι Z) := fun b =>
    if h : (a b).1 ∈ ptsIn (genStr Z) σ V.1 then fr _ h else (a b).2
  have hf : ∀ b (h : (a b).1 ∈ ptsIn (genStr Z) σ V.1), F.IsMap (evHom h) (f b) := fun b h => by
    rw [show f b = fr _ h from dif_pos h]
    exact hfr _ h
  have hcont := TrueCx.TorHolo.continuousOn_of_isHolTo (y := fun b => (a b).1) ha.1
  let B : Set W := U ∩ (fun b => (a b).1) ⁻¹' (T ∩ ptsIn (genStr Z) σ V.1)
  have hB : IsOpen B := hcont.isOpen_inter_preimage hU (hT.inter (isOpen_ptsIn _))
  have huB : u ∈ B := ⟨hu, huT, huV⟩
  have hyB : IsHolTo B fun b => (a b).1.1 := LocLift.isHolTo_mono ha.1 hB Set.inter_subset_left
  have hfT : ∀ j, HolTan B fun b => (f b).v τ j := fun j =>
    HolFrames.holTan_dualMap hB (F.v τ j) (fun b hb => evHom hb.2.2)
      (fun r => ⟨_, (hyB V.1 r).2.mono fun b hb => ⟨hb, hb.2.2⟩, fun b hb => (CxPts.ev_eq hb.2.2 r).symm⟩)
      fun b hb => hf b hb.2.2 τ j
  have hco : ∀ j j', ContDiffAt ℝ ∞ (fun b => (f b).co (a b).2 τ j j') u := fun j j' => by
    have hd : DifferentiableOn ℂ (fun b => (f b).co (a b).2 τ j j') B := fun b hb =>
      (differentiableAt_pi.1 (differentiableAt_coord (t := Z.t) (C := fun b j => (f b).co (a b).2 τ j j')
        (LocLift.isHolTo_comp_hom hyB (genι Z)) hfT (w := fun b => (a b).2.v τ j')
        (fun O g => (ha.2 τ j' O g).mono fun _ h => ⟨h.1.1, h.2⟩) (fun b _ j => (f b).tan τ j)
        (fun b _ => (a b).2.tan τ j') (fun b _ => (f b).co_spec (a b).2 τ j') hb
        ((f b).linearIndependent_vec τ)) j).differentiableWithinAt
    exact (SCV.contDiffAt_of_differentiableOn hd (hB.mem_nhds huB) _).restrict_scalars ℝ
  have hgr : ∀ j j', ContDiffAt ℝ ∞ (fun b => G.gram (a b).1 (f b) τ j j') u := fun j j' => by
    obtain ⟨g, hre, him, hg⟩ := hG V φ F τ j j' hφ'
    have h1 := contDiffAt_comp R hU ha.1 (hT.inter (isOpen_ptsIn _)) hre hu huB.2
    have h2 := contDiffAt_comp R hU ha.1 (hT.inter (isOpen_ptsIn _)) him hu huB.2
    refine ((Complex.ofRealCLM.contDiff.contDiffAt.comp u h1).add
      ((Complex.ofRealCLM.contDiff.contDiffAt.comp u h2).mul (contDiffAt_const (c := Complex.I)))).congr_of_eventuallyEq ?_
    filter_upwards [hB.mem_nhds huB] with b hb
    rw [hg _ hb.2.1 hb.2.2 _ (hf b hb.2.2)]
    simp [Complex.re_add_im]
  have e : (fun v => G.gram (a v).1 (a v).2 τ i k) = fun v => ∑ j', (∑ j, starRingEnd ℂ ((f v).co (a v).2 τ j i) *
      G.gram (a v).1 (f v) τ j j') * (f v).co (a v).2 τ j' k := funext fun v => by
    rw [G.change _ (f v) (a v).2 τ]
    rfl
  rw [e]
  exact ContDiffAt.sum fun j' _ => (ContDiffAt.sum fun j _ =>
    (Complex.conjCLE.contDiff.contDiffAt.comp u (hco j i)).mul (hgr j j')).mul (hco j' k)

end General

section Main

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory Matrix NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ArInt GlobalTheory.CovTest GlobalTheory.VdmRec GlobalTheory.ArchLim
open GlobalTheory.MixDens (part IsDens chernMat emb)
open GlobalTheory.FlagFibre (Low uni)
open ReciprocityTheory.L2DbarEstimates (V cHess bas)
open ReciprocityTheory.AnForm.M (LocPot FinHolAtlas IsPotential IsSection)
open GlobalTheory.IndefiniteRowSideFullHecke.BoundaryPolynomialFunctions (IsProjective IsIrreducibleAnalytic IsIrreducibleComponent regularLocus regIntegral normSec absLogNorm boundary rFun poincarePot IsBoundarySetting)
open Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Hor GlobalTheory.Mean4O
open scoped ContDiff ComplexOrder ENNReal Classical

theorem contDiffAt_eigGram : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (σ : κ.c.F →+* ℂ)
    (G : EigMet s.T.Z σ) (T : Set (CxPts (genStr s.T.Z) σ)), IsOpen T → G.SmoothOn (manifold s.T.Z σ) T →
    ∀ (n : ℕ) (U : Set (V n)) (a : V n → CxFr s.T.Z σ), IsOpen U → HolFam U a → ContinuousOn (fun u => (a u).1) U →
    ∀ u ∈ U, (a u).1 ∈ T → ∀ (τ : D.host.E →+* ℂ) i k, ContDiffAt ℝ (∞ : WithTop ℕ∞) (fun v => eigGram G a τ v i k) u := by
  intro D A N j S κ s σ G T hT hG n U a hU ha _ u hu huT τ i k
  exact contDiffAt_gram _ G hT hG hU ha hu huT τ k i

end Main

end GlobalTheory.GramSmooth
