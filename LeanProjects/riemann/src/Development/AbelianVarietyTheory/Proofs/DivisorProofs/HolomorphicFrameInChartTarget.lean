import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondChernDensity
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EigenMetricSmoothOfHodge
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HodgeMetricSmoothOffBoundary
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineStableLieEigenspaceFrame
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalEquationComplexPoints
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsHolToOfOpenImmersion
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLinearEquivLift
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsHolomorphicLieFrame
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

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ArchLim.DRFrames

section Smooth

variable {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]

theorem contDiffOn_comp_of_isHolTo {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ} {d : ℕ}
    (R : AnRead p σ d) {S : Set (CxPts p σ)} (hS : IsOpen S) {f : CxPts p σ → ℝ} (hf : R.SmoothOn S f)
    {B : Set W} (hB : IsOpen B) {y : W → CxPts p σ} (hy : IsHolTo B fun b => (y b).1) :
    ContDiffOn ℝ ∞ (fun b => f (y b)) (B ∩ y ⁻¹' S) := by
  have hPc : ContinuousOn y B := TrueCx.TorHolo.continuousOn_of_isHolTo hy
  intro z hz
  obtain ⟨i, hi⟩ := R.cover (y z)
  have hB0 : IsOpen (B ∩ y ⁻¹' (S ∩ (R.chart i).e.source)) :=
    hPc.isOpen_inter_preimage hB (hS.inter (R.chart i).e.open_source)
  have hz0 : z ∈ B ∩ y ⁻¹' (S ∩ (R.chart i).e.source) := ⟨hz.1, hz.2, hi⟩
  have hd : DifferentiableOn ℂ (fun v => (R.chart i).e (y v)) (B ∩ y ⁻¹' (S ∩ (R.chart i).e.source)) :=
    fun w hw => (TrueCx.TorHolo.differentiableAt_chart hB hy (R.chart i) hw.1 hw.2.2).differentiableWithinAt
  have h1 : ContDiffAt ℝ ∞ (fun v => (R.chart i).e (y v)) z :=
    ((SCV.analyticOnNhd_of_differentiableOn hB0 hd z hz0).contDiffAt (n := ∞)).restrict_scalars ℝ
  have hO : IsOpen ((R.chart i).e.target ∩ (R.chart i).e.symm ⁻¹' S) := (R.chart i).e.isOpen_inter_preimage_symm hS
  have h2 : ContDiffAt ℝ ∞ (f ∘ (R.chart i).e.symm) ((R.chart i).e (y z)) :=
    (hf i).contDiffAt (hO.mem_nhds ⟨(R.chart i).e.map_source hi, by
      rw [Set.mem_preimage, (R.chart i).e.left_inv hi]; exact hz.2⟩)
  refine ((h2.comp z h1).congr_of_eventuallyEq ?_).contDiffWithinAt
  filter_upwards [hB0.mem_nhds hz0] with w hw
  simp only [Function.comp_apply, (R.chart i).e.left_inv hw.2.2]

end Smooth

section Up

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
  {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l}
  {c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} {Oz : Type} [CommRing Oz] {β : Oz →+* c.F}
  {Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β}

theorem isHolTo_up_symm {Y : Scheme.{0}} {q : Y ⟶ Sp Oz} (j : Y ⟶ Z.X) (hj : j ≫ Z.s = q) (σ : c.F →+* ℂ) {n : ℕ}
    (ch : AlgChart q (σ.comp β) n) : IsHolTo ch.e.target fun u => (up j hj σ (ch.e.symm u)).1 := by
  let L := EuclideanSpace.equiv (Fin n) ℂ
  have hB' : IsOpen (L.symm ⁻¹' ch.e.target) := ch.e.open_target.preimage L.symm.continuous
  have h1 : IsHolTo (L.symm ⁻¹' ch.e.target) fun w => (up j hj σ (ch.e.symm (L.symm w))).1 := by
    refine TrueCx.TorHolo.isHolTo_of_fst _ _ hB' (spMap σ) (fun w => (up j hj σ (ch.e.symm (L.symm w))).2) ?_
    refine LocLift.isHolTo_congr (LocLift.isHolTo_comp (LocLift.isHolTo_comp_hom (TrueCx.TorHolo.isHolTo_symm ch) j)
      hB' L.symm.differentiable.differentiableOn fun w hw => hw) fun w _ => up_ι _ _ _ _
  refine LocLift.isHolTo_congr (LocLift.isHolTo_comp h1 ch.e.open_target L.differentiable.differentiableOn
    fun u hu => by simpa using hu) fun u _ => by simp

end Up

end GlobalTheory.ArchLim.DRFrames

namespace GlobalTheory.ArchLim.DRFrames

theorem exists_frames_chart : ∀ (D : D7) (O : Setup D) (c : O.s.Comp) (M : DRBase O c) (Y : Scheme.{0}) (i : Y ⟶ M.B) (hi : (i ≫ M.b) ≫ O.s.T.Z.s = i ≫ M.q) (σ : O.κ.c.F →+* ℂ) (e : ℕ) (ch : AlgChart (i ≫ M.q) (σ.comp _) (e + 2)), ∀ y ∈ ch.e.source, ∃ (U : Set (V (e + 2))) (a : V (e + 2) → CxFr O.s.T.Z σ), IsOpen U ∧ ch.e y ∈ U ∧ U ⊆ ch.e.target ∧ HolFam U a ∧ ContinuousOn (fun u => (a u).1) U ∧ (∀ u ∈ U, (a u).1 = up (i ≫ M.b) hi σ (ch.e.symm u)) ∧ ∀ R : ℝ, ∀ τ, IsPosFrame U (eigGram (M.x.eigMetAt σ (some R)) a τ) := by
  intro D O c M Y i hi σ e ch y hy
  have hsm := O.s.T.smooth
  let P : V (e + 2) → CxPts (genStr O.s.T.Z) σ := fun u => up (i ≫ M.b) hi σ (ch.e.symm u)
  have hPc : ContinuousOn P ch.e.target :=
    (continuous_up (i ≫ M.b) hi σ).comp_continuousOn ch.e.continuousOn_symm
  have hPh : IsHolTo ch.e.target fun u => (P u).1 := isHolTo_up_symm (i ≫ M.b) hi σ ch
  obtain ⟨V₀, hV₀, φ₀, Fr₀, hz, hs₀, -⟩ := EigSpread.exists_stable_eigFrame _ _ _ _ _ _ _ _ O.s.T.Z
    ((P (ch.e y)).1 (IsLocalRing.closedPoint ℂ))
  let U : Set (V (e + 2)) := ch.e.target ∩ P ⁻¹' ptsIn (genStr O.s.T.Z) σ V₀
  have hU : IsOpen U := hPc.isOpen_inter_preimage ch.e.open_target (isOpen_ptsIn _)
  have hyU : ch.e y ∈ U := ⟨ch.e.map_source hy, CxPts.mem_ptsIn.2 hz⟩
  have hpt : ∀ q (hq : q ∈ ptsIn (genStr O.s.T.Z) σ V₀), spMap (evHom hq) ≫ hV₀.fromSpec = q.1 :=
    fun q hq => Points.specMap_valMap_fromSpec hV₀ q.1 hq
  have hφ : ∀ q (hq : q ∈ ptsIn (genStr O.s.T.Z) σ V₀), σ = (evHom hq).comp φ₀ := fun q hq =>
    EigLoc.spMap_inj (by rw [← q.2, ← hpt q hq, Category.assoc, hs₀, ← Spec.map_comp]; rfl)
  have hx : ∀ q (hq : q ∈ ptsIn (genStr O.s.T.Z) σ V₀),
      q.1 ≫ genι O.s.T.Z = spMap (evHom hq) ≫ hV₀.fromSpec ≫ genι O.s.T.Z := fun q hq => by
    rw [← Category.assoc, hpt q hq]
  choose fr hfr using fun q hq => Fr₀.exists_isMap (evHom hq) (hφ q hq) (hx q hq)
  let a : V (e + 2) → CxFr O.s.T.Z σ := fun u =>
    if h : P u ∈ ptsIn (genStr O.s.T.Z) σ V₀ then ⟨P u, fr _ h⟩ else ⟨P (ch.e y), fr _ hyU.2⟩
  have ha : ∀ u (hu : u ∈ U), a u = ⟨P u, fr _ hu.2⟩ := fun u hu => dif_pos hu.2
  have hPU : IsHolTo U fun u => (P u).1 := LocLift.isHolTo_mono hPh hU Set.inter_subset_left
  let ev' : V (e + 2) → (Γ(gen O.s.T.Z, V₀) →+* ℂ) := fun u =>
    if h : P u ∈ ptsIn (genStr O.s.T.Z) σ V₀ then evHom h else evHom hyU.2
  have hev' : ∀ u (hu : u ∈ U), ev' u = evHom hu.2 := fun u hu => dif_pos hu.2
  have hdev : ∀ r : Γ(gen O.s.T.Z, V₀), DifferentiableOn ℂ (fun u => ev' u r) U := fun r u hu =>
    (HolLieFrame.differentiableAt_ev hPU hV₀.fromSpec ev'
      (fun b hb => by rw [hev' b hb]; exact (hpt _ hb.2).symm) hu r).differentiableWithinAt
  refine ⟨U, a, hU, hyU, Set.inter_subset_left, ⟨?_, fun ρ k => ?_⟩, ?_, fun u hu => by rw [ha u hu], fun R τ => ?_⟩
  · exact LocLift.isHolTo_congr hPU fun u hu => by rw [ha u hu]
  · refine HolFrames.holTan_dualMap hU (Fr₀.v ρ k) (fun u hu => evHom hu.2)
      (fun r => ⟨fun u => ev' u r, hdev r, fun u hu => by show _ = ev' u r; rw [hev' u hu]⟩) (fun u hu => ?_)
    rw [ha u hu]
    exact hfr _ hu.2 ρ k
  · exact (hPc.mono Set.inter_subset_left).congr fun u hu => by rw [ha u hu]
  · have hGs : (M.x.eigMetAt σ (some R)).SmoothOn (manifold O.s.T.Z σ) Set.univ := by
      have e' : M.x.wt σ R = M.x.wt σ (max R 2) := funext fun y => by simp only [ToroidalCompactificationData.wt, max_assoc, max_self]
      have e : M.x.eigMetAt σ (some R) = M.x.eigMetAt σ (some (max R 2)) := by simp only [ToroidalCompactificationData.eigMetAt, e']
      rw [e]
      exact ToroidalCompactificationData.smoothOn_eigMetAt_some _ _ _ _ _ _ _ M.x σ _ (le_max_right _ _)
        (ToroidalCompactificationData.hodge_smoothOn _ _ _ _ _ _ _ M.x σ)
    choose gf hre him hgf using fun k k' => hGs ⟨V₀, hV₀⟩ φ₀ Fr₀ τ k k' hs₀
    have hg : ∀ k k', ∀ u ∈ U, eigGram (M.x.eigMetAt σ (some R)) a τ u k k' = gf k' k (P u) := by
      intro k k' u hu
      simp only [eigGram, Matrix.transpose_apply]
      rw [ha u hu]
      exact hgf k' k (P u) trivial hu.2 (fr _ hu.2) (hfr _ hu.2)
    refine ⟨hU, fun k k' => ?_, fun u _ => ((M.x.eigMetAt σ (some R)).pos _ _ τ).transpose⟩
    have hsub : U ⊆ U ∩ P ⁻¹' (Set.univ ∩ ptsIn (genStr O.s.T.Z) σ V₀) := fun u hu => ⟨hu, trivial, hu.2⟩
    have h1 := (contDiffOn_comp_of_isHolTo (manifold O.s.T.Z σ) (isOpen_univ.inter (isOpen_ptsIn _)) (hre k' k) hU
      hPU).mono hsub
    have h2 := (contDiffOn_comp_of_isHolTo (manifold O.s.T.Z σ) (isOpen_univ.inter (isOpen_ptsIn _)) (him k' k) hU
      hPU).mono hsub
    have h3 := (Complex.ofRealCLM.contDiff.comp_contDiffOn h1).add
      ((Complex.ofRealCLM.contDiff.comp_contDiffOn h2).mul (contDiffOn_const (c := Complex.I)))
    refine h3.congr fun u hu => ?_
    rw [hg k k' u hu]
    simp only [Function.comp_apply, Complex.ofRealCLM_apply]
    exact (Complex.re_add_im _).symm

end GlobalTheory.ArchLim.DRFrames

end
