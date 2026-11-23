import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondChernDensity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothOnNhdOffBoundary
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

namespace GlobalTheory.ArchLim.PotMeas

theorem isOpen_compl_boundary {d : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas d X) {m : ℕ}
    (Λ : Fin m → LocPot X) (sg : Fin m → X → X → ℂ) (h : ∀ i, IsSection A (Λ i) (sg i)) :
    IsOpen (boundary sg)ᶜ := by
  rw [isOpen_iff_forall_mem_open]
  intro x hx
  have hx' : ∀ i, sg i x x ≠ 0 := fun i h => hx ⟨i, h⟩
  refine ⟨⋂ i, ((Λ i).U x ∩ sg i x ⁻¹' {0}ᶜ), ?_, isOpen_iInter_of_finite fun i => ?_,
    Set.mem_iInter.2 fun i => ⟨(Λ i).mem_U x, hx' i⟩⟩
  · rintro z hz ⟨i, hi⟩
    have hz' := Set.mem_iInter.1 hz i
    have e := (h i).2 z x z ⟨(Λ i).mem_U _, hz'.1⟩
    have hi' : sg i z z = 0 := hi
    have hne : sg i x z ≠ 0 := hz'.2
    rw [hi', norm_zero, zero_mul] at e
    exact (mul_pos (norm_pos_iff.2 hne) (Real.exp_pos _)).ne e
  · exact (PoincSmooth.continuousOn_of_holoOn A ((h i).1 x)).isOpen_inter_preimage ((Λ i).isOpen_U x)
      isOpen_compl_singleton

theorem aemeasurable_potDens_of {k : Type} [CommRing k] {Y : Scheme.{0}} {q : Y ⟶ Sp k} {σ : k →+* ℂ} {n : ℕ}
    {X : Type} [TopologicalSpace X] (α P : LocPot X) {S : Set X} (hS : IsOpen S) {u : CxPts q σ → X}
    (hu : Continuous u) (ch : AlgChart q σ n)
    (h1 : ∀ (x : X) (y : CxPts q σ), y ∈ ch.e.source → u y ∈ S → u y ∈ α.U x →
      ∃ O : Set (V n), IsOpen O ∧ ch.e y ∈ O ∧ O ⊆ ch.e.target ∧
        ContDiffOn ℝ ∞ (fun v => P.φ x (u (ch.e.symm v))) O)
    (h2 : ∀ (x x' : X) (y : CxPts q σ), y ∈ ch.e.source → u y ∈ S → u y ∈ α.U x → u y ∈ α.U x' →
      cHess n (fun v => (P.φ x (u (ch.e.symm v)) : ℂ)) (ch.e y) =
        cHess n (fun v => (P.φ x' (u (ch.e.symm v)) : ℂ)) (ch.e y)) :
    AEMeasurable (fun v => potDens P S u ch (ch.e.symm v)) (volume.restrict ch.e.target) := by
  have hT : IsOpen (ch.e.target ∩ ch.e.symm ⁻¹' (u ⁻¹' S)) :=
    ch.e.isOpen_inter_preimage_symm (hS.preimage hu)
  set T := ch.e.target ∩ ch.e.symm ⁻¹' (u ⁻¹' S) with hTd
  let g : V n → ℝ := fun v => n.factorial * (2 / Real.pi) ^ n * (potMat P u ch (ch.e.symm v)).det.re
  have hc : ContinuousOn (fun v => potMat P u ch (ch.e.symm v)) T := by
    intro v hv
    obtain ⟨O, hO, hvO, -, hs⟩ := h1 (u (ch.e.symm v)) (ch.e.symm v) (ch.e.map_target hv.1) hv.2 (α.mem_U _)
    rw [ch.e.right_inv hv.1] at hvO
    have hs' : ContDiffOn ℝ ∞ (fun w => ((P.φ (u (ch.e.symm v)) (u (ch.e.symm w)) : ℝ) : ℂ)) O :=
      Complex.ofRealCLM.contDiff.comp_contDiffOn hs
    have hca : ContinuousAt
        (fun w => cHess n (fun w => ((P.φ (u (ch.e.symm v)) (u (ch.e.symm w)) : ℝ) : ℂ)) w) v :=
      continuousAt_pi.2 fun a => continuousAt_pi.2 fun b =>
        (ReciprocityTheory.L2DbarEstimates.Y.continuousOn_wd_wdb hO hs' a b).continuousAt (hO.mem_nhds hvO)
    refine ContinuousAt.continuousWithinAt (hca.congr ?_)
    have ho : IsOpen (ch.e.target ∩ ch.e.symm ⁻¹' (u ⁻¹' α.U (u (ch.e.symm v)))) :=
      ch.e.isOpen_inter_preimage_symm ((α.isOpen_U _).preimage hu)
    filter_upwards [ho.mem_nhds ⟨hv.1, α.mem_U _⟩, hT.mem_nhds hv] with w hw hw'
    unfold potMat
    rw [h2 (u (ch.e.symm w)) (u (ch.e.symm v)) (ch.e.symm w) (ch.e.map_target hw.1) hw'.2 (α.mem_U _) hw.2,
      ch.e.right_inv hw.1]
  have hg : ContinuousOn g T :=
    continuousOn_const.mul
      (Complex.continuous_re.comp_continuousOn ((continuous_id.matrix_det).comp_continuousOn hc))
  have hi : AEMeasurable (T.indicator g) (volume.restrict ch.e.target) :=
    ((aemeasurable_indicator_iff hT.measurableSet).2 (hg.aemeasurable hT.measurableSet)).restrict
  refine hi.congr ?_
  filter_upwards [ae_restrict_mem ch.e.open_target.measurableSet] with v hv
  unfold potDens
  by_cases hs : u (ch.e.symm v) ∈ S
  · rw [Set.indicator_of_mem (show v ∈ T from ⟨hv, hs⟩), if_pos hs]
  · rw [Set.indicator_of_notMem (fun h : v ∈ T => hs h.2), if_neg hs]

theorem aemeasurable_potDens_poincare : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (σ : κ.c.F →+* ℂ) [CompactSpace (CxPts (genStr s.T.Z) σ)] (m : ℕ) (α : LocPot (CxPts (genStr s.T.Z) σ)) (Λ : Fin m → LocPot (CxPts (genStr s.T.Z) σ)) (sg : Fin m → CxPts (genStr s.T.Z) σ → CxPts (genStr s.T.Z) σ → ℂ) (t : ℝ), IsBoundarySetting (manifold s.T.Z σ).finAtlas α Λ sg t → ∀ (Y : Scheme.{0}) (q : Y ⟶ Sp (𝓞 κ.c.F)) (jm : Y ⟶ s.T.Z.X) (hq : jm ≫ s.T.Z.s = q) (n : ℕ) (ch : AlgChart q (σ.comp (algebraMap (𝓞 κ.c.F) κ.c.F)) n), (∀ (x : CxPts (genStr s.T.Z) σ) (y : CxPts q (σ.comp (algebraMap (𝓞 κ.c.F) κ.c.F))), y ∈ ch.e.source → up jm hq σ y ∉ boundary sg → up jm hq σ y ∈ α.U x → ∃ O : Set (V n), IsOpen O ∧ ch.e y ∈ O ∧ O ⊆ ch.e.target ∧ ContDiffOn ℝ ∞ (fun v => (poincarePot α Λ sg t).φ x (up jm hq σ (ch.e.symm v))) O) → (∀ (x x' : CxPts (genStr s.T.Z) σ) (y : CxPts q (σ.comp (algebraMap (𝓞 κ.c.F) κ.c.F))), y ∈ ch.e.source → up jm hq σ y ∉ boundary sg → up jm hq σ y ∈ α.U x → up jm hq σ y ∈ α.U x' → cHess n (fun v => ((poincarePot α Λ sg t).φ x (up jm hq σ (ch.e.symm v)) : ℂ)) (ch.e y) = cHess n (fun v => ((poincarePot α Λ sg t).φ x' (up jm hq σ (ch.e.symm v)) : ℂ)) (ch.e y)) → AEMeasurable (fun v => potDens (poincarePot α Λ sg t) (boundary sg)ᶜ (up jm hq σ) ch (ch.e.symm v)) (volume.restrict ch.e.target) := by
  intro D A N j S κ s σ _ m α Λ sg t hB Y q jm hq n ch h1 h2
  exact aemeasurable_potDens_of α _ (isOpen_compl_boundary _ Λ sg fun i => (hB.2.2.1 i).2.1) (continuous_up jm hq σ) ch h1 h2

end GlobalTheory.ArchLim.PotMeas

end
