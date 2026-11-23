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

namespace GlobalTheory.PoincPull

theorem smoothOn_chart_up_off_boundary : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (σ : κ.c.F →+* ℂ) [CompactSpace (CxPts (genStr s.T.Z) σ)] (m : ℕ) (α : LocPot (CxPts (genStr s.T.Z) σ)) (Λ : Fin m → LocPot (CxPts (genStr s.T.Z) σ)) (sg : Fin m → CxPts (genStr s.T.Z) σ → CxPts (genStr s.T.Z) σ → ℂ) (t : ℝ), IsBoundarySetting (manifold s.T.Z σ).finAtlas α Λ sg t → ∀ (Y : Scheme.{0}) (q : Y ⟶ Sp (𝓞 κ.c.F)) (jm : Y ⟶ s.T.Z.X) (hq : jm ≫ s.T.Z.s = q) (n : ℕ) (ch : AlgChart q (σ.comp (algebraMap (𝓞 κ.c.F) κ.c.F)) n), (∀ (W : (gen s.T.Z).Opens) (f : Γ(gen s.T.Z, W)), DifferentiableOn ℂ (ev (genStr s.T.Z) σ W f ∘ up jm hq σ ∘ ch.e.symm) (ch.e.target ∩ ch.e.symm ⁻¹' (up jm hq σ ⁻¹' ptsIn (genStr s.T.Z) σ W))) → ∀ (x : CxPts (genStr s.T.Z) σ) (y : CxPts q (σ.comp (algebraMap (𝓞 κ.c.F) κ.c.F))), y ∈ ch.e.source → up jm hq σ y ∉ boundary sg → up jm hq σ y ∈ α.U x → ∃ O : Set (V n), IsOpen O ∧ ch.e y ∈ O ∧ O ⊆ ch.e.target ∧ ContDiffOn ℝ ∞ (fun v => (poincarePot α Λ sg t).φ x (up jm hq σ (ch.e.symm v))) O := by
  intro D A N j S κ s σ _ m α Λ sg t hB Y q jm hq n ch hhol x y hy hyb hyx
  obtain ⟨O₁, hO₁, hyO₁, hO₁U, hO₁s⟩ := GlobalTheory.PoincSmooth.smoothOn_nhd_off_boundary _ _
    (manifold s.T.Z σ).finAtlas m α Λ sg t hB.1 (fun i => ⟨(hB.2.2.1 i).1, (hB.2.2.1 i).2.1⟩)
    (fun i => (hB.2.2.1 i).2.2.2) (up jm hq σ y) hyb
  set O' := O₁ ∩ α.U x with hO'def
  have hO' : IsOpen O' := hO₁.inter (α.isOpen_U x)
  obtain ⟨i, hi⟩ := (manifold s.T.Z σ).finAtlas.cover (up jm hq σ y)
  obtain ⟨c, hc⟩ := (manifold s.T.Z σ).isAlgAtlas_finAtlas i
  have hi' : up jm hq σ y ∈ c.e.source := by rw [hc] at hi; exact hi
  have hP : ∀ z' z, (poincarePot α Λ sg t).φ z' z = α.φ z' z + GlobalTheory.IndefiniteRowSideFullHecke.BoundaryPolynomialFunctions.pFun Λ sg t z / 2 :=
    fun _ _ => rfl
  have hg : ContDiffOn ℝ ∞ ((poincarePot α Λ sg t).φ x ∘ c.e.symm) (c.e.target ∩ c.e.symm ⁻¹' O') := by
    have h1 := hO₁s i
    have h2 := hB.1.1 (up jm hq σ y) i
    have h3 := hB.1.1 x i
    rw [hc] at h1 h2 h3
    have h1' := (c.contDiffOn_finChart_iff _ _ _).1 h1
    have h2' := (c.contDiffOn_finChart_iff _ _ _).1 h2
    have h3' := (c.contDiffOn_finChart_iff _ _ _).1 h3
    have h4 := ((h1'.mono fun w (hw : w ∈ c.e.target ∩ c.e.symm ⁻¹' O') => ⟨hw.1, hw.2.1⟩).sub
      (h2'.mono fun w (hw : w ∈ c.e.target ∩ c.e.symm ⁻¹' O') => ⟨hw.1, (hO₁U hw.2.1).1⟩)).add
      (h3'.mono fun w (hw : w ∈ c.e.target ∩ c.e.symm ⁻¹' O') => ⟨hw.1, hw.2.2⟩)
    refine h4.congr fun w _ => ?_
    simp only [Function.comp_apply, Pi.add_apply, Pi.sub_apply, hP]
    ring
  set O : Set (V n) := ch.e.target ∩ ch.e.symm ⁻¹' (up jm hq σ ⁻¹' (c.e.source ∩ O')) with hOdef
  have hOo : IsOpen O := ch.e.isOpen_inter_preimage_symm
    ((c.e.open_source.inter hO').preimage (continuous_up jm hq σ))
  have hF : ContDiffOn ℝ ∞ (fun w => c.e (up jm hq σ (ch.e.symm w))) O := by
    have hd : DifferentiableOn ℂ (fun w => c.e (up jm hq σ (ch.e.symm w))) O := by
      refine differentiableOn_euclidean.2 fun a => ?_
      refine ((hhol c.U (c.x a)).mono fun w hw => ⟨hw.1, c.source_subset hw.2.1⟩).congr fun w hw => ?_
      exact c.apply_eq _ hw.2.1 a
    exact (GlobalTheory.SCV.contDiffOn_of_differentiableOn hOo hd ∞).restrict_scalars ℝ
  refine ⟨O, hOo, ⟨ch.e.map_source hy, ?_⟩, Set.inter_subset_left, ?_⟩
  · show up jm hq σ (ch.e.symm (ch.e y)) ∈ c.e.source ∩ O'
    rw [ch.e.left_inv hy]
    exact ⟨hi', hyO₁, hyx⟩
  · refine (hg.comp hF fun w hw => ⟨c.e.map_source hw.2.1, ?_⟩).congr fun w hw => ?_
    · show c.e.symm (c.e (up jm hq σ (ch.e.symm w))) ∈ O'
      rw [c.e.left_inv hw.2.1]
      exact hw.2.2
    · simp only [Function.comp_apply]
      rw [c.e.left_inv hw.2.1]

end GlobalTheory.PoincPull
