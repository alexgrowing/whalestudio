import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpMapCompSpMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedIrreducibleAnalyticStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsChartOffClosedSubsetStatement
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsCompatChartRestrOpen
import ReciprocityTheory.AnalyticForms.PotentialTheory.Degree
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteIrreducibleComponentsComplexFibreStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RangeUniformizationEqPointsOfSubvarietyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedImmersionGenericComplexFibreStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexComponentAvoidsProperClosedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraicChartIrreducibleComponentLocalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraicChartLocalAnalyticParamStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximalIrreducibleAbelianLocusComponentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrreducibleComponentsNoetherianFiniteStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NoetherianSpaceGenericComplexFibreStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocallyOfFiniteTypeGenericFibreStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrreducibleAnalyticInFiniteUnionStatement
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
open GlobalTheory.HorComp
set_option autoImplicit false

theorem _root_.GlobalTheory.HorComp.analytic_components : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (x : ToroidalCompactificationData s) (σ : κ.c.F →+* ℂ) [CompactSpace (CxPts (genStr s.T.Z) σ)] (Y : Scheme.{0}) [IsIntegral Y] (q : Y ⟶ Sp _) (jm : Y ⟶ s.T.Z.X) [IsClosedImmersion jm] (hq : jm ≫ s.T.Z.s = q) (n : ℕ), IsArithVar q n → jm (genericPoint Y) ∈ abLocus s.T.Z.t.G → ∃ (m : ℕ) (Zs : Fin m → Set (CxPts (genStr s.T.Z) σ)) (T₀ : Set Y), IsClosed T₀ ∧ genericPoint Y ∉ T₀ ∧ (∀ a, IsIrreducibleAnalytic (manifold s.T.Z σ).finAtlas (Zs a) ∧ (regularLocus (manifold s.T.Z σ).finAtlas (Zs a) n).Nonempty ∧ Zs a ⊆ Set.range (up jm hq σ)) ∧ (∀ y : CxPts q (σ.comp _), y.1 (IsLocalRing.closedPoint ℂ) ∉ T₀ → ∃ a W, IsOpen W ∧ up jm hq σ y ∈ W ∧ W ∩ Set.range (up jm hq σ) = W ∩ Zs a) ∧ (∀ a (T : Set Y), IsClosed T → genericPoint Y ∉ T → ∃ y : CxPts q (σ.comp _), up jm hq σ y ∈ Zs a ∧ y.1 (IsLocalRing.closedPoint ℂ) ∉ T) ∧ ∀ a C, IsIrreducibleComponent (manifold s.T.Z σ).finAtlas (Zs a ∩ {y | ¬ Inner y}) C → ∀ T : Set Y, IsClosed T → (∀ y : CxPts q (σ.comp _), up jm hq σ y ∈ C → y.1 (IsLocalRing.closedPoint ℂ) ∈ T) → ∃ v ∈ T, jm v ∉ abLocus s.T.Z.t.G ∧ CharZero (Y.residueField v) ∧ Order.coheight v = 1 := by
  intro D A N j S κ s x σ _ Y _ q jm _ hq n hY hgen
  classical
  have hfin := GlobalTheory.T.finite_irreducible_components_complex_fibre _ _ (algebraMap (𝓞 κ.c.F) κ.c.F) Y q σ n hY
  set Fs := hfin.toFinset with hFs
  set e := Fs.equivFin with he
  set comp : Fin Fs.card → Set (cxFib (algebraMap (𝓞 κ.c.F) κ.c.F) q σ) := fun a => (e.symm a).1 with hcompdef
  have hcomp : ∀ a, comp a ∈ irreducibleComponents (cxFib (algebraMap (𝓞 κ.c.F) κ.c.F) q σ) := fun a => hfin.mem_toFinset.1 (e.symm a).2
  have hinj : ∀ a b, comp a = comp b → a = b := fun a b h => e.symm.injective (Subtype.ext h)
  haveI hci := GlobalTheory.T.isClosedImmersion_generic_complex_fibre D A N j S κ s σ Y q jm hq n hY
  have hce : Topology.IsClosedEmbedding (toGenCx jm hq σ) := (toGenCx jm hq σ).isClosedEmbedding
  have hcl : ∀ a, IsClosed (toGenCx jm hq σ '' comp a) := fun a =>
    hce.isClosedMap _ (isClosed_of_mem_irreducibleComponents _ (hcomp a))
  have hir : ∀ a, _root_.IsIrreducible (toGenCx jm hq σ '' comp a) := fun a =>
    (hcomp a).1.image _ hce.continuous.continuousOn
  haveI := GlobalTheory.T.locallyOfFiniteType_generic_fibre D A N j S κ s
  have hirrT : ∀ W : Set (genCx s.T.Z σ), IsClosed W → _root_.IsIrreducible W →
      IsIrreducibleAnalytic (manifold s.T.Z σ).finAtlas (ptsOf s.T.Z W) := fun W h1 h2 =>
    GlobalTheory.T.closed_irreducible_analytic _ _ (genStr s.T.Z) σ _ (manifold s.T.Z σ) W h1 h2
  have hZa : ∀ a, IsIrreducibleAnalytic (manifold s.T.Z σ).finAtlas (ptsOf s.T.Z (toGenCx jm hq σ '' comp a)) :=
    fun a => hirrT _ (hcl a) (hir a)
  have hZcl : ∀ a, IsClosed (ptsOf s.T.Z (toGenCx jm hq σ '' comp a)) := fun a =>
    ReciprocityTheory.AnForm.M.isClosed_of_isAnalyticSubset _ (hZa a).1
  have hrange : Set.range (up jm hq σ) = ⋃ a, ptsOf s.T.Z (toGenCx jm hq σ '' comp a) := by
    rw [GlobalTheory.T.range_uniformization_eq_points_of_subvariety D A N j S κ s σ Y q jm hq n hY]
    ext z
    simp only [ptsOf, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_range, Set.mem_image]
    constructor
    · rintro ⟨w, hw⟩
      have hC := irreducibleComponent_mem_irreducibleComponents w
      refine ⟨e ⟨irreducibleComponent w, hfin.mem_toFinset.2 hC⟩, w, ?_, hw⟩
      simp only [hcompdef, Equiv.symm_apply_apply]
      exact mem_irreducibleComponent
    · rintro ⟨a, w, -, hw⟩
      exact ⟨w, hw⟩
  have hsub : ∀ a, ptsOf s.T.Z (toGenCx jm hq σ '' comp a) ⊆ Set.range (up jm hq σ) := fun a => by
    rw [hrange]; exact Set.subset_iUnion (fun a => ptsOf s.T.Z (toGenCx jm hq σ '' comp a)) a
  obtain ⟨T₀, hT₀c, hT₀g, hT₀⟩ := GlobalTheory.T.exists_chart_off_closed_subset _ Y q n hY
  have hloc : ∀ y : CxPts q (σ.comp (algebraMap (𝓞 κ.c.F) κ.c.F)), y.1 (IsLocalRing.closedPoint ℂ) ∉ T₀ → ∀ a,
      up jm hq σ y ∈ ptsOf s.T.Z (toGenCx jm hq σ '' comp a) → ∃ W, IsOpen W ∧ up jm hq σ y ∈ W ∧
        W ∩ Set.range (up jm hq σ) = W ∩ ptsOf s.T.Z (toGenCx jm hq σ '' comp a) := by
    intro y hy a ha
    obtain ⟨ch, hch⟩ := hT₀ (σ.comp (algebraMap (𝓞 κ.c.F) κ.c.F)) y hy
    refine ⟨(⋃ b ∈ Finset.univ.filter (fun b => up jm hq σ y ∉ ptsOf s.T.Z (toGenCx jm hq σ '' comp b)),
      ptsOf s.T.Z (toGenCx jm hq σ '' comp b))ᶜ, (isClosed_biUnion_finset fun b _ => hZcl b).isOpen_compl, ?_, ?_⟩
    · simp only [Set.mem_compl_iff, Set.mem_iUnion, Finset.mem_filter, Finset.mem_univ, true_and, exists_prop,
        not_exists, not_and]
      exact fun b h1 h2 => h1 h2
    · ext z
      constructor
      · rintro ⟨hzW, hzr⟩
        refine ⟨hzW, ?_⟩
        rw [hrange] at hzr
        obtain ⟨b, hb⟩ := Set.mem_iUnion.1 hzr
        have hyb : up jm hq σ y ∈ ptsOf s.T.Z (toGenCx jm hq σ '' comp b) := by
          by_contra h
          exact hzW (Set.mem_biUnion (by simp [h]) hb)
        have := hinj _ _ (GlobalTheory.T.algebraic_chart_irreducible_component_local D A N j S κ s σ Y q jm hq n hY ch y hch _ (hcomp b) _ (hcomp a) hyb ha)
        exact this ▸ hb
      · rintro ⟨hzW, hza⟩
        exact ⟨hzW, hsub a hza⟩
  refine ⟨Fs.card, fun a => ptsOf s.T.Z (toGenCx jm hq σ '' comp a), T₀, hT₀c, hT₀g, ?_, ?_, ?_, ?_⟩
  · intro a
    refine ⟨hZa a, ?_, hsub a⟩
    obtain ⟨y, hyZ, hyT⟩ := GlobalTheory.T.complex_component_avoids_proper_closed D A N j S κ s σ Y q jm hq n hY (comp a) (hcomp a) T₀ hT₀c hT₀g
    obtain ⟨ch, hch⟩ := hT₀ _ y hyT
    obtain ⟨ψ, hψ, hyψ⟩ := GlobalTheory.T.algebraic_chart_local_analytic_param D A N j S κ s σ Y q jm hq n hY ch y hch
    obtain ⟨W, hWo, hyW, hWeq⟩ := hloc y hyT a hyZ
    refine ⟨up jm hq σ y, hyZ, ψ.restrOpen W hWo, ⟨hψ.1, ReciprocityTheory.AnForm.M.PLAux.isCompatChart_restrOpen hψ.2.1 hWo, ?_⟩, ⟨hyψ, hyW⟩⟩
    ext z
    have hz := Set.ext_iff.1 hψ.2.2 z
    have hw := Set.ext_iff.1 hWeq z
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq] at hz hw ⊢
    rw [ReciprocityTheory.AnForm.M.PLAux.restrOpen_source']
    simp only [Set.mem_inter_iff]
    change _ ↔ (z ∈ ψ.source ∧ z ∈ W) ∧ ∀ k : Fin _, n ≤ (k : ℕ) → ψ z k = 0
    tauto
  · intro y hy
    have : up jm hq σ y ∈ ⋃ a, ptsOf s.T.Z (toGenCx jm hq σ '' comp a) := hrange ▸ Set.mem_range_self y
    obtain ⟨a, ha⟩ := Set.mem_iUnion.1 this
    obtain ⟨W, hWo, hyW, hWeq⟩ := hloc y hy a ha
    exact ⟨a, W, hWo, hyW, hWeq⟩
  · intro a T hT hTg
    exact GlobalTheory.T.complex_component_avoids_proper_closed D A N j S κ s σ Y q jm hq n hY (comp a) (hcomp a) T hT hTg
  · intro a C hC T hT hTC
    set K := toGenCx jm hq σ '' comp a ∩ bdCx s.T.Z σ with hK
    have hKc : IsClosed K := (hcl a).inter ((genBd s.T.Z).isClosed.preimage (Limits.pullback.fst (genStr s.T.Z) (spMap σ)).continuous)
    haveI := GlobalTheory.T.noetherianSpace_generic_complex_fibre D A N j S κ s σ
    obtain ⟨hWf, hWu, hWc⟩ := GlobalTheory.T.irreducible_components_noetherian_finite _ K hKc
    set G := hWf.toFinset with hG
    set eG := G.equivFin with heG
    have hWi : ∀ i, Maximal (fun W : Set (genCx s.T.Z σ) => _root_.IsIrreducible W ∧ W ⊆ K) (eG.symm i).1 :=
      fun i => hWf.mem_toFinset.1 (eG.symm i).2
    have hCsub : C ⊆ ⋃ i, ptsOf s.T.Z (eG.symm i).1 := by
      intro z hz
      have hz' := hC.1.2 hz
      have hzK : ptOf s.T.Z z ∈ K := ⟨hz'.1, (mem_ptsOf_bdCx z).2 (not_not.1 hz'.2)⟩
      rw [← hWu] at hzK
      obtain ⟨W, hW, hzW⟩ := hzK
      refine Set.mem_iUnion.2 ⟨eG ⟨W, hWf.mem_toFinset.2 hW⟩, ?_⟩
      simp only [ptsOf, Set.mem_setOf_eq, Equiv.symm_apply_apply]
      exact hzW
    obtain ⟨i, hi⟩ := GlobalTheory.T.irreducible_analytic_in_finite_union _ _ (manifold s.T.Z σ).finAtlas C G.card (fun i => ptsOf s.T.Z (eG.symm i).1) hC.1.1
      (fun i => (hirrT _ (hWc _ (hWi i)) (hWi i).1.1).1) hCsub
    have hirrW := hirrT _ (hWc _ (hWi i)) (hWi i).1.1
    have hsubS : ptsOf s.T.Z (eG.symm i).1 ⊆ ptsOf s.T.Z (toGenCx jm hq σ '' comp a) ∩ {y | ¬ Inner y} := by
      intro z hz
      have hzK := (hWi i).1.2 hz
      exact ⟨hzK.1, fun h => h ((mem_ptsOf_bdCx z).1 hzK.2)⟩
    have hle := hC.2 ⟨hirrW, hsubS⟩ hi
    exact GlobalTheory.T.maximal_irreducible_abelian_locus_component D A N j S κ s x σ Y q jm hq n hY hgen (comp a) (hcomp a) _ (hWi i) T hT fun y hy => hTC y (hle hy)
