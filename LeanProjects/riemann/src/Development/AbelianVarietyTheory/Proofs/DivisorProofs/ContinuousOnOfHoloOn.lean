import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondChernDensity
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

noncomputable section

namespace GlobalTheory.IrrAn

open CategoryTheory AlgebraicGeometry Limits Topology Filter
open ReciprocityTheory.AnForm.M

variable {k : Type} [CommRing k] {X : Scheme.{0}}

def pt (p : X ⟶ Sp k) (σ : k →+* ℂ) (y : CxPts p σ) : Sp ℂ ⟶ pullback p (spMap σ) :=
  pullback.lift y.1 (𝟙 _) (y.2.trans (Category.id_comp _).symm)

def ptsOf (p : X ⟶ Sp k) (σ : k →+* ℂ) (T : Set (pullback p (spMap σ) : Scheme.{0})) :
    Set (CxPts p σ) :=
  {y | pt p σ y (IsLocalRing.closedPoint ℂ) ∈ T}

theorem ptsOf_mono {p : X ⟶ Sp k} {σ : k →+* ℂ} {T T' : Set (pullback p (spMap σ) : Scheme.{0})}
    (h : T ⊆ T') : ptsOf p σ T ⊆ ptsOf p σ T' := fun _ hy => h hy

def LocIdent {d : ℕ} {Y : Type} [TopologicalSpace Y] (A : FinHolAtlas d Y) (S : Set Y) : Prop :=
  ∀ x ∈ S, ∀ W : Set Y, IsOpen W → x ∈ W → ∃ N : Set Y, IsOpen N ∧ x ∈ N ∧ N ⊆ W ∧
    ∀ g : Y → ℂ, A.HoloOn W g → ∀ x' ∈ S ∩ N, (∀ᶠ y in 𝓝 x', y ∈ S → g y = 0) →
      ∀ y ∈ S ∩ N, g y = 0

theorem continuousOn_of_holoOn {d : ℕ} {Y : Type} [TopologicalSpace Y] (A : FinHolAtlas d Y)
    {W : Set Y} (hW : IsOpen W) {g : Y → ℂ} (hg : A.HoloOn W g) : ContinuousOn g W := by
  intro y hy
  obtain ⟨j, hj⟩ := A.cover y
  have h1 : (A.chart j) y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' W :=
    ⟨(A.chart j).map_source hj, by simpa [(A.chart j).left_inv hj] using hy⟩
  have h2 : ContinuousAt (g ∘ (A.chart j).symm) ((A.chart j) y) := (hg j _ h1).continuousAt
  have h3 : ContinuousAt (fun z => (g ∘ (A.chart j).symm) ((A.chart j) z)) y :=
    h2.comp ((A.chart j).continuousAt hj)
  refine (h3.congr ?_).continuousWithinAt
  filter_upwards [(A.chart j).open_source.mem_nhds hj] with z hz
  simp [(A.chart j).left_inv hz]

theorem isClosed_of_isAnalyticSubset {d : ℕ} {Y : Type} [TopologicalSpace Y] (A : FinHolAtlas d Y)
    {Z : Set Y} (hZ : A.IsAnalyticSubset Z) : IsClosed Z := by
  refine isClosed_of_closure_subset fun x hx => ?_
  obtain ⟨W, hW, hxW, r, f, hf, hZW⟩ := hZ x
  have hc : IsClosed {y : W | ∀ i, f i y = 0} := by
    simp only [Set.setOf_forall]
    refine isClosed_iInter fun i => isClosed_eq (f := fun y : W => f i y) ?_ continuous_const
    exact (continuousOn_iff_continuous_restrict.1 (continuousOn_of_holoOn A hW (hf i)))
  have hx' : (⟨x, hxW⟩ : W) ∈ closure {y : W | ∀ i, f i y = 0} := by
    rw [closure_subtype]
    refine mem_closure_iff.2 fun O hO hxO => ?_
    obtain ⟨z, hz⟩ := mem_closure_iff.1 hx (O ∩ W) (hO.inter hW) ⟨hxO, hxW⟩
    have : z ∈ Z ∩ W := ⟨hz.2, hz.1.2⟩
    rw [hZW] at this
    exact ⟨z, hz.1.1, ⟨z, this.1⟩, this.2, rfl⟩
  have := hc.closure_subset hx'
  have hm : x ∈ {y ∈ W | ∀ i, f i y = 0} := ⟨hxW, this⟩
  rw [← hZW] at hm
  exact hm.1

end GlobalTheory.IrrAn

end
