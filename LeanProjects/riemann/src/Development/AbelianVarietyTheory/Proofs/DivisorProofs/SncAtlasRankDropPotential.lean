import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSNCAtlasOfIsEmpty
import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffAtOfIsPotential
import ReciprocityTheory.AnalyticForms.PotentialTheory.Pullback
open MeasureTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.IndefiniteRowSideFullHecke.BoundaryPolynomialFunctions GlobalTheory.LogResInt GlobalTheory.SNCComp
open scoped ENNReal

namespace GlobalTheory.SNCRankDrop

open Filter Topology

theorem holoMap_comp {a b c : ℕ} {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] {A : FinHolAtlas a X} {B : FinHolAtlas b Y} {C : FinHolAtlas c Z}
    {μ : Y → X} {ν : Z → Y} (hμ : HoloMap B A μ) (hν : HoloMap C B ν) : HoloMap C A (μ ∘ ν) := by
  refine ⟨hμ.1.comp hν.1, fun j k z hz => ?_⟩
  obtain ⟨j₀, hj₀⟩ := B.cover (ν ((C.chart j).symm z))
  have h1 : AnalyticAt ℂ (B.chart j₀ ∘ ν ∘ (C.chart j).symm) z := hν.2 j j₀ z ⟨hz.1, hj₀⟩
  have h2 : AnalyticAt ℂ (A.chart k ∘ μ ∘ (B.chart j₀).symm)
      ((B.chart j₀ ∘ ν ∘ (C.chart j).symm) z) := by
    refine hμ.2 j₀ k _ ⟨(B.chart j₀).map_source hj₀, ?_⟩
    simp only [Function.comp_apply, Set.mem_preimage, (B.chart j₀).left_inv hj₀]
    exact hz.2
  refine (h2.comp h1).congr ?_
  filter_upwards [holoMap_preimage_mem_nhds hν j j₀ hz.1 hj₀] with y hy
  simp only [Function.comp_apply, (B.chart j₀).left_inv hy.2]

theorem analyticAt_compat {a b : ℕ} {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {A : FinHolAtlas a X} {B : FinHolAtlas b Y} {μ : Y → X} (hμ : HoloMap B A μ)
    {χ : OpenPartialHomeomorph Y (Fin b → ℂ)} (hχ : IsCompatChart B χ) (k : Fin A.n)
    {z : Fin b → ℂ} (hz : z ∈ χ.target) (hk : μ (χ.symm z) ∈ (A.chart k).source) :
    AnalyticAt ℂ (fun z => A.chart k (μ (χ.symm z))) z := by
  obtain ⟨j₀, hj₀⟩ := B.cover (χ.symm z)
  have h1 : AnalyticAt ℂ (B.chart j₀ ∘ χ.symm) z := (hχ j₀).2 z ⟨hz, hj₀⟩
  have h2 : AnalyticAt ℂ (A.chart k ∘ μ ∘ (B.chart j₀).symm) ((B.chart j₀ ∘ χ.symm) z) := by
    refine hμ.2 j₀ k _ ⟨(B.chart j₀).map_source hj₀, ?_⟩
    simp only [Function.comp_apply, Set.mem_preimage, (B.chart j₀).left_inv hj₀]
    exact hk
  refine (h2.comp h1).congr ?_
  filter_upwards [(χ.isOpen_inter_preimage_symm (B.chart j₀).open_source).mem_nhds ⟨hz, hj₀⟩]
    with y hy
  simp only [Function.comp_apply, (B.chart j₀).left_inv hy.2]

noncomputable def insZero {n : ℕ} (a : Fin (n + 1)) : (Fin n → ℂ) →L[ℂ] (Fin (n + 1) → ℂ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun z => Fin.insertNth a 0 z
      map_add' := fun x y => by
        funext b
        refine Fin.succAboveCases a ?_ (fun c => ?_) b <;> simp
      map_smul' := fun t x => by
        funext b
        refine Fin.succAboveCases a ?_ (fun c => ?_) b <;> simp }

theorem insZero_apply {n : ℕ} (a : Fin (n + 1)) (z : Fin n → ℂ) :
    insZero a z = Fin.insertNth a 0 z := rfl

theorem finrank_range_comp_le {E E' F G : Type} [AddCommGroup E] [AddCommGroup E'] [AddCommGroup F]
    [AddCommGroup G] [Module ℂ E] [Module ℂ E'] [Module ℂ F] [Module ℂ G] [Module.Finite ℂ F]
    (T : F →ₗ[ℂ] G) (D : E' →ₗ[ℂ] F) (I : E →ₗ[ℂ] E') (K : Submodule ℂ E')
    (hK : ∀ x, I x ∈ K) :
    Module.finrank ℂ (LinearMap.range (T ∘ₗ D ∘ₗ I)) ≤
      Module.finrank ℂ (LinearMap.range (D ∘ₗ K.subtype)) := by
  rw [LinearMap.range_comp (D ∘ₗ I) T]
  refine (Submodule.finrank_map_le _ _).trans (Submodule.finrank_mono ?_)
  rintro _ ⟨x, rfl⟩
  exact ⟨⟨I x, hK x⟩, rfl⟩

theorem mInt_eq_zero_of_rankDropAlong : ∀ (d n : ℕ) (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y] (A : FinHolAtlas d X)
    (B : FinHolAtlas (n + 1) Y) (μ : Y → X) (hμ : HoloMap B A μ) (q r : ℕ) (L : Fin q → LocPot X)
    (t : Fin q → X → X → ℂ) (W : Fin r → Set Y) (e : Fin q → Fin r → ℕ) (k : Fin r)
    (C : FinHolAtlas n (W k)), HoloMap C B Subtype.val → GlobalTheory.SNCComp.IsSNCAtlas B μ L t W e k C →
    RankDropAlong A μ B (W k) → ∀ Φ : Fin n → LocPot X, (∀ i, IsPotential A (Φ i)) →
    ∀ g : W k → ℝ, mInt C (fun i => ((Φ i).pullback μ hμ.1).pullback Subtype.val continuous_subtype_val) g = 0 := by
  intro d n X Y _ _ A B μ hμ q r L t W e k C hC hS hR Φ hΦ g
  refine rankDrop A C (μ ∘ Subtype.val) (holoMap_comp hμ hC) ?_ Φ hΦ g
  intro j k' z hz hk'
  obtain ⟨y, χ, κ, a, hχ, -, hκ, -, hW, -, hsrc, -, htgt, hsymm⟩ := hS j
  have hzt : insZero a z ∈ χ.target := by
    have := hz
    rw [htgt] at this
    exact this
  set w : Y := ((C.chart j).symm z).1 with hw
  have hwχ : w = χ.symm (insZero a z) := hsymm z hz
  have hws : w ∈ χ.source := hwχ ▸ χ.map_target hzt
  have hχw : χ w = insZero a z := by rw [hwχ, χ.right_inv hzt]
  have hWk : W k ∩ χ.source = {w' | w' ∈ χ.source ∧ χ w' a = 0} := by
    rw [hW k]
    ext v
    simp [hκ]
  have hlt := hR w ((C.chart j).symm z).2 χ a hχ hws hWk
  rw [hχw] at hlt
  set k₀ := chartIdx A (μ w) with hk₀
  have hk₀s : μ w ∈ (A.chart k₀).source := Classical.choose_spec (A.cover (μ w))
  have hk's : μ w ∈ (A.chart k').source := hk'
  set F : (Fin (n + 1) → ℂ) → (Fin d → ℂ) := fun z => A.chart k₀ (μ (χ.symm z)) with hF
  have hFa : AnalyticAt ℂ F (insZero a z) := analyticAt_compat hμ hχ k₀ hzt (hwχ ▸ hk₀s)
  have hFz : F (insZero a z) = A.chart k₀ (μ w) := by rw [hwχ]
  have hTa : AnalyticAt ℂ (A.chart k' ∘ (A.chart k₀).symm) (F (insZero a z)) := by
    rw [hFz]
    refine A.holo k₀ k' _ ⟨(A.chart k₀).map_source hk₀s, ?_⟩
    simp only [Set.mem_preimage, (A.chart k₀).left_inv hk₀s]
    exact hk's
  have hd : HasFDerivAt ((A.chart k' ∘ (A.chart k₀).symm) ∘ F ∘ insZero a)
      ((fderiv ℂ (A.chart k' ∘ (A.chart k₀).symm) (F (insZero a z))).comp
        ((fderiv ℂ F (insZero a z)).comp (insZero a))) z :=
    HasFDerivAt.comp z hTa.differentiableAt.hasFDerivAt
      (HasFDerivAt.comp z hFa.differentiableAt.hasFDerivAt (insZero a).hasFDerivAt)
  have heq : (A.chart k' ∘ (μ ∘ Subtype.val) ∘ (C.chart j).symm) =ᶠ[𝓝 z]
      ((A.chart k' ∘ (A.chart k₀).symm) ∘ F ∘ insZero a) := by
    filter_upwards [holoMap_preimage_mem_nhds (holoMap_comp hμ hC) j k₀ hz hk₀s] with v hv
    have h1 : ((C.chart j).symm v).1 = χ.symm (insZero a v) := hsymm v hv.1
    have h2 : μ (χ.symm (insZero a v)) ∈ (A.chart k₀).source := h1 ▸ hv.2
    simp only [Function.comp_apply, hF, h1, (A.chart k₀).left_inv h2]
  rw [(hd.congr_of_eventuallyEq heq).fderiv]
  refine lt_of_le_of_lt (finrank_range_comp_le
    (fderiv ℂ (A.chart k' ∘ (A.chart k₀).symm) (F (insZero a z))).toLinearMap
    (fderiv ℂ F (insZero a z)).toLinearMap (insZero a).toLinearMap
    (LinearMap.ker (LinearMap.proj a)) ?_) hlt
  intro x
  simp [insZero_apply]

end GlobalTheory.SNCRankDrop
