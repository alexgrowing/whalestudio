import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSNCAtlasOfIsEmpty
import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffAtOfIsPotential
import ReciprocityTheory.AnalyticForms.PotentialTheory.SNCAtlas
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SncAtlasRankDropPotential
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundarySectionPullbackBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBdPullbackBoundary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveAtlasPositivePotentialStatement

open MeasureTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.IndefiniteRowSideFullHecke.BoundaryPolynomialFunctions GlobalTheory.LogResInt GlobalTheory.SNCComp
open ReciprocityTheory.AnForm.P GlobalTheory.Mean4O GlobalTheory.LogResCurv Filter Topology
open scoped ENNReal

namespace GlobalTheory.SNCCompBound

variable {d n : ℕ} {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

theorem isPosPot_restrict (B : FinHolAtlas (n + 1) Y) (μ : Y → X) {q r : ℕ} (L : Fin q → LocPot X)
    (t : Fin q → X → X → ℂ) (W : Fin r → Set Y) (e : Fin q → Fin r → ℕ) (k : Fin r)
    (C : FinHolAtlas n (W k)) (hC : HoloMap C B Subtype.val) (hS : IsSNCAtlas B μ L t W e k C)
    (P : LocPot Y) (hP : IsPotential B P) (hp : IsPosPot B P) :
    IsPosPot C (P.pullback Subtype.val continuous_subtype_val) := by
  intro y j z hz w hw
  obtain ⟨-, χ, -, a, hχ, -, -, -, -, -, -, -, htgt, hsymm⟩ := hS j
  obtain ⟨l, hl⟩ := B.cover ((C.chart j).symm z).1
  have hO : IsOpen ((C.chart j).target ∩ (C.chart j).symm ⁻¹' (Subtype.val ⁻¹' (B.chart l).source)) :=
    (C.chart j).isOpen_inter_preimage_symm ((B.chart l).open_source.preimage continuous_subtype_val)
  have hzO : z ∈ (C.chart j).target ∩ (C.chart j).symm ⁻¹' (Subtype.val ⁻¹' (B.chart l).source) := ⟨hz.1, hl⟩
  have han := hC.2 j l z hzO
  set F := B.chart l ∘ Subtype.val ∘ (C.chart j).symm with hF
  have hFz : (B.chart l).symm (F z) = ((C.chart j).symm z).1 := (B.chart l).left_inv hl
  have hin : F z ∈ (B.chart l).target ∩ (B.chart l).symm ⁻¹' P.U y.1 :=
    ⟨(B.chart l).map_source hl, by rw [Set.mem_preimage, hFz]; exact hz.2⟩
  have h1 : ContDiffAt ℝ 2 (P.φ y.1 ∘ (B.chart l).symm) (F z) :=
    (contDiffAt_of_isPotential B P hP y.1 l hin).of_le (by norm_cast)
  have heq : (P.pullback Subtype.val continuous_subtype_val).φ y ∘ (C.chart j).symm =ᶠ[𝓝 z]
      (P.φ y.1 ∘ (B.chart l).symm) ∘ F := by
    filter_upwards [hO.mem_nhds hzO] with z' hz'
    show P.φ y.1 ((C.chart j).symm z').1 = P.φ y.1 ((B.chart l).symm ((B.chart l) ((C.chart j).symm z').1))
    rw [(B.chart l).left_inv hz'.2]
  rw [levi_congr heq, levi_comp w han h1]
  refine hp _ l _ hin _ fun h0 => hw ?_
  have hmem : ∀ v ∈ (C.chart j).target, Fin.insertNth (α := fun _ => ℂ) a 0 v ∈ χ.target := fun v hv => by
    rw [htgt] at hv
    exact hv
  have hG : AnalyticAt ℂ (fun v => a.removeNth ((χ ∘ (B.chart l).symm) v)) (F z) :=
    SimpleNormalCrossingSliceCharts.analyticAt_removeNth_comp a ((hχ l).1 _ ⟨hin.1, by
      rw [Set.mem_preimage, hFz, hsymm z hz.1]
      exact χ.map_target (hmem z hz.1)⟩)
  have hid : id =ᶠ[𝓝 z] (fun v => a.removeNth ((χ ∘ (B.chart l).symm) v)) ∘ F := by
    filter_upwards [hO.mem_nhds hzO] with v hv
    show v = a.removeNth (χ ((B.chart l).symm ((B.chart l) ((C.chart j).symm v).1)))
    rw [(B.chart l).left_inv hv.2, hsymm v hv.1, χ.right_inv (hmem v hv.1), Fin.removeNth_insertNth]
  have hd := ((hG.differentiableAt.hasFDerivAt.comp z han.differentiableAt.hasFDerivAt).congr_of_eventuallyEq
    hid).unique (hasFDerivAt_id z)
  have h2 := congrArg (fun T => T w) hd
  simpa [h0] using h2.symm

theorem interior_zero_eq_empty (A : FinHolAtlas d X) (B : FinHolAtlas (n + 1) Y) (μ : Y → X) {q r : ℕ}
    (L : Fin q → LocPot X) (t : Fin q → X → X → ℂ) (W : Fin r → Set Y) (e : Fin q → Fin r → ℕ) (k : Fin r)
    (C : FinHolAtlas n (W k)) (hS : IsSNCAtlas B μ L t W e k C) (i : Fin q) (hi : IsSection A (L i) (t i))
    (he : e i k = 0) : interior {v : W k | t i (μ v.1) (μ v.1) = 0} = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro x hx
  obtain ⟨j, hj⟩ := C.cover x
  obtain ⟨y, χ, κ, a, -, -, hκ, hinj, -, hfac, -, -, htgt, hsymm⟩ := hS j
  obtain ⟨hU, u, -, hu0, hprod⟩ := hfac i
  have hO := (C.chart j).isOpen_inter_preimage_symm
    (isOpen_interior (s := {v : W k | t i (μ v.1) (μ v.1) = 0}))
  have hD : Dense {z : Fin n → ℂ | ∀ b, z b ≠ 0} := by
    have h : Dense (Set.pi Set.univ fun _ : Fin n => ({0}ᶜ : Set ℂ)) :=
      dense_pi Set.univ fun _ _ => dense_compl_singleton (0 : ℂ)
    refine Dense.mono ?_ h
    intro z hz b
    exact hz b trivial
  obtain ⟨z, ⟨hzt, hzi⟩, hz0⟩ := hD.inter_open_nonempty _ hO
    ⟨C.chart j x, (C.chart j).map_source hj, by rwa [Set.mem_preimage, (C.chart j).left_inv hj]⟩
  have hzχ : Fin.insertNth (α := fun _ => ℂ) a 0 z ∈ χ.target := by
    rw [htgt] at hzt
    exact hzt
  have h0 : t i (μ ((C.chart j).symm z).1) (μ ((C.chart j).symm z).1) = 0 :=
    interior_subset (s := {v : W k | t i (μ v.1) (μ v.1) = 0}) hzi
  rw [hsymm z hzt] at h0
  have hs := χ.map_target hzχ
  rw [LeviFormBoundaryTopology.bdry_iff hi (hU hs), hprod _ hs, χ.right_inv hzχ] at h0
  rcases mul_eq_zero.1 h0 with h1 | h1
  · exact hu0 _ hs h1
  · obtain ⟨k', -, hk'⟩ := Finset.prod_eq_zero_iff.1 h1
    revert hk'
    cases hb : κ k' with
    | none => simp
    | some b =>
      intro hk'
      obtain ⟨h2, h3⟩ := pow_eq_zero_iff'.1 hk'
      rcases Fin.eq_self_or_eq_succAbove a b with rfl | ⟨c, rfl⟩
      · exact h3 (hinj k' k _ hb hκ ▸ he)
      · rw [Fin.insertNth_apply_succAbove] at h2
        exact hz0 c h2

theorem component_term_bounded : ∀ (d : ℕ) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (A : FinHolAtlas d X) (m : ℕ) (α : LocPot X) (Λ : Fin m → LocPot X) (σ : Fin m → X → X → ℂ) (c : ℝ),
    IsBoundarySetting A α Λ σ c →
    ∀ (L : LocPot X) (s : X → X → ℂ), IsPotential A L → IsSection A L s → (∀ y, normSec L s y ≤ 1) →
    ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [CompactSpace Y] [T2Space Y] (B : FinHolAtlas (n + 1) Y),
    IsProjective B → ∀ (μ : Y → X) (hμ : HoloMap B A μ) (r : ℕ) (W : Fin r → Set Y)
    (e : Fin (m + 1) → Fin r → ℕ),
    IsJointSNC B μ (Fin.cons L Λ) (Fin.cons s σ) W e →
    ∀ (w : ℕ → X → ℝ) (K : ℝ), (∀ R, A.Smooth (w R)) → (∀ R, IsPsh A (α + LocPot.ofFun (w R))) →
    (∀ R x, x ∉ boundary σ →
        -(K * (1 + ∑ i, Real.log (rFun (Λ i) (σ i) x))) ≤ w R x ∧ w R x ≤ 0) →
    ∀ (k : Fin r) (Ck : FinHolAtlas n (W k)), HoloMap Ck B Subtype.val →
    GlobalTheory.SNCComp.IsSNCAtlas B μ (Fin.cons L Λ) (Fin.cons s σ) W e k Ck →
    1 ≤ e 0 k → (∀ i : Fin m, e i.succ k = 0) →
    ∃ C : ℝ, ∀ (R : ℕ) (T : Fin n → LocPot Y),
      (∀ i, T i = (α + LocPot.ofFun (w R)).pullback μ hμ.1 ∨ T i = α.pullback μ hμ.1) →
        -C ≤ mInt Ck (fun i => (T i).pullback Subtype.val continuous_subtype_val) (fun y => w R (μ y.1)) := by
  intro d X _ _ _ A m α Λ σ c hS L s _ _ _ n Y _ _ _ B hB μ hμ r W e hJ w K hw hwp hwb k Ck hCk hA _ he
  obtain ⟨hα, hαp, hσ, -⟩ := hS
  have hcl : IsClosed (W k) := by
    refine SimpleNormalCrossingSliceCharts.isClosed_divisorComponent B (L.pullback μ hμ.1) (fun y z => s (μ y) (μ z)) (e 0) W (fun y => ?_) k
    obtain ⟨χ, h1, h2, κ, h3, h4, h5⟩ := hJ y
    obtain ⟨h6, u, h7, h8, h9⟩ := h5 0
    exact ⟨χ, h1, h2, h6, κ, h3, h4, u, h7, h8, h9⟩
  haveI : CompactSpace (W k) := isCompact_iff_compactSpace.mp hcl.isCompact
  obtain ⟨OmY, hOY, hOYpos⟩ := GlobalTheory.T.projective_atlas_positive_potential (n + 1) Y B hB
  set Om := OmY.pullback (Subtype.val : W k → Y) continuous_subtype_val with hOm
  have hO : IsPotential Ck Om := isPotentialPullback B Ck _ hCk OmY hOY
  have hOpos : IsPosPot Ck Om := isPosPot_restrict B μ _ _ W e k Ck hCk hA OmY hOY hOYpos
  have hOp := TailBoundAlt.isPsh_of_isPosPot Ck Om hOpos
  set ν : W k → X := μ ∘ Subtype.val with hνdef
  have hν : HoloMap Ck A ν := GlobalTheory.SNCRankDrop.holoMap_comp hμ hCk
  have hint : ∀ i, interior {y | σ i (ν y) (ν y) = 0} = ∅ := fun i =>
    interior_zero_eq_empty A B μ _ _ W e k Ck hA i.succ (hσ i).2.1 (he i)
  have hBd := GlobalTheory.isBd_pullback_boundary d X A m Λ σ (fun i => ⟨(hσ i).1, (hσ i).2.1, (hσ i).2.2.2⟩) n (W k) Ck ν hν
    hint Om hO hOpos
  set Z := ν ⁻¹' boundary σ with hZ
  set ρ : W k → ℝ := fun y => Real.exp 1 - 2 * ∑ i, logNormSec (Λ i) (σ i) (ν y) with hρ
  have hα' := isPotentialPullback A Ck ν hν α hα
  have hαp' := GlobalTheory.PshPull.isPsh_pullback d X A n (W k) Ck ν hν α hα (TailBoundAlt.isPsh_of_isPosPot A α hαp)
  obtain ⟨K₂, hK₂, ha1, ha2⟩ := TailBoundAlt.exists_psh_chern_bound Ck Om _ hO hOpos hα'
  have hKm : 0 ≤ max K 0 * (1 + (m : ℝ)) := by positivity
  set K' := K₂ + max K 0 * (1 + (m : ℝ)) with hK'
  have hK'0 : 0 ≤ K' := by positivity
  have hρe := hBd.2.2.2.2.2.1
  obtain ⟨C, hC⟩ := GlobalTheory.Mean4O.LogTail.tail n (W k) Ck Z ρ Om hBd K'
  have ha1' := psh_mono Ck hO hOp hα' ha1 (C' := K') (by linarith)
  have ha2' := psh_mono Ck hO hOp (isPotentialRsmul Ck _ _ hα') ha2 (C' := K') (by linarith)
  refine ⟨K' * (C * Real.log (Real.exp 1) ^ (n + 1) / Real.exp 1), fun R T hT => ?_⟩
  have hg := smooth_comp_holo A Ck ν hν _ (hw R)
  have hgc := continuous_of_smooth Ck hg
  have hgb : ∀ y, y ∉ Z → -(K' * Real.log (ρ y)) ≤ w R (ν y) ∧ w R (ν y) ≤ 0 := fun y hy => by
    obtain ⟨h1, h2⟩ := hwb R (ν y) hy
    refine ⟨le_trans ?_ h1, h2⟩
    obtain ⟨h3, h4⟩ := sum_log_le (fun i => logNormSec (Λ i) (σ i) (ν y))
      fun i => logNormSec_nonpos ((hσ i).2.2.2 _)
    have h5 : 0 ≤ Real.log (ρ y) := Real.log_nonneg ((Real.one_le_exp zero_le_one).trans (hρe y hy))
    have h6 := mul_le_mul (le_max_left K 0) h4 h3 (le_max_right K 0)
    have h7 := mul_nonneg hK₂ h5
    have h8 : K' * Real.log (ρ y) =
        K₂ * Real.log (ρ y) + max K 0 * ((1 + (m : ℝ)) * Real.log (ρ y)) := by rw [hK']; ring
    rw [h8]
    exact neg_le_neg (h6.trans (le_add_of_nonneg_left h7))
  have hwR := isPotentialAdd A _ _ hα (isPotential_ofFun A _ (hw R))
  have hTall : ∀ i, IsPotential Ck ((T i).pullback Subtype.val continuous_subtype_val) ∧
      IsPsh Ck ((T i).pullback Subtype.val continuous_subtype_val) ∧
      ListForm Ck Z ρ Om K' ((T i).pullback Subtype.val continuous_subtype_val) := fun i => by
    rcases hT i with h | h <;> rw [h]
    · have hp := GlobalTheory.PshPull.isPsh_pullback d X A n (W k) Ck ν hν _ hwR (hwp R)
      refine ⟨isPotentialPullback A Ck ν hν _ hwR, hp, ?_⟩
      rw [pullback_add_ofFun] at hp
      exact listForm_add Ck hα' ha1' ha2' hg hgb hp
    · exact ⟨hα', hαp', listForm_self Ck hK'0 hρe hα' ha1' ha2' hαp'⟩
  exact mInt_lower_of_tail Ck hBd hK'0 hC _ (fun i => (hTall i).1) (fun i => (hTall i).2.1)
    (fun i => (hTall i).2.2) hgc fun y hy => (hgb y hy).1

end GlobalTheory.SNCCompBound
