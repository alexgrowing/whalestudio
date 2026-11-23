import Mathlib
import GroundTheory.AutomorphicForms.HarishChandraRegularity.CartanBasis

namespace GroundTheory.Automorphic

open MeasureTheory Set Filter Topology NormedSpace
open scoped NNReal ENNReal

set_option linter.unusedSectionVars false

section Conj

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

def conjCME (k : G) : G ≃ₜ* G :=
  { MulAut.conj k with
    continuous_toFun := (continuous_const.mul continuous_id).mul continuous_const
    continuous_invFun := (continuous_const.mul continuous_id).mul continuous_const }

@[simp] theorem conjCME_apply (k x : G) : conjCME k x = k * x * k⁻¹ := rfl

theorem conjCME_mul (a b : G) : conjCME (a * b) = (conjCME b).trans (conjCME a) := by
  ext x
  simp [mul_assoc]

theorem conjCME_one : conjCME (1 : G) = ContinuousMulEquiv.refl G := by
  ext x
  simp

variable [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]

theorem mulEquivHaarChar_conjCME_mul (a b : G) :
    mulEquivHaarChar (conjCME (a * b)) =
      mulEquivHaarChar (conjCME a) * mulEquivHaarChar (conjCME b) := by
  rw [conjCME_mul, mulEquivHaarChar_trans, mul_comm]

theorem mulEquivHaarChar_conjCME_pow (a : G) (n : ℕ) :
    mulEquivHaarChar (conjCME (a ^ n)) = mulEquivHaarChar (conjCME a) ^ n := by
  induction n with
  | zero => simp [conjCME_one]
  | succ n ih => rw [pow_succ, mulEquivHaarChar_conjCME_mul, ih, pow_succ]

theorem mulEquivHaarChar_conjCME_inv (a : G) :
    mulEquivHaarChar (conjCME a⁻¹) * mulEquivHaarChar (conjCME a) = 1 := by
  rw [← mulEquivHaarChar_conjCME_mul, inv_mul_cancel, conjCME_one, mulEquivHaarChar_refl]

theorem exists_bound_mulEquivHaarChar_conjCME {K : Set G} (hK : IsCompact K)
    (hKinv : ∀ k ∈ K, k⁻¹ ∈ K) :
    ∃ B : ℝ≥0, ∀ k ∈ K, mulEquivHaarChar (conjCME k) ≤ B := by
  obtain ⟨V, hVc, hV1⟩ := exists_compact_mem_nhds (1 : G)
  set μ : Measure G := Measure.haar
  set C : Set G := (fun p : G × G × G => p.1 * p.2.1 * p.2.2) '' (K ×ˢ V ×ˢ K)
  have hC : IsCompact C := (hK.prod (hVc.prod hK)).image (by fun_prop)
  have hV0 : μ V ≠ 0 := (μ.measure_pos_of_mem_nhds hV1).ne'
  have hCt : μ C ≠ ∞ := hC.measure_lt_top.ne
  refine ⟨(μ C / μ V).toNNReal, fun k hk => ?_⟩
  have hsub : V ⊆ conjCME k ⁻¹' C := fun x hx =>
    ⟨(k, x, k⁻¹), ⟨hk, hx, hKinv k hk⟩, rfl⟩
  have e := mulEquivHaarChar_smul_preimage μ (X := C) (conjCME k)
  have hle : (mulEquivHaarChar (conjCME k) : ℝ≥0∞) * μ V ≤ μ C := by
    rw [← e, ENNReal.smul_def, smul_eq_mul]
    gcongr
  have : (mulEquivHaarChar (conjCME k) : ℝ≥0∞) ≤ μ C / μ V :=
    (ENNReal.le_div_iff_mul_le (Or.inl hV0) (Or.inr hCt)).2 hle
  rw [← ENNReal.coe_le_coe, ENNReal.coe_toNNReal (ENNReal.div_ne_top hCt hV0)]
  exact this

theorem mulEquivHaarChar_conjCME_eq_one {K : Subgroup G} (hK : IsCompact (K : Set G)) {k : G}
    (hk : k ∈ K) : mulEquivHaarChar (conjCME k) = 1 := by
  obtain ⟨B, hB⟩ := exists_bound_mulEquivHaarChar_conjCME hK fun k hk => K.inv_mem hk
  have hle : ∀ a ∈ K, mulEquivHaarChar (conjCME a) ≤ 1 := by
    intro a ha
    by_contra hlt
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt B (not_le.1 hlt)
    have := hB (a ^ n) (K.pow_mem ha n)
    rw [mulEquivHaarChar_conjCME_pow] at this
    exact absurd this (not_le.2 hn)
  have h1 := hle k hk
  have h2 := hle k⁻¹ (K.inv_mem hk)
  have h3 := mulEquivHaarChar_conjCME_inv k
  refine le_antisymm h1 ?_
  by_contra hlt
  have hlt' := not_le.1 hlt
  have : mulEquivHaarChar (conjCME k⁻¹) * mulEquivHaarChar (conjCME k) < 1 :=
    calc mulEquivHaarChar (conjCME k⁻¹) * mulEquivHaarChar (conjCME k)
        ≤ 1 * mulEquivHaarChar (conjCME k) := by gcongr
      _ < 1 := by rwa [one_mul]
  rw [h3] at this
  exact lt_irrefl _ this

theorem map_conj_eq_self_of_mem (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular] {K : Subgroup G}
    (hK : IsCompact (K : Set G)) {k : G} (hk : k ∈ K) : μ.map (conjCME k) = μ := by
  have e := mulEquivHaarChar_smul_map μ (conjCME k)
  rwa [mulEquivHaarChar_conjCME_eq_one hK hk, one_smul] at e

theorem integral_conj_eq_self_of_mem (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]
    {K : Subgroup G} (hK : IsCompact (K : Set G)) {k : G} (hk : k ∈ K) {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (F : G → E) :
    ∫ y, F (k * y * k⁻¹) ∂μ = ∫ y, F y ∂μ := by
  have e := integral_map_equiv (conjCME k).toHomeomorph.toMeasurableEquiv (μ := μ) F
  conv_rhs => rw [← map_conj_eq_self_of_mem μ hK hk]
  exact e.symm

end Conj

section Closed

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
  {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸}

theorem IsExpLieAlgebra.isClosed (h : IsExpLieAlgebra G 𝔤) : IsClosed (G : Set 𝔸ˣ) := by
  set W : Set 𝔸ˣ := (fun u : 𝔸ˣ => (u : 𝔸)) ⁻¹' h.nhdOne with hW
  have hWo : IsOpen W := h.isOpen_nhdOne.preimage Units.continuous_val
  refine isClosed_of_closure_subset fun x hx => ?_
  have hN : {z : 𝔸ˣ | z⁻¹ * x ∈ W} ∈ 𝓝 x := by
    refine (hWo.preimage (continuous_inv.mul continuous_const)).mem_nhds ?_
    show (((x⁻¹ * x : 𝔸ˣ)) : 𝔸) ∈ h.nhdOne
    simpa using h.one_mem_nhdOne
  obtain ⟨g₀, hg₀N, hg₀G⟩ := mem_closure_iff_nhds.1 hx _ hN
  set y := g₀⁻¹ * x with hy
  have hyW : y ∈ W := hg₀N
  have hyc : y ∈ closure (G : Set 𝔸ˣ) :=
    map_mem_closure (continuous_const.mul continuous_id) hx fun z hz =>
      G.mul_mem (G.inv_mem hg₀G) hz
  have hyc' : y ∈ closure (W ∩ (G : Set 𝔸ˣ)) := hWo.inter_closure ⟨hyW, hyc⟩
  set L : 𝔸ˣ → 𝔸 := fun u => (expPartialHomeomorph ℝ 𝔸).symm (u : 𝔸) with hLdef
  have hL : ContinuousAt L y :=
    ((expPartialHomeomorph ℝ 𝔸).continuousAt_symm (h.nhdOne_subset_target hyW)).comp
      Units.continuous_val.continuousAt
  have himg : L '' (W ∩ (G : Set 𝔸ˣ)) ⊆ (𝔤 : Set 𝔸) := by
    rintro _ ⟨u, ⟨huW, huG⟩, rfl⟩
    apply h.mem_of_mem_nhd (h.symm_mem_nhd huW)
    have : expUnit ℝ 𝔸 (L u) = u := Units.ext (h.exp_symm huW)
    rw [this]
    exact huG
  have hLy : L y ∈ 𝔤 :=
    (Submodule.closed_of_finiteDimensional 𝔤).closure_subset_iff.2 himg (mem_closure_image hL hyc')
  have hyG : y ∈ G := by
    have : expUnit ℝ 𝔸 (L y) = y := Units.ext (h.exp_symm hyW)
    rw [← this]
    exact h.expUnit_mem _ hLy
  have : x = g₀ * y := by rw [hy, mul_inv_cancel_left]
  rw [this]
  exact G.mul_mem hg₀G hyG

end Closed

section MaxCompact

open Matrix
open scoped Matrix.Norms.L2Operator

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem isCompact_unitaryGroup_entries : IsCompact (Matrix.unitaryGroup ι 𝕜 : Set (Matrix ι ι 𝕜)) := by
  have hT : IsCompact (Set.pi univ fun _ : ι => Set.pi univ fun _ : ι => Metric.closedBall (0 : 𝕜) 1) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall 0 1
  refine hT.of_isClosed_subset ?_ ?_
  · have : (Matrix.unitaryGroup ι 𝕜 : Set (Matrix ι ι 𝕜)) = {a | aᴴ * a = 1} := by
      ext a
      simp [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
    rw [this]
    exact isClosed_eq (continuous_id.matrix_conjTranspose.matrix_mul continuous_id) continuous_const
  · intro a ha i _ j _
    simpa using entry_norm_bound_of_unitary ha i j

theorem isCompact_maxCompact_of_isClosed {G : Subgroup (Matrix ι ι 𝕜)ˣ}
    (hG : IsClosed (G : Set (Matrix ι ι 𝕜)ˣ)) :
    IsCompact ((maxCompact G : Subgroup G) : Set G) := by
  set e : G → Matrix ι ι 𝕜 := fun x => ((x : (Matrix ι ι 𝕜)ˣ) : Matrix ι ι 𝕜) with he
  have hemb : Topology.IsEmbedding e :=
    Units.isOpenEmbedding_val.isEmbedding.comp Topology.IsEmbedding.subtypeVal
  rw [hemb.isCompact_iff]
  set S := (Matrix.unitaryGroup ι 𝕜 : Set (Matrix ι ι 𝕜))
  have himg : e '' (maxCompact G : Set G) = S ∩ range e := by
    ext a
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact ⟨hg, g, rfl⟩
    · rintro ⟨ha, g, rfl⟩
      exact ⟨g, ha, rfl⟩
  rw [himg]
  refine isCompact_unitaryGroup_entries.of_isClosed_subset ?_ inter_subset_left
  refine isClosed_of_closure_subset fun a ha => ?_
  have haS : a ∈ S :=
    (closure_mono inter_subset_left |>.trans isCompact_unitaryGroup_entries.isClosed.closure_subset) ha
  set u : (Matrix ι ι 𝕜)ˣ :=
    ⟨a, star a, Matrix.mem_unitaryGroup_iff.1 haS, Matrix.mem_unitaryGroup_iff'.1 haS⟩
  have hu : u ∈ closure (G : Set (Matrix ι ι 𝕜)ˣ) := by
    rw [Units.isOpenEmbedding_val.isInducing.closure_eq_preimage_closure_image]
    refine closure_mono ?_ ha
    rintro _ ⟨-, g, rfl⟩
    exact ⟨g, g.2, rfl⟩
  have huG : u ∈ G := hG.closure_subset hu
  exact ⟨haS, ⟨u, huG⟩, rfl⟩

theorem IsExpLieAlgebra.isCompact_maxCompact_real {G : Subgroup (Matrix ι ι ℝ)ˣ}
    {𝔤 : Submodule ℝ (Matrix ι ι ℝ)} (h : IsExpLieAlgebra G 𝔤) :
    IsCompact ((maxCompact G : Subgroup G) : Set G) :=
  isCompact_maxCompact_of_isClosed h.isClosed

theorem IsExpLieAlgebra.isCompact_maxCompact_complex {G : Subgroup (Matrix ι ι ℂ)ˣ}
    {𝔤 : Submodule ℝ (Matrix ι ι ℂ)} (h : IsExpLieAlgebra G 𝔤) :
    IsCompact ((maxCompact G : Subgroup G) : Set G) :=
  isCompact_maxCompact_of_isClosed h.isClosed

end MaxCompact

end GroundTheory.Automorphic
