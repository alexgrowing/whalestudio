import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemBand
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarishChandraExistsReproducingTestFunctionGLStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormLeSupWiderBandGenCentralEigenformsStatement
import GroundTheory.AutomorphicForms.AdelicGLn

noncomputable section

open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.HCF Topology Pointwise

namespace GlobalTheory.HCF.Equi

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

theorem continuous_infGL' : Continuous (infGL E a) := by
  refine Continuous.units_map _ ?_
  have hs : Continuous (sInf E : Cinf E → Ad E) := (continuous_infEq E).prodMk continuous_const
  exact continuous_const.sub continuous_const |>.add (continuous_id.matrix_map hs)

theorem continuous_pInf' : Continuous (pInf E) :=
  continuous_pi fun w =>
    ((InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).continuous.comp
      (continuous_apply w)).comp continuous_fst

theorem continuous_mapInf : Continuous (Matrix.GeneralLinearGroup.map (n := Fin a) (pInf E)) :=
  Continuous.units_map _ (continuous_id.matrix_map continuous_pInf')

omit [IsTotallyComplex E] in
theorem continuous_mapFin : Continuous (Matrix.GeneralLinearGroup.map (n := Fin a) (pFin E)) :=
  Continuous.units_map _ (continuous_id.matrix_map (continuous_snd : Continuous (pFin E)))

omit [IsTotallyComplex E] in

theorem absDetA_eq (g : GA E a) :
    absDetA g = (GroundTheory.Global.IdeleGroup.ideleModule E (Matrix.GeneralLinearGroup.det g) : ℝ) := by
  unfold absDetA
  exact GroundTheory.Automorphic.Reduction.adeleAbs_units (K := E) _

omit [IsTotallyComplex E] in

theorem absDetA_mul (g h : GA E a) : absDetA (g * h) = absDetA g * absDetA h := by
  rw [absDetA_eq, absDetA_eq, absDetA_eq, map_mul, map_mul, Positive.val_mul]

omit [IsTotallyComplex E] in

theorem continuous_absDetA : Continuous (absDetA (E := E) (a := a)) := by
  have e : (absDetA (E := E) (a := a)) =
      fun g => (GroundTheory.Global.IdeleGroup.ideleModule E (GroundTheory.Automorphic.AdelicGLn.det E a g) : ℝ) :=
    funext absDetA_eq
  rw [e]
  exact continuous_subtype_val.comp (GroundTheory.Global.IdeleGroup.continuous_ideleModule.comp
    (GroundTheory.Automorphic.AdelicGLn.continuous_det E a))

theorem continuous_along (ψ : Sm E a) (g : GA E a) : Continuous fun z : GL (Fin a) (Cinf E) => ψ.1 (g * infGL E a z) := by
  have h := (ψ.2 g).continuousOn
  have h2 : Continuous fun z : GL (Fin a) (Cinf E) => chart ψ.1 g (toL z.val) :=
    h.comp_continuous (Units.continuous_val (M := Matrix (Fin a) (Fin a) (Cinf E)) : _) fun z => val_mem_invSet z
  exact h2.congr fun z => chart_val ψ.1 g z

theorem equicontinuous_band : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ)
    (L : Subgroup (GL (Fin a) (Af E))), IsOpen (L : Set (GL (Fin a) (Af E))) → ∀ W : Submodule ℂ (Kinf E a → ℂ),
    FiniteDimensional ℂ W → ∀ X : Set (Module.End ℂ (Sm E a) → ℂ), X.Finite → ∀ N : ℕ, ∀ ε : ℝ, 0 < ε →
    ∃ U ∈ 𝓝 (1 : GA E a), ∀ φ ∈ Submodule.span ℂ (formsGL E a L W X N), ∀ M : ℝ, (∀ h ∈ band E a, ‖φ.1 h‖ ≤ M) →
      ∀ g ∈ band E a, ∀ u ∈ U, g * u ∈ band E a → ‖φ.1 (g * u) - φ.1 g‖ ≤ ε * M := by
  intro E _ _ _ a L hL W hW X hX N ε hε
  letI : MeasurableSpace (GL (Fin a) (Cinf E)) := borel _
  haveI : BorelSpace (GL (Fin a) (Cinf E)) := ⟨rfl⟩
  haveI : LocallyCompactSpace (GL (Fin a) (Cinf E)) := Units.isClosedEmbedding_embedProduct.locallyCompactSpace
  set μ : Measure (GL (Fin a) (Cinf E)) := Measure.haar
  obtain ⟨α, hαc, hαs, hα⟩ := GlobalTheory.T.harishChandra_exists_reproducing_testFunction_GL E a L hL W hW X hX N μ inferInstance
  have hint : ∀ (ψ : Sm E a) (g : GA E a), Integrable (fun y => ψ.1 (g * infGL E a y) * α y) μ := fun ψ g =>
    ((continuous_along ψ g).mul hαc).integrable_of_hasCompactSupport hαs.mul_left

  have hrep : ∀ φ ∈ Submodule.span ℂ (formsGL E a L W X N), ∀ g,
      ∫ y, φ.1 (g * infGL E a y) * α y ∂μ = φ.1 g := by
    intro φ hφ
    induction hφ using Submodule.span_induction with
    | mem x hx => exact hα x hx
    | zero => intro g; change ∫ z, (0 : ℂ) * α z ∂μ = 0; simp
    | add x y _ _ hx hy =>
      intro g
      change ∫ z, (x.1 (g * infGL E a z) + y.1 (g * infGL E a z)) * α z ∂μ = x.1 g + y.1 g
      simp_rw [add_mul]
      rw [integral_add (hint x g) (hint y g), hx, hy]
    | smul c x _ hx =>
      intro g
      change ∫ z, (c * x.1 (g * infGL E a z)) * α z ∂μ = c * x.1 g
      simp_rw [mul_assoc]
      rw [integral_const_mul, hx]

  have hfix : ∀ φ ∈ Submodule.span ℂ (formsGL E a L W X N), ∀ k ∈ L, ∀ x, φ.1 (x * finGL E a k) = φ.1 x := by
    intro φ hφ k hk x
    induction hφ using Submodule.span_induction with
    | mem ψ hψ => exact congrArg (fun f : Sm E a => f.1 x) (hψ.2.1 k hk)
    | zero => rfl
    | add ψ χ _ _ h1 h2 =>
      change ψ.1 (x * finGL E a k) + χ.1 (x * finGL E a k) = ψ.1 x + χ.1 x
      rw [h1, h2]
    | smul c ψ _ h =>
      change c * ψ.1 (x * finGL E a k) = c * ψ.1 x
      rw [h]

  obtain ⟨V, hVc, hV1⟩ := exists_compact_mem_nhds (1 : GL (Fin a) (Cinf E))
  have hKc : IsCompact (tsupport α) := hαs
  set K' := V * tsupport α with hK'
  have hK'c : IsCompact K' := hVc.mul hKc
  have hK'm : MeasurableSet K' := hK'c.measurableSet

  have hfc : Continuous fun z : GL (Fin a) (Cinf E) => absDetA (infGL E a z) :=
    continuous_absDetA.comp continuous_infGL'
  obtain ⟨B₁, hB₁⟩ := hK'c.exists_bound_of_continuousOn hfc.continuousOn
  obtain ⟨B₂, hB₂⟩ := hK'c.exists_bound_of_continuousOn
    (hfc.inv₀ fun z => (absDetA_pos _).ne').continuousOn
  set c := max 1 (max B₁ B₂) with hc
  have hc1 : 1 ≤ c := le_max_left _ _
  have hcK : ∀ z ∈ K', c⁻¹ ≤ absDetA (infGL E a z) ∧ absDetA (infGL E a z) ≤ c := by
    intro z hz
    have hp := absDetA_pos (infGL E a z)
    have h1 := hB₁ z hz
    have h2 : ‖(absDetA (infGL E a z))⁻¹‖ ≤ B₂ := hB₂ z hz
    rw [Real.norm_of_nonneg hp.le] at h1
    rw [Real.norm_of_nonneg (inv_nonneg.2 hp.le)] at h2
    refine ⟨?_, h1.trans ((le_max_left _ _).trans (le_max_right _ _))⟩
    rw [inv_le_comm₀ (by positivity) hp]
    exact h2.trans ((le_max_right _ _).trans (le_max_right _ _))
  obtain ⟨C, hC⟩ := GlobalTheory.T.norm_le_sup_wider_band_genCentralEigenforms E a L hL W hW X hX N c hc1
  set C' := |C| + 1 with hC'
  have hC'0 : 0 < C' := by positivity
  set m := μ.real K' with hm
  have hm0 : 0 ≤ m := measureReal_nonneg
  set δ := ε / (C' * (m + 1)) with hδ
  have hδ0 : 0 < δ := by positivity
  have hδe : C' * δ * (m + 1) = ε := by rw [hδ]; field_simp

  obtain ⟨v, hv, hvK⟩ := hK'c.mem_uniformity_of_prod (f := fun p x => α (p⁻¹ * x)) (s := Set.univ) (q := 1)
    (by exact (hαc.comp (continuous_fst.inv.mul continuous_snd)).continuousOn) (Set.mem_univ _)
    (Metric.dist_mem_uniformity hδ0)
  rw [nhdsWithin_univ] at hv

  refine ⟨{u | Matrix.GeneralLinearGroup.map (pInf E) u ∈ v ∩ V ∧ Matrix.GeneralLinearGroup.map (pFin E) u ∈ L}, ?_, ?_⟩
  · refine Filter.inter_mem ?_ ?_
    · exact continuous_mapInf.continuousAt.preimage_mem_nhds (by rw [map_one]; exact Filter.inter_mem hv hV1)
    · exact continuous_mapFin.continuousAt.preimage_mem_nhds (by rw [map_one]; exact hL.mem_nhds L.one_mem)
  intro φ hφ M hM g hg u hu _
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 1 one_mem_band)
  set y := Matrix.GeneralLinearGroup.map (pInf E) u with hy
  set k := Matrix.GeneralLinearGroup.map (pFin E) u with hk
  have hyv : y ∈ v := hu.1.1
  have hyV : y ∈ V := hu.1.2
  have hkL : k ∈ L := hu.2
  have hgu : φ.1 (g * u) = φ.1 (g * infGL E a y) := by
    rw [← infGL_mul_finGL u, ← mul_assoc, hfix φ hφ k hkL]
  rw [hgu]

  have e1 : φ.1 (g * infGL E a y) = ∫ z, φ.1 (g * infGL E a z) * α (y⁻¹ * z) ∂μ := by
    rw [← hrep φ hφ (g * infGL E a y),
      ← integral_mul_left_eq_self (fun z => φ.1 (g * infGL E a z) * α (y⁻¹ * z)) y]
    congr 1
    funext x
    simp only [map_mul, mul_assoc, inv_mul_cancel_left]
  have hi1 : Integrable (fun z => φ.1 (g * infGL E a z) * α (y⁻¹ * z)) μ :=
    ((continuous_along φ g).mul (hαc.comp (continuous_const.mul continuous_id))).integrable_of_hasCompactSupport
      (HasCompactSupport.mul_left (hαs.comp_homeomorph (Homeomorph.mulLeft y⁻¹)))
  have e2 : φ.1 (g * infGL E a y) - φ.1 g = ∫ z, φ.1 (g * infGL E a z) * (α (y⁻¹ * z) - α z) ∂μ := by
    rw [e1, ← hrep φ hφ g, ← integral_sub hi1 (hint φ g)]
    simp_rw [mul_sub]
  rw [e2]

  have hpt : ∀ z, ‖φ.1 (g * infGL E a z) * (α (y⁻¹ * z) - α z)‖ ≤ K'.indicator (fun _ => C' * M * δ) z := by
    intro z
    by_cases hz : z ∈ K'
    · rw [Set.indicator_of_mem hz, norm_mul]
      have hd := hcK z hz
      have hg' := hg
      obtain ⟨hg1, hg2⟩ := hg'
      have hb1 : c⁻¹ ≤ absDetA (g * infGL E a z) := by
        rw [absDetA_mul]
        have := absDetA_pos (infGL E a z)
        nlinarith
      have hb2 : absDetA (g * infGL E a z) ≤ 2 * c := by
        rw [absDetA_mul]
        have := absDetA_pos (infGL E a z)
        nlinarith
      have h1 : ‖φ.1 (g * infGL E a z)‖ ≤ C' * M :=
        (hC φ hφ M hM _ hb1 hb2).trans (mul_le_mul_of_nonneg_right (by rw [hC']; linarith [le_abs_self C]) hM0)
      have h2 : ‖α (y⁻¹ * z) - α z‖ ≤ δ := by
        have := hvK y hyv z hz
        simp only [inv_one, one_mul, Set.mem_setOf_eq] at this
        rw [← dist_eq_norm]; exact this.le
      exact mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
    · rw [Set.indicator_of_notMem hz]
      have hz1 : α z = 0 := image_eq_zero_of_notMem_tsupport fun h => hz ⟨1, mem_of_mem_nhds hV1, z, h, one_mul z⟩
      have hz2 : α (y⁻¹ * z) = 0 := image_eq_zero_of_notMem_tsupport fun h =>
        hz ⟨y, hyV, y⁻¹ * z, h, mul_inv_cancel_left y z⟩
      simp [hz1, hz2]
  have hint' : Integrable (K'.indicator (fun _ => C' * M * δ)) μ :=
    (integrableOn_const (C := C' * M * δ) hK'c.measure_lt_top.ne).integrable_indicator hK'm
  refine (norm_integral_le_of_norm_le hint' (Filter.Eventually.of_forall hpt)).trans ?_
  rw [integral_indicator_const _ hK'm, smul_eq_mul, ← hm]
  have : 0 ≤ C' * M * δ := by positivity
  calc m * (C' * M * δ) ≤ (m + 1) * (C' * M * δ) := by nlinarith
    _ = ε * M := by rw [← hδe]; ring

end GlobalTheory.HCF.Equi
