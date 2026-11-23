import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.UnitaryLattices.LatticeIndexLifts.MeasurableSpaceThirdLift

noncomputable section

open Matrix MeasureTheory GlobalTheory.SplitWeil GlobalTheory.BZMir Filter
open scoped Topology ENNReal NNReal

namespace PositivityTheory.RgUd.Form.U.Lift2

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

section Main

local instance measurableSpaceFourthLift : MeasurableSpace k := borel k
local instance borelSpaceOnK : BorelSpace k := ⟨rfl⟩
local instance instSCK4 : SecondCountableTopology k := GlobalTheory.SplitWeil.secondCountable k

variable {ψ : AddChar k Circle} (hψ : Continuous ψ) (hψ1 : ψ ≠ 1) {m : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
  {col : (Fin (m + 1) → k) → V →ₗ[ℂ] V} {gl : GL (Fin (m + 1)) k →* (V →ₗ[ℂ] V)} (hS : Setup col gl) {s : ℝ}
  {B B' C : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ} {A₀ : AddSubgroup (Fin (m + 1) → k)} (hA₀ : Lat A₀)
  (hBp : Psd B) (hBc : ∀ x v w, B (col x v) (col x w) = B v w)
  (hBg : ∀ g v w, B (gl g v) (gl g w) = ((md g ^ s : ℝ) : ℂ) * B v w)
  (hD : IsD ψ col A₀ B B') (hCp : Psd C) (hCc : ∀ x v w, C (col x v) w = ((ψ (xz m ⬝ᵥ x) : Circle) : ℂ) * C v w)
  (hC : ∀ p ∈ Mir k m, ∀ v w, C (gl p v) (gl p w) = ((md p ^ (s + 1) : ℝ) : ℂ) * C v w)
  (hCB : ∀ v, (C v v).re ≤ (B' v v).re)
  {ν : Measure (Fin (m + 1) → k)} [ν.IsAddHaarMeasure] (hν : ν (perp ψ A₀) = 1)

private theorem addHaar_singleton_zero_eq_zero {m : ℕ} {ψ : AddChar k Circle} (hψ : Continuous ψ) (hψ1 : ψ ≠ 1)
    (ν : Measure (Fin (m + 1) → k)) [ν.IsAddHaarMeasure] : ν {0} = 0 := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (ValuativeRel.valuation k).integer
  have hϖ0 : (ϖ : k) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)
  set x : kˣ := Units.mk0 (ϖ : k) hϖ0 with hxdef
  have hx : nabs k x < 1 := by
    rw [nabs_uniformiser hϖ rfl]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast one_lt_resCard k)
  have hx0 : 0 < nabs k x := nabs_pos k x
  let g : GL (Fin (m + 1)) k :=
    Matrix.GeneralLinearGroup.mkOfDetNeZero (((x⁻¹ : kˣ) : k) • (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) k))
      (by simp [Matrix.det_smul])
  have hdet : Matrix.GeneralLinearGroup.det g = x⁻¹ ^ (m + 1) := by
    ext
    simp [g, Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_smul]
  have hg : md g = (nabs k x)⁻¹ ^ (m + 1) := by
    show nabs k (Matrix.GeneralLinearGroup.det g) = _
    rw [hdet]
    simp [nabs, map_pow, map_inv]
  have hg1 : 1 < md g := by
    rw [hg]
    exact one_lt_pow₀ (one_lt_inv₀ hx0 |>.2 hx) (Nat.succ_ne_zero m)
  obtain ⟨A, hA, -⟩ := lat_over (isCompact_empty (X := Fin (m + 1) → k))
  have hpow : ∀ j : ℕ, md (g ^ j) = md g ^ j := by
    intro j
    induction j with
    | zero => simp [md_one]
    | succ j ih => rw [pow_succ, md_mul, ih, pow_succ]
  have hbound : ∀ j : ℕ, (ν {0}).toReal ≤ ((md g)⁻¹) ^ j * (ν (perp ψ A)).toReal := by
    intro j
    have h0 : ({0} : Set (Fin (m + 1) → k)) ⊆ (perp ψ (gmap (g ^ j) A) : Set _) := by
      simp [(perp ψ (gmap (g ^ j) A)).zero_mem]
    calc (ν {0}).toReal ≤ (ν (perp ψ (gmap (g ^ j) A))).toReal :=
          ENNReal.toReal_mono (meas_perp_lt_top ψ ν hψ hψ1 (lat_gmap _ _ hA)).ne (measure_mono h0)
      _ = _ := by rw [meas_perp_gmap ψ ν hψ hψ1 _ hA, hpow, inv_pow]
  have hlim : Tendsto (fun j : ℕ => ((md g)⁻¹) ^ j * (ν (perp ψ A)).toReal) atTop (𝓝 0) := by
    have := tendsto_pow_atTop_nhds_zero_of_lt_one (inv_nonneg.2 (md_pos g).le) (inv_lt_one_of_one_lt₀ hg1)
    simpa using this.mul_const (ν (perp ψ A)).toReal
  have hle : (ν {0}).toReal ≤ 0 := ge_of_tendsto' hlim hbound
  have hfin : ν {0} ≠ ⊤ := by
    refine ne_top_of_le_ne_top (meas_perp_lt_top ψ ν hψ hψ1 hA).ne (measure_mono ?_)
    simp [(perp ψ A).zero_mem]
  have := le_antisymm hle ENNReal.toReal_nonneg
  rcases (ENNReal.toReal_eq_zero_iff _).1 this with h | h
  · exact h
  · exact absurd h hfin

include hψ hψ1 hS hA₀ hBp hBc hBg hD hCp hCc hC hCB hν in

theorem lift_form : ∃ I : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ, Psd I ∧ (∀ x v w, I (col x v) (col x w) = I v w) ∧
      (∀ g v w, I (gl g v) (gl g w) = ((nabs k (Matrix.GeneralLinearGroup.det g) ^ s : ℝ) : ℂ) * I v w) ∧
      (∀ v, (I v v).re ≤ (B v v).re) ∧ IsD ψ col A₀ I C ∧ IsA col I 0 ∧
      ∀ Y : Submodule ℂ V, (∀ g, ∀ y ∈ Y, gl g y ∈ Y) → (∀ y ∈ Y, ∀ w, C y w = 0) → ∀ y ∈ Y, ∀ w, I y w = 0 := by
  have hC' : ∀ p ∈ Mir k m, ∀ v w, C (gl p v) (gl p w) = ((md p ^ (s + 1) : ℝ) : ℂ) * C v w := hC
  have hint : ∀ v w, Integrable (fun ξ => Df gl s C ξ v w) ν :=
    integrable_Df hψ hψ1 hS hA₀ hBp hBc hBg hD hCp hC' hCB hν
  let I : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ := LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ)
    (fun v w => ∫ ξ, Df gl s C ξ v w ∂ν)
    (fun v₁ v₂ w => by
      simp only [map_add, LinearMap.add_apply]
      exact integral_add (hint _ _) (hint _ _))
    (fun c v w => by
      simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply]
      exact integral_const_mul c _)
    (fun v w₁ w₂ => by
      simp only [map_add]
      exact integral_add (hint _ _) (hint _ _))
    (fun c v w => by
      simp only [LinearMap.map_smulₛₗ, smul_eq_mul]
      exact integral_const_mul _ _)
  have hI : ∀ v w, I v w = ∫ ξ, Df gl s C ξ v w ∂ν := fun _ _ => rfl
  refine ⟨I, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro v w
    rw [hI, hI, ← integral_conj]
    exact integral_congr_ae (Filter.Eventually.of_forall fun ξ => Df_herm hCp ξ v w)
  · intro v
    rw [hI]
    have := integral_re (hint v v)
    simp only [RCLike.re_to_complex] at this
    rw [← this]
    exact integral_nonneg fun ξ => Df_re_nonneg hCp ξ v
  · intro x v w
    rw [hI, hI]
    exact integral_congr_ae (Filter.Eventually.of_forall fun ξ => form_column_invariant hS hCp hCc hC' ξ x v w)
  · intro g v w
    rw [hI, hI]
    have h1 : ∀ ξ, Df gl s C ξ (gl g v) (gl g w) =
        ((md g ^ (s + 1) : ℝ) : ℂ) * Df gl s C (ξ ᵥ* (g : Matrix (Fin (m + 1)) (Fin (m + 1)) k)) v w := by
      intro ξ
      by_cases hξ : ξ = 0
      · subst hξ
        simp [Df_zero, Matrix.zero_vecMul]
      · exact Df_gl hS hC' hξ g v w
    simp_rw [h1]
    rw [integral_const_mul, integral_vecMul ν (fun ξ => Df gl s C ξ v w) g, ← mul_assoc]
    congr 1
    have hp := md_pos g
    rw [Real.rpow_add_one hp.ne']
    push_cast
    exact mul_div_cancel_right₀ _ (by exact_mod_cast hp.ne')
  · intro v
    rw [hI]
    have := integral_re (hint v v)
    simp only [RCLike.re_to_complex] at this
    rw [← this]
    have hb := bessel hψ hψ1 hS hA₀ hBp hBc hBg hD hCp hC' hCB hν v
    rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun ξ => Df_re_nonneg hCp ξ v)
      (integrable_re hψ hψ1 hS hA₀ hBp hBc hBg hD hCp hC' hCB hν v).aestronglyMeasurable]
    calc _ ≤ (ENNReal.ofReal (B v v).re).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
      _ = _ := ENNReal.toReal_ofReal (hBp.2 v)
  · intro v w
    have hxz : xz m ≠ (0 : Fin (m + 1) → k) := by
      intro h
      have := congrFun h (Fin.last m)
      simp [xz] at this
    have hloc := Df_loc hS hC' hxz v w
    rw [Df_xz hC'] at hloc
    have hU : (fun η => xz m + η) ⁻¹' {ξ | Df gl s C ξ v w = C v w} ∈ 𝓝 (0 : Fin (m + 1) → k) := by
      have ht : Tendsto (fun η : Fin (m + 1) → k => xz m + η) (𝓝 0) (𝓝 (xz m)) := by
        have := (continuous_add_left (xz m)).tendsto (0 : Fin (m + 1) → k)
        simpa using this
      exact ht hloc
    obtain ⟨A₂, hA₂, hsub⟩ := lat_shrink ψ hψ hψ1 hU
    obtain ⟨A₁, hA₁, h01, h21⟩ := lat_sup hA₀ hA₂
    refine ⟨A₁, hA₁, h01, fun A hA hA1 => ?_⟩
    rw [hI]
    have hav : ∀ ξ, Df gl s C ξ (av ψ col (xz m) A v) w =
        Set.indicator {ξ | ξ - xz m ∈ perp ψ A} (fun _ => C v w) ξ := by
      intro ξ
      rw [AvA.av_eigen' ψ hψ col hS.col_zero hS.col_add hS.smooth_col (Df gl s C ξ) ψ ξ
        (Df_col hS hCc hC' ξ) A hA (xz m) v w]
      by_cases hm : ξ - xz m ∈ perp ψ A
      · rw [Set.indicator_of_mem (show ξ ∈ {ξ | ξ - xz m ∈ perp ψ A} from hm), if_pos]
        · have h2 : ξ - xz m ∈ perp ψ A₂ := perp_anti ψ (h21.trans hA1) hm
          have h3 := hsub h2
          simpa using h3
        · intro a ha
          have := (mem_perp ψ A _).1 hm a ha
          rw [sub_dotProduct, AddChar.map_sub_eq_div, div_eq_one] at this
          exact this
      · rw [Set.indicator_of_notMem (show ξ ∉ {ξ | ξ - xz m ∈ perp ψ A} from hm), if_neg]
        intro hall
        apply hm
        rw [mem_perp]
        intro a ha
        rw [sub_dotProduct, AddChar.map_sub_eq_div, hall a ha, div_self']
    have hset : {ξ | ξ - xz m ∈ perp ψ A} = (fun ξ => ξ + -xz m) ⁻¹' (perp ψ A : Set (Fin (m + 1) → k)) := by
      ext ξ
      simp [sub_eq_add_neg]
    have hmeas : MeasurableSet {ξ | ξ - xz m ∈ perp ψ A} := by
      rw [hset]
      exact (perp_open ψ hψ hψ1 hA).measurableSet.preimage (measurable_add_const _)
    simp_rw [hav]
    rw [integral_indicator_const _ hmeas, measureReal_def, hset, measure_preimage_add_right]
    have h1 : ((A₀.relIndex A : ℝ)) * (ν (perp ψ A)).toReal = 1 := by
      have := meas_perp_index ψ ν hψ hψ1 hA₀ hA (h01.trans hA1)
      rw [hν] at this
      have := congrArg ENNReal.toReal this
      rw [ENNReal.toReal_mul, ENNReal.toReal_natCast] at this
      simpa using this.symm
    have h2 : ((A₀.relIndex A : ℂ)) * (((ν (perp ψ A)).toReal : ℝ) : ℂ) = 1 := by
      exact_mod_cast h1
    rw [Complex.real_smul, ← mul_assoc, h2, one_mul]
  · intro v w
    simp only [LinearMap.zero_apply]
    have hone : Continuous ⇑(1 : AddChar k Circle) := by
      have : ⇑(1 : AddChar k Circle) = fun _ => 1 := by
        funext x
        exact AddChar.one_apply x
      rw [this]
      exact continuous_const
    have hav : ∀ A : {A : AddSubgroup (Fin (m + 1) → k) // Lat A},
        I (av 1 col 0 A.1 v) w = ∫ ξ in (perp ψ A.1 : Set (Fin (m + 1) → k)), Df gl s C ξ v w ∂ν := by
      intro A
      rw [hI, ← integral_indicator (perp_open ψ hψ hψ1 A.2).measurableSet]
      congr 1
      funext ξ
      rw [AvA.av_eigen' 1 hone col hS.col_zero hS.col_add hS.smooth_col (Df gl s C ξ) ψ ξ
        (Df_col hS hCc hC' ξ) A.1 A.2 0 v w]
      by_cases hm : ξ ∈ perp ψ A.1
      · rw [Set.indicator_of_mem (show ξ ∈ (perp ψ A.1 : Set (Fin (m + 1) → k)) from hm), if_pos]
        intro a ha
        rw [(mem_perp ψ _ _).1 hm a ha, AddChar.one_apply]
      · rw [Set.indicator_of_notMem (show ξ ∉ (perp ψ A.1 : Set (Fin (m + 1) → k)) from hm), if_neg]
        intro hall
        apply hm
        rw [mem_perp]
        intro a ha
        rw [hall a ha, AddChar.one_apply]
    have hfun : (fun A : {A : AddSubgroup (Fin (m + 1) → k) // Lat A} => I (av 1 col 0 A.1 v) w) =
        fun A => ∫ ξ in (perp ψ A.1 : Set (Fin (m + 1) → k)), Df gl s C ξ v w ∂ν := funext hav
    rw [hfun]
    apply (hint v w).tendsto_setIntegral_nhds_zero
    rw [ENNReal.tendsto_nhds_zero]
    intro ε hε
    have h0 : ν {0} < ε := by
      rw [addHaar_singleton_zero_eq_zero hψ hψ1 ν]
      exact hε
    obtain ⟨U, hU0, hUo, hUε⟩ := Set.exists_isOpen_lt_of_lt _ _ h0
    obtain ⟨A₂, hA₂, hsub⟩ := lat_shrink ψ hψ hψ1 (hUo.mem_nhds (hU0 rfl))
    filter_upwards [Filter.mem_atTop (⟨A₂, hA₂⟩ : {A : AddSubgroup (Fin (m + 1) → k) // Lat A})] with A hA
    have hsub2 : (perp ψ A.1 : Set (Fin (m + 1) → k)) ⊆ U :=
      (SetLike.coe_subset_coe.2 (perp_anti ψ (show A₂ ≤ A.1 from hA))).trans hsub
    exact (measure_mono hsub2).trans hUε.le
  · intro Y hY hCY y hy w
    rw [hI]
    have : (fun ξ => Df gl s C ξ y w) = fun _ => (0 : ℂ) := funext fun ξ => Df_ker hCp hC' Y hY hCY ξ hy w
    rw [this, integral_zero]

end Main

theorem absLift : @AbsLift k _ _ _ _ := by
  intro ψ hψ hψ1 m V _ _ col gl hS s B B' C A₀ hA₀ hBp hBc hBg hD hCp hCc hC hCB
  letI : MeasurableSpace k := measurableSpaceFourthLift
  haveI : BorelSpace k := borelSpaceOnK
  haveI : SecondCountableTopology k := instSCK4
  let μ : Measure (Fin (m + 1) → k) := Measure.addHaar
  have h0 : μ (perp ψ A₀) ≠ 0 := meas_perp_ne_zero ψ μ hψ hψ1 hA₀
  have htop : μ (perp ψ A₀) ≠ ⊤ := (meas_perp_lt_top ψ μ hψ hψ1 hA₀).ne
  let ν : Measure (Fin (m + 1) → k) := (μ (perp ψ A₀))⁻¹ • μ
  haveI : ν.IsAddHaarMeasure :=
    Measure.IsAddHaarMeasure.smul μ (ENNReal.inv_ne_zero.2 htop) (ENNReal.inv_ne_top.2 h0)
  have hν : ν (perp ψ A₀) = 1 := by
    simp only [ν, Measure.smul_apply, smul_eq_mul]
    exact ENNReal.inv_mul_cancel h0 htop
  exact lift_form hψ hψ1 hS hA₀ hBp hBc hBg hD hCp hCc hC hCB hν

end PositivityTheory.RgUd.Form.U.Lift2
