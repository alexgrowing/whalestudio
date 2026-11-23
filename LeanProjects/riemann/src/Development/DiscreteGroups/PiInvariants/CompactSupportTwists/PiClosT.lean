import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PiClosU

set_option linter.all false

noncomputable section

open NumberField Matrix MeasureTheory Filter Set
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.CuspRep.CuspidalL2GL PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.Desc
open scoped ENNReal

namespace DiscreteGroups.T1.G

attribute [local instance] borelH

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem borelSpace_H : BorelSpace (H E n 0) := ⟨rfl⟩

attribute [local instance] borelSpace_H

theorem GL_zero_subsingleton (a b : GA E 0) : a = b := Units.ext (Matrix.ext fun i => Fin.elim0 i)

def eH : GA E n ≃ₜ* H E n 0 where
  toFun g := (g, 1)
  invFun x := x.1
  left_inv g := rfl
  right_inv x := Prod.ext rfl (GL_zero_subsingleton _ _)
  map_mul' g h := Prod.ext rfl (mul_one 1).symm
  continuous_toFun := continuous_id.prodMk continuous_const
  continuous_invFun := continuous_fst

theorem eH_symm_apply (x : H E n 0) : (eH (E := E) (n := n)).symm x = x.1 := rfl

def muG (D : Dom E n 0) : Measure (GA E n) := D.μ.map (eH (E := E) (n := n)).symm

theorem measurable_eH : Measurable (eH (E := E) (n := n)) := (eH (E := E) (n := n)).continuous.measurable

theorem measurable_eH_symm : Measurable (eH (E := E) (n := n)).symm :=
  (eH (E := E) (n := n)).symm.continuous.measurable

theorem mp_fst (D : Dom E n 0) : MeasurePreserving (fun x : H E n 0 => x.1) D.μ (muG D) :=
  ⟨measurable_eH_symm, rfl⟩

theorem mp_eH (D : Dom E n 0) : MeasurePreserving (eH (E := E) (n := n)) (muG D) D.μ := by
  refine ⟨measurable_eH, ?_⟩
  rw [muG, Measure.map_map measurable_eH measurable_eH_symm]
  have : (eH (E := E) (n := n)) ∘ (eH (E := E) (n := n)).symm = id := funext fun x => (eH (E := E) (n := n)).apply_symm_apply x
  rw [this, Measure.map_id]

theorem isHaar_D (D : Dom E n 0) : D.μ.IsHaarMeasure := by
  obtain ⟨h1, h2, h3, h4⟩ := D.haar
  exact { toIsFiniteMeasureOnCompacts := inferInstance, toIsMulLeftInvariant := h1, toIsOpenPosMeasure := h3 }

instance muG_haar (D : Dom E n 0) : (muG D).IsHaarMeasure := by
  haveI := isHaar_D D
  exact (eH (E := E) (n := n)).symm.isHaarMeasure_map D.μ

instance muG_right (D : Dom E n 0) : (muG D).IsMulRightInvariant := by
  haveI := D.haar.2.1
  refine ⟨fun g => ?_⟩
  rw [muG, Measure.map_map (continuous_mul_right g).measurable measurable_eH_symm]
  have e : (fun x => x * g) ∘ (eH (E := E) (n := n)).symm =
      (eH (E := E) (n := n)).symm ∘ fun x => x * eH g := funext fun x => by
    simp only [Function.comp_apply, map_mul, ContinuousMulEquiv.symm_apply_apply]
  rw [e, ← Measure.map_map measurable_eH_symm (continuous_mul_right _).measurable, map_mul_right_eq_self]

def eR (δ : ratH E n 0) : (ratGL E n).range :=
  ⟨(δ : H E n 0).1, by
    obtain ⟨p, hp⟩ := δ.2
    exact ⟨p.1, congrArg Prod.fst hp⟩⟩

theorem eR_bijective : Function.Bijective (eR (E := E) (n := n)) := by
  refine ⟨fun δ δ' h => Subtype.ext (Prod.ext (congrArg Subtype.val h) (GL_zero_subsingleton _ _)), fun γ => ?_⟩
  obtain ⟨γ₁, hγ⟩ := γ.2
  refine ⟨⟨((γ : GA E n), 1), ⟨(γ₁, 1), Prod.ext hγ (GL_zero_subsingleton _ _)⟩⟩, rfl⟩

theorem isFundamentalDomain_pre (D : Dom E n 0) :
    IsFundamentalDomain (ratGL E n).range ((eH (E := E) (n := n)) ⁻¹' D.F) (muG D) :=
  D.fd.preimage_of_equiv (mp_eH D).quasiMeasurePreserving eR_bijective fun δ x => by
    change (((δ : H E n 0).1 * x, 1) : H E n 0) = (δ : H E n 0) * (x, 1)
    exact Prod.ext rfl (GL_zero_subsingleton _ _)

theorem lintegral_nu (D : Dom E n 0) (Φ : GA E n → ℝ≥0∞) (hΦ : ∀ γ ∈ (ratGL E n).range, ∀ g, Φ (γ * g) = Φ g) :
    ∫⁻ x, Φ x.1 ∂D.ν = ∫⁻ g in stdDom (ratGL E n).range, Φ g ∂muG D := by
  let eM : GA E n ≃ᵐ H E n 0 := (eH (E := E) (n := n)).toHomeomorph.toMeasurableEquiv
  have hm : (muG D).map eM = D.μ := (mp_eH D).map_eq
  rw [Dom.ν, ← hm, eM.restrict_map, lintegral_map_equiv]
  refine (isFundamentalDomain_pre D).setLIntegral_eq (isFundamentalDomain_stdDom _ _) (fun g => Φ g) fun γ g => ?_
  rw [Subgroup.smul_def, smul_eq_mul]
  exact hΦ γ γ.2 g

theorem lg_rat_mul (γ : GA E n) (hγ : γ ∈ (ratGL E n).range) (g : GA E n) : lg (γ * g) = lg g := by
  obtain ⟨γ₁, rfl⟩ := hγ
  rw [lg_mul, lg_rat, zero_add]

theorem tsum_shift_le (u : ℝ → ℂ) (hu : Continuous u) (hs : HasCompactSupport u) (c : ℝ) (hc : 0 < c) :
    ∃ K : ℝ≥0∞, K ≠ ⊤ ∧ ∀ s : ℝ, ∑' m : ℤ, ‖u (s + m * c)‖ₑ ^ (2 : ℝ) ≤ K := by
  obtain ⟨M, hM⟩ := hu.bounded_above_of_compact_support hs
  obtain ⟨R, hR⟩ := hs.isCompact.isBounded.subset_closedBall 0
  let N : ℕ := ⌈2 * |R| / c⌉₊ + 1
  refine ⟨N * ENNReal.ofReal M ^ (2 : ℝ), by finiteness, fun s => ?_⟩
  let a : ℤ := ⌈(-|R| - s) / c⌉
  let S : Finset ℤ := Finset.Icc a (a + ⌈2 * |R| / c⌉₊)
  have hz : ∀ m ∉ S, ‖u (s + m * c)‖ₑ ^ (2 : ℝ) = 0 := fun m hm => by
    have hu0 : u (s + m * c) = 0 := by
      refine image_eq_zero_of_notMem_tsupport fun ht => hm ?_
      have h1 := hR ht
      rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs, abs_le] at h1
      have hR' : R ≤ |R| := le_abs_self R
      rw [Finset.mem_Icc]
      constructor
      · refine Int.ceil_le.2 ?_
        rw [div_le_iff₀ hc]
        linarith
      · have h2 : ((m : ℝ) - a) * c ≤ 2 * |R| := by
          have ha : (a : ℝ) ≥ (-|R| - s) / c := Int.le_ceil _
          rw [ge_iff_le, div_le_iff₀ hc] at ha
          nlinarith
        have h3 : ((m : ℝ) - a) ≤ 2 * |R| / c := by rw [le_div_iff₀ hc]; linarith
        have h4 : (2 * |R| / c) ≤ (⌈2 * |R| / c⌉₊ : ℝ) := Nat.le_ceil _
        have h5 : ((m - a : ℤ) : ℝ) ≤ ((⌈2 * |R| / c⌉₊ : ℕ) : ℤ) := by push_cast; linarith
        have h6 := Int.cast_le.1 h5
        omega
    rw [hu0, enorm_zero, ENNReal.zero_rpow_of_pos (by norm_num)]
  rw [tsum_eq_sum hz]
  have hb : ∀ m ∈ S, ‖u (s + m * c)‖ₑ ^ (2 : ℝ) ≤ ENNReal.ofReal M ^ (2 : ℝ) := fun m _ =>
    ENNReal.rpow_le_rpow (by
      rw [← ofReal_norm_eq_enorm]
      exact ENNReal.ofReal_le_ofReal (hM _)) (by norm_num)
  refine (Finset.sum_le_sum hb).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  gcongr
  have : S.card = ⌈2 * |R| / c⌉₊ + 1 := by
    simp only [S, Int.card_Icc]
    omega
  rw [this]
  try simp [N]

variable (D : Dom E n 0)

def Tf (u : ℝ → ℂ) (F : L2 (latticeGL E n) (muG D)) : H E n 0 → ℂ :=
  fun x => lift (latticeGL E n) F x.1 * u (ldet x)

theorem ldet_eq (x : H E n 0) : ldet x = lg x.1 := rfl

theorem aesm_Tf (u : ℝ → ℂ) (hu : Continuous u) (F : L2 (latticeGL E n) (muG D)) :
    AEStronglyMeasurable (Tf D u F) D.ν := by
  have h1 : AEStronglyMeasurable (lift (latticeGL E n) F) (muG D) :=
    aestronglyMeasurable_quotMeasure_iff_lift.1 (Lp.aestronglyMeasurable F)
  have h2 : AEStronglyMeasurable (fun x : H E n 0 => lift (latticeGL E n) F x.1) D.μ :=
    h1.comp_measurePreserving (mp_fst D)
  exact (h2.mul (hu.comp continuous_ldet).aestronglyMeasurable).restrict

theorem lintegral_Tf (hn : 1 ≤ n) (u : ℝ → ℂ) (hu : Continuous u) (F : L2 (latticeGL E n) (muG D)) :
    ∫⁻ x, ‖Tf D u F x‖ₑ ^ (2 : ℝ) ∂D.ν =
      ∫⁻ q, ‖F q‖ₑ ^ (2 : ℝ) * ∑' m : ℤ, ‖u (lg q.out + m * lg (splitCentre E n 1))‖ₑ ^ (2 : ℝ)
        ∂quotMeasure (latticeGL E n) (muG D) := by
  have e1 : ∀ x : H E n 0, ‖Tf D u F x‖ₑ ^ (2 : ℝ) =
      (fun g => ‖lift (latticeGL E n) F g‖ₑ ^ (2 : ℝ) * ‖u (lg g)‖ₑ ^ (2 : ℝ)) x.1 := fun x => by
    simp only [Tf, enorm_mul, ldet_eq]
    exact ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)
  refine (lintegral_congr e1).trans ((lintegral_nu D _ fun γ hγ g => ?_).trans
    ((lintegral_unfold (muG D) hn (fun g => ‖lift (latticeGL E n) F g‖ₑ ^ (2 : ℝ))
      (fun γ hγ g => by simp only [(memL2_lift F).1 γ hγ g])
      ((aestronglyMeasurable_quotMeasure_iff_lift.1 (Lp.aestronglyMeasurable F)).enorm.pow_const _)
      (fun s => ‖u s‖ₑ ^ (2 : ℝ)) (hu.measurable.enorm.pow_const _)).trans
      (lintegral_congr fun q => ?_)))
  · simp only [lg_rat_mul γ hγ g, (memL2_lift F).1 γ (ratRange_le hγ) g]
  · simp only [lift, Quotient.out_eq]

theorem exists_bound (hn : 1 ≤ n) (u : ℝ → ℂ) (hu : Continuous u) (hs : HasCompactSupport u) :
    ∃ k : ℝ, 0 ≤ k ∧ ∀ F : L2 (latticeGL E n) (muG D),
      MemLp (Tf D u F) 2 D.ν ∧ eLpNorm (Tf D u F) 2 D.ν ≤ ENNReal.ofReal k * eLpNorm F 2 (quotMeasure (latticeGL E n) (muG D)) := by
  obtain ⟨K, hK, hKs⟩ := tsum_shift_le u hu hs _ (lg_e_pos (E := E) hn)
  refine ⟨Real.sqrt K.toReal, Real.sqrt_nonneg _, fun F => ?_⟩
  have hk : ENNReal.ofReal (Real.sqrt K.toReal) ^ (2 : ℝ) = K := by
    rw [ENNReal.ofReal_rpow_of_nonneg (Real.sqrt_nonneg _) (by norm_num), Real.rpow_two, Real.sq_sqrt ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hK]
  have hle : ∫⁻ x, ‖Tf D u F x‖ₑ ^ (2 : ℝ) ∂D.ν ≤
      ∫⁻ q, ‖(Real.sqrt K.toReal : ℂ) • F q‖ₑ ^ (2 : ℝ) ∂quotMeasure (latticeGL E n) (muG D) := by
    rw [lintegral_Tf D hn u hu F]
    refine lintegral_mono fun q => ?_
    rw [enorm_smul, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), mul_comm]
    gcongr
    rw [← ofReal_norm_eq_enorm, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _), hk]
    exact hKs _
  have key : eLpNorm (Tf D u F) 2 D.ν ≤ eLpNorm (fun q => (Real.sqrt K.toReal : ℂ) • F q) 2
      (quotMeasure (latticeGL E n) (muG D)) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm two_ne_zero ENNReal.ofNat_ne_top,
      eLpNorm_eq_lintegral_rpow_enorm two_ne_zero ENNReal.ofNat_ne_top]
    simp only [ENNReal.toReal_ofNat]
    exact ENNReal.rpow_le_rpow hle (by norm_num)
  have key2 : eLpNorm (fun q => (Real.sqrt K.toReal : ℂ) • F q) 2 (quotMeasure (latticeGL E n) (muG D)) =
      ENNReal.ofReal (Real.sqrt K.toReal) * eLpNorm F 2 (quotMeasure (latticeGL E n) (muG D)) := by
    change eLpNorm ((Real.sqrt K.toReal : ℂ) • (F : GlobalTheory.AutomorphicL2Unitary.Quot (latticeGL E n) → ℂ)) 2 _ = _
    rw [eLpNorm_const_smul, ← ofReal_norm_eq_enorm, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  rw [key2] at key
  refine ⟨⟨aesm_Tf D u hu F, key.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (Lp.eLpNorm_lt_top F))⟩, key⟩

end DiscreteGroups.T1.G
