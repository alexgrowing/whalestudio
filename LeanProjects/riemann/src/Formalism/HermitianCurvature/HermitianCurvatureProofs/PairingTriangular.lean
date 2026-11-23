import Formalism.HermitianCurvature.LatticeHerglotzBound
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HerglotzLowerSemicontinuous

namespace Formalism.FourierDecayAlt.P.PairingConjugationLemmas

open MeasureTheory Filter Topology Finset Module Formalism.FourierDecayAlt.crystallineComparison

noncomputable section

variable {f : ℕ}

def pair (σ z : V f) : ℝ := ∑ v, 2 * (σ v * z v).re

lemma psi_mul (σ z : V f) :
    psi (σ * z) = Complex.exp (2 * Real.pi * Complex.I * (pair σ z : ℂ)) := by
  unfold Formalism.FourierDecayAlt.crystallineComparison.psi pair
  congr 2
  push_cast
  refine Finset.sum_congr rfl (fun v _ => ?_)
  rw [Complex.add_conj]
  simp

lemma pair_add_left (σ σ' z : V f) : pair (σ + σ') z = pair σ z + pair σ' z := by
  unfold pair
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  simp [add_mul, mul_add]

lemma pair_smul_left (r : ℝ) (σ z : V f) : pair (r • σ) z = r * pair σ z := by
  unfold pair
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  simp [Complex.smul_re, smul_mul_assoc]
  ring

lemma pair_add_right (σ z z' : V f) : pair σ (z + z') = pair σ z + pair σ z' := by
  unfold pair
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  simp [add_mul, mul_add]

lemma pair_smul_right (r : ℝ) (σ z : V f) : pair σ (r • z) = r * pair σ z := by
  unfold pair
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  simp [Complex.smul_re, mul_smul_comm]
  ring

def pairL : V f →ₗ[ℝ] V f →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ pair pair_add_left (fun c m n => by rw [pair_smul_left, smul_eq_mul])
    pair_add_right (fun c m n => by rw [pair_smul_right, smul_eq_mul])

lemma pairL_apply (σ z : V f) : pairL σ z = pair σ z := rfl

lemma pair_conj (σ : V f) :
    pair σ (fun v => starRingEnd ℂ (σ v)) = ∑ v, 2 * Complex.normSq (σ v) := by
  unfold pair
  refine Finset.sum_congr rfl (fun v _ => ?_)
  rw [Complex.mul_conj, Complex.ofReal_re]

lemma eq_zero_of_pair (σ : V f) (h : ∀ z, pair σ z = 0) : σ = 0 := by
  have h0 := h (fun v => starRingEnd ℂ (σ v))
  rw [pair_conj] at h0
  have h1 : ∀ v ∈ (Finset.univ : Finset (Fin f)), 2 * Complex.normSq (σ v) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun v _ => mul_nonneg (by norm_num) (Complex.normSq_nonneg _))).mp h0
  funext v
  have h2 := h1 v (Finset.mem_univ v)
  simpa using h2

section Lat

variable (La : Submodule ℤ (V f)) [DiscreteTopology La] [IsZLattice ℝ La]

def bR : Basis (Fin (finrank ℤ La)) ℝ (V f) := (Module.finBasis ℤ La).ofZLatticeBasis ℝ La

lemma bR_apply (j : Fin (finrank ℤ La)) : bR La j = ((Module.finBasis ℤ La) j : V f) := by
  simp [bR]

lemma bR_mem (j : Fin (finrank ℤ La)) : bR La j ∈ La := by
  rw [bR_apply]
  exact ((Module.finBasis ℤ La) j).2

lemma mem_iff (z : V f) : z ∈ La ↔ ∀ j, (bR La).repr z j ∈ Set.range (algebraMap ℤ ℝ) := by
  conv_lhs => rw [← Module.Basis.ofZLatticeBasis_span ℝ La (Module.finBasis ℤ La)]
  exact Module.Basis.mem_span_iff_repr_mem ℤ (bR La) z

def Tl : (Fin (finrank ℤ La) → ℝ) ≃L[ℝ] V f := (bR La).equivFun.symm.toContinuousLinearEquiv

lemma Tl_apply (y : Fin (finrank ℤ La) → ℝ) : Tl La y = ∑ j, y j • bR La j := by
  simp [Tl, Basis.equivFun_symm_apply]

lemma Tl_symm_apply (z : V f) : (Tl La).symm z = fun j => (bR La).repr z j := by
  funext j
  simp [Tl]

lemma repr_Tl (y : Fin (finrank ℤ La) → ℝ) (j) : (bR La).repr (Tl La y) j = y j := by
  exact congrFun ((bR La).equivFun.apply_symm_apply y) j

lemma pair_Tl (σ : V f) (y : Fin (finrank ℤ La) → ℝ) :
    pair σ (Tl La y) = ∑ j, y j * pair σ (bR La j) := by
  rw [Tl_apply, ← pairL_apply, map_sum]
  simp only [map_smul, pairL_apply, smul_eq_mul]

def Lm : V f →ₗ[ℝ] (Fin (finrank ℤ La) → ℝ) where
  toFun σ := fun j => pair σ (bR La j)
  map_add' σ σ' := by
    funext j
    simp only [Pi.add_apply, pair_add_left]
  map_smul' r σ := by
    funext j
    simp only [Pi.smul_apply, pair_smul_left, smul_eq_mul, RingHom.id_apply]

lemma Lm_inj : Function.Injective (Lm La) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro σ hσ
  apply eq_zero_of_pair
  intro z
  have hj : ∀ j, pair σ (bR La j) = 0 := fun j => congrFun hσ j
  rw [← (Tl La).apply_symm_apply z, pair_Tl]
  simp [hj]

lemma Lm_bij : Function.Bijective (Lm La) := by
  refine ⟨Lm_inj La, ?_⟩
  rw [← LinearMap.injective_iff_surjective_of_finrank_eq_finrank]
  · exact Lm_inj La
  · rw [Module.finrank_fin_fun, ZLattice.rank ℝ La]

def Le : V f ≃ₗ[ℝ] (Fin (finrank ℤ La) → ℝ) := LinearEquiv.ofBijective (Lm La) (Lm_bij La)

lemma Le_apply (σ : V f) (j) : Le La σ j = pair σ (bR La j) := rfl

def ψd (m : Fin (finrank ℤ La) → ℤ) : V f := (Le La).symm (fun j => (m j : ℝ))

lemma pair_ψd (m : Fin (finrank ℤ La) → ℤ) (j) : pair (ψd La m) (bR La j) = m j := by
  rw [← Le_apply, ψd, LinearEquiv.apply_symm_apply]

lemma ψd_inj : Function.Injective (ψd La) := by
  intro m m' h
  funext j
  have h1 := pair_ψd La m j
  rw [h, pair_ψd] at h1
  exact_mod_cast h1.symm

lemma ψd_sub (m m' : Fin (finrank ℤ La) → ℤ) : ψd La (m - m') = ψd La m - ψd La m' := by
  simp only [ψd]
  rw [← map_sub]
  congr 1
  funext j
  simp

lemma pair_ψd_Tl (m : Fin (finrank ℤ La) → ℤ) (y : Fin (finrank ℤ La) → ℝ) :
    pair (ψd La m) (Tl La y) = ∑ j, y j * (m j : ℝ) := by
  rw [pair_Tl]
  simp [pair_ψd]

lemma psi_ψd_Tl (m : Fin (finrank ℤ La) → ℤ) (y : Fin (finrank ℤ La) → ℝ) :
    psi (ψd La m * Tl La y) =
      Complex.exp (2 * Real.pi * Complex.I * ∑ j, ((m j : ℝ) : ℂ) * (y j : ℂ)) := by
  rw [psi_mul, pair_ψd_Tl]
  congr 2
  push_cast
  exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)

lemma ψd_mem (m : Fin (finrank ℤ La) → ℤ) : ψd La m ∈ dualSet La := by
  show ∀ z ∈ La, psi (ψd La m * z) = 1
  intro z hz
  obtain ⟨n, hn⟩ : ∃ n : Fin (finrank ℤ La) → ℤ, ∀ j, (bR La).repr z j = n j := by
    have h1 := (mem_iff La z).mp hz
    exact ⟨fun j => (h1 j).choose, fun j => by simpa using (h1 j).choose_spec.symm⟩
  rw [← (Tl La).apply_symm_apply z, psi_ψd_Tl, Tl_symm_apply]
  have hs : (∑ j, ((m j : ℝ) : ℂ) * (((bR La).repr z j : ℝ) : ℂ)) = ((∑ j, m j * n j : ℤ) : ℂ) := by
    push_cast
    simp [hn]
  rw [hs, mul_comm, Complex.exp_int_mul_two_pi_mul_I]

lemma ψd_surj (σ : V f) (hσ : σ ∈ dualSet La) : ∃ m, ψd La m = σ := by
  have hσ' : ∀ z ∈ La, psi (σ * z) = 1 := hσ
  have hint : ∀ j, ∃ n : ℤ, pair σ (bR La j) = n := by
    intro j
    have h1 := hσ' (bR La j) (bR_mem La j)
    rw [psi_mul, Complex.exp_eq_one_iff] at h1
    obtain ⟨n, hn⟩ := h1
    refine ⟨n, ?_⟩
    have h2 : ((pair σ (bR La j) : ℝ) : ℂ) = (n : ℂ) := by
      have hne : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
        simp [Real.pi_ne_zero, Complex.I_ne_zero]
      apply mul_left_cancel₀ hne
      rw [hn]
      ring
    exact_mod_cast h2
  choose m hm using hint
  refine ⟨m, ?_⟩
  apply (Le La).injective
  rw [ψd, LinearEquiv.apply_symm_apply]
  funext j
  rw [Le_apply, hm]

def eD : (Fin (finrank ℤ La) → ℤ) ≃ dualSet La :=
  Equiv.ofBijective (fun m => ⟨ψd La m, ψd_mem La m⟩)
    ⟨fun m m' h => ψd_inj La (congrArg Subtype.val h),
     fun σ => by
      obtain ⟨m, hm⟩ := ψd_surj La σ.1 σ.2
      exact ⟨m, Subtype.ext hm⟩⟩

lemma eD_apply (m : Fin (finrank ℤ La) → ℤ) : ((eD La m : dualSet La) : V f) = ψd La m := rfl

lemma Tl_emb : MeasurableEmbedding (Tl La) := (Tl La).toHomeomorph.measurableEmbedding

lemma vol_eq : ∃ c : NNReal, 0 < c ∧
    (volume : Measure (V f)) = c • Measure.map (Tl La) (volume : Measure (Fin (finrank ℤ La) → ℝ)) := by
  haveI : (Measure.map (Tl La) (volume : Measure (Fin (finrank ℤ La) → ℝ))).IsAddHaarMeasure :=
    (Tl La).isAddHaarMeasure_map _
  exact ⟨_, Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _,
    Measure.isAddLeftInvariant_eq_smul _ _⟩

lemma map_fd :
    Measure.map (Tl La) (volume : Measure (Fin (finrank ℤ La) → ℝ)) (ZSpan.fundamentalDomain (bR La)) = 1 := by
  rw [(Tl_emb La).map_apply]
  have hpre : (Tl La) ⁻¹' ZSpan.fundamentalDomain (bR La) =
      Set.univ.pi (fun _ => Set.Ico (0 : ℝ) 1) := by
    ext y
    simp [ZSpan.mem_fundamentalDomain, repr_Tl]
  rw [hpre, MeasureTheory.volume_pi_pi]
  simp [Real.volume_Ico]

lemma covol_eq (c : NNReal)
    (hc : (volume : Measure (V f)) = c • Measure.map (Tl La) (volume : Measure (Fin (finrank ℤ La) → ℝ))) :
    ZLattice.covolume La volume = (c : ℝ) := by
  have hfd := ZSpan.isAddFundamentalDomain (bR La) (volume : Measure (V f))
  rw [show Submodule.span ℤ (Set.range (bR La)) = La from
    Module.Basis.ofZLatticeBasis_span ℝ La _] at hfd
  rw [ZLattice.covolume_eq_measure_fundamentalDomain La volume hfd, hc, measureReal_def, Measure.smul_apply, map_fd]
  simp

end Lat

end

end Formalism.FourierDecayAlt.P.PairingConjugationLemmas

namespace Formalism.FourierDecayAlt.P

open MeasureTheory Filter Topology Finset Module Formalism.FourierDecayAlt.crystallineComparison Formalism.FourierDecayAlt.P.PairingConjugationLemmas

theorem latticeHerglotzBound_statement : Formalism.FourierDecayAlt.crystallineComparison.LatticeHerglotzBound := by
  intro f La _ _ N A hN0 hlsc hint hPD hsum z₀ S hS
  obtain ⟨c, hcpos, hc⟩ := vol_eq La
  have hcR : (0 : ℝ) < c := hcpos
  have hcov := covol_eq La c hc
  set T := Tl La with hT

  have hint_tr : ∀ g : V f → ℂ, ∫ z, g z = (c : ℂ) * ∫ y, g (T y) := by
    intro g
    rw [hc, integral_smul_nnreal_measure, (Tl_emb La).integral_map, NNReal.smul_def, Complex.real_smul]

  set N' : (Fin (finrank ℤ La) → ℝ) → ℝ := fun y => N (T y) with hN'
  set A' : (Fin (finrank ℤ La) → ℤ) → ℂ := fun m => A (ψd La m) / (c : ℂ) with hA'
  have hN'0 : ∀ y, 0 ≤ N' y := fun y => hN0 _
  have hlsc' : LowerSemicontinuous N' := hlsc.comp T.continuous
  have hint' : Integrable N' := by
    have h1 : Integrable N (Measure.map T volume) := by
      have := hint.smul_measure_nnreal (c := c⁻¹)
      rwa [hc, smul_smul, inv_mul_cancel₀ hcpos.ne', one_smul] at this
    exact ((Tl_emb La).integrable_map_iff).1 h1
  have hk : ∀ m : Fin (finrank ℤ La) → ℤ,
      (∫ y, (N' y : ℂ) * Complex.exp (2 * Real.pi * Complex.I * ∑ j, ((m j : ℝ) : ℂ) * (y j : ℂ))) + A' m =
        (crystallineComparison.fourier N (ψd La m) + A (ψd La m)) / (c : ℂ) := by
    intro m
    have hcC : (c : ℂ) ≠ 0 := by exact_mod_cast hcR.ne'
    have h1 : crystallineComparison.fourier N (ψd La m) = (c : ℂ) *
        ∫ y, (N' y : ℂ) * Complex.exp (2 * Real.pi * Complex.I * ∑ j, ((m j : ℝ) : ℂ) * (y j : ℂ)) := by
      unfold crystallineComparison.fourier
      rw [hint_tr]
      congr 1
      refine integral_congr_ae (Filter.Eventually.of_forall (fun y => ?_))
      simp only [hN']
      rw [psi_ψd_Tl]
    rw [h1, hA']
    field_simp
  have hPD' : ∀ (S0 : Finset (Fin (finrank ℤ La) → ℤ)) (c0 : (Fin (finrank ℤ La) → ℤ) → ℂ),
      0 ≤ (∑ σ ∈ S0, ∑ σ' ∈ S0, A' (σ - σ') * c0 σ * starRingEnd ℂ (c0 σ')).re := by
    intro S0 c0
    have hinj := ψd_inj La
    have h := hPD (S0.image (ψd La)) (c0 ∘ Function.invFun (ψd La)) (by
      intro σ hσ
      obtain ⟨m, _, rfl⟩ := Finset.mem_image.1 hσ
      exact ψd_mem La m)
    have hsi : ∀ F : V f → ℂ, ∑ x ∈ S0.image (ψd La), F x = ∑ m ∈ S0, F (ψd La m) :=
      fun F => Finset.sum_image (by intro x _ y _ h; exact hinj h)
    simp only [hsi] at h
    simp only [Function.comp_apply, Function.leftInverse_invFun hinj _, ← ψd_sub] at h
    have e : (∑ σ ∈ S0, ∑ σ' ∈ S0, A' (σ - σ') * c0 σ * starRingEnd ℂ (c0 σ')) =
        (∑ σ ∈ S0, ∑ σ' ∈ S0, A (ψd La (σ - σ')) * c0 σ * starRingEnd ℂ (c0 σ')) / ((c : ℝ) : ℂ) := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl (fun σ _ => ?_)
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl (fun σ' _ => ?_)
      rw [hA']
      ring
    rw [e, Complex.div_ofReal_re]
    exact div_nonneg h hcR.le
  have hsum' : Summable (fun m : Fin (finrank ℤ La) → ℤ =>
      ‖(∫ y, (N' y : ℂ) * Complex.exp (2 * Real.pi * Complex.I * ∑ j, ((m j : ℝ) : ℂ) * (y j : ℂ))) + A' m‖) := by
    simp_rw [hk]
    have h := (Equiv.summable_iff (eD La)).2 hsum
    refine (h.div_const (c : ℝ)).congr (fun m => ?_)
    simp only [Function.comp_apply, eD_apply, norm_div]
    congr 1
    simp

  set z₀' := T.symm z₀ with hz₀'
  let κ : V f → (Fin (finrank ℤ La) → ℤ) := fun z j => ⌊(bR La).repr (z - z₀) j⌋
  have hκ : ∀ z ∈ S, (fun j => ((κ z j : ℤ) : ℝ)) = T.symm (z - z₀) := by
    intro z hz
    have hm := (mem_iff La (z - z₀)).1 (hS z hz)
    rw [hT, Tl_symm_apply]
    funext j
    obtain ⟨n, hn⟩ := hm j
    simp only [κ, ← hn, algebraMap_int_eq, eq_intCast, Int.floor_intCast]
  have hκinj : ∀ x ∈ S, ∀ y ∈ S, κ x = κ y → x = y := by
    intro x hx y hy h
    have h1 := hκ x hx
    rw [h, hκ y hy] at h1
    have h2 := T.symm.injective h1
    simpa using h2.symm
  have H := Formalism.FourierDecayAlt.P.herglotz_lower_semicontinuous (finrank ℤ La) N' A' hN'0 hlsc' hint' hPD' hsum' z₀' (S.image κ)
  rw [Finset.sum_image (by intro x hx y hy h; exact hκinj x hx y hy h)] at H
  have hL : ∀ z ∈ S, N' (fun j => z₀' j + ((κ z j : ℤ) : ℝ)) = N z := by
    intro z hz
    have e1 : (fun j => z₀' j + ((κ z j : ℤ) : ℝ)) = z₀' + T.symm (z - z₀) := by
      rw [← hκ z hz]
      rfl
    simp only [hN']
    rw [e1, map_add, hz₀', ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearEquiv.apply_symm_apply]
    congr 1
    abel
  rw [Finset.sum_congr rfl hL] at H
  have hR : (∑' m : Fin (finrank ℤ La) → ℤ,
      ‖(∫ y, (N' y : ℂ) * Complex.exp (2 * Real.pi * Complex.I * ∑ j, ((m j : ℝ) : ℂ) * (y j : ℂ))) + A' m‖) =
      (∑' σ : dualSet La, ‖crystallineComparison.fourier N σ + A (σ : V f)‖) / (c : ℝ) := by
    simp_rw [hk]
    rw [← Equiv.tsum_eq (eD La), ← tsum_div_const]
    refine tsum_congr (fun m => ?_)
    rw [eD_apply, norm_div]
    congr 1
    simp
  rw [hR, le_div_iff₀ hcR] at H
  rw [hcov]
  linarith

end Formalism.FourierDecayAlt.P
