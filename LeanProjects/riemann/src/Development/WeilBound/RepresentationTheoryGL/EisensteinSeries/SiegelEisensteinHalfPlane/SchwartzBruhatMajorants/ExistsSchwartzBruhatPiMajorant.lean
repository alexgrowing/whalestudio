import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.HeisenbergTheta.HeisenbergThetaConstant.ThetaC
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsNormTheta2TailLeOfLeOne
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LinearChangeMemSchwartzBruhatPiStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsSummableMajorantLatticeSumStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaSubValueZeroRapidDecayStatement
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.SchwartzBruhatMajorants.ThetaCScalCEq
set_option maxSynthPendingDepth 1
set_option synthInstance.maxSize 1000
open NumberField Matrix MeasureTheory Filter Topology
open scoped NumberField.AdeleRing
open PositivityTheory.He2M1 GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix IdeleGroup PositivityTheory.RgEis

namespace GlobalTheory.CompanionTheory.EpsteinUnfold.Hd

open NumberField.mixedEmbedding
open scoped SchwartzMap Classical

section SlopeTestRemainingChoices

variable {k : Type} [Field k] [NumberField k] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem exists_schwartzBruhatPi_majorant {F : (ι → 𝔸[k]) → ℂ} (hF : F ∈ schwartzBruhatPi k ι) :
    ∃ G ∈ schwartzBruhatPi k ι, ∃ r : (ι → 𝔸[k]) → ℝ,
      (∀ x, G x = (r x : ℂ)) ∧ ∀ x, ‖F x‖ ≤ r x := by
  rw [schwartzBruhatPi_eq_cosetSpanPi] at hF
  induction hF using Submodule.span_induction with
  | mem H hH =>
    obtain ⟨φ, I, b, rfl⟩ := hH
    obtain ⟨Φ, r, hΦ, hr⟩ := GlobalTheory.CompanionTheory.EisRk1.exists_schwartz_majorant φ
    set g : (ι → 𝔸ᶠ[k]) → ℂ := finiteTensor fun i ↦ cosetIndicator I (b i) with hg
    have hgv : ∀ v, g v = (‖g v‖ : ℂ) := by
      intro v
      simp only [hg, finiteTensor]
      rw [norm_prod, Complex.ofReal_prod]
      refine Finset.prod_congr rfl fun i _ ↦ ?_
      rw [cosetIndicator_apply]
      split_ifs <;> simp
    refine ⟨schwartzBruhatTensorPi Φ g, schwartzBruhatTensorPi_mem Φ
      (finiteTensor_mem fun i ↦ cosetIndicator_mem_finiteSchwartzBruhat I (b i)),
      fun x ↦ r (infPartPi x) * ‖g (finPartPi x)‖, fun x ↦ ?_, fun x ↦ ?_⟩
    · simp only [schwartzBruhatTensorPi]
      rw [hΦ, Complex.ofReal_mul, ← hgv]
    · simp only [schwartzBruhatTensorPi, norm_mul]
      exact mul_le_mul_of_nonneg_right (hr _) (norm_nonneg _)
  | zero => exact ⟨0, zero_mem _, 0, by simp, by simp⟩
  | add H₁ H₂ _ _ ih₁ ih₂ =>
    obtain ⟨G₁, m₁, r₁, e₁, b₁⟩ := ih₁
    obtain ⟨G₂, m₂, r₂, e₂, b₂⟩ := ih₂
    refine ⟨G₁ + G₂, add_mem m₁ m₂, r₁ + r₂, fun x ↦ ?_, fun x ↦ ?_⟩
    · simp [e₁, e₂]
    · exact (norm_add_le _ _).trans (add_le_add (b₁ x) (b₂ x))
  | smul c H _ ih =>
    obtain ⟨G, m, r, e, b⟩ := ih
    refine ⟨(‖c‖ : ℂ) • G, Submodule.smul_mem _ _ m, ‖c‖ • r, fun x ↦ ?_, fun x ↦ ?_⟩
    · simp [e]
    · simp only [Pi.smul_apply, smul_eq_mul, norm_mul]
      exact mul_le_mul_of_nonneg_left (b x) (norm_nonneg _)

theorem single_mem_schwartzBruhat {F : (ι → 𝔸[k]) → ℂ} (hF : F ∈ schwartzBruhatPi k ι) (i₀ : ι) :
    (fun t : 𝔸[k] ↦ F (Pi.single i₀ t)) ∈ schwartzBruhat k := by
  induction hF using Submodule.span_induction with
  | mem G hG =>
    obtain ⟨φ, g, hg, rfl⟩ := hG
    set L : mixedSpace k →L[ℝ] (ι → mixedSpace k) :=
      ContinuousLinearMap.single ℝ (fun _ : ι ↦ mixedSpace k) i₀
    have hL : ∀ u, L u = Pi.single i₀ u := fun u ↦ rfl
    set φ' : 𝓢(mixedSpace k, ℂ) := SchwartzMap.compCLM ℂ L.hasTemperateGrowth
      ⟨1, 1, fun u ↦ by rw [hL, Pi.norm_single, one_mul, pow_one]; linarith⟩ φ
    have hφ' : ∀ u, φ' u = φ (Pi.single i₀ u) := fun u ↦ rfl
    have hcl : Topology.IsClosedEmbedding (fun v : 𝔸ᶠ[k] ↦ (Pi.single i₀ v : ι → 𝔸ᶠ[k])) :=
      Function.LeftInverse.isClosedEmbedding (f := fun x : ι → 𝔸ᶠ[k] ↦ x i₀)
        (fun v ↦ Pi.single_eq_same _ _) (continuous_apply i₀) ((continuous_const (y := (0 : ι → 𝔸ᶠ[k]))).update i₀ continuous_id)
    have hg' : (fun v : 𝔸ᶠ[k] ↦ g (Pi.single i₀ v)) ∈ finiteSchwartzBruhat k := by
      obtain ⟨hlc, hcs⟩ := (mem_finiteSchwartzBruhatPi k).mp hg
      exact mem_finiteSchwartzBruhat.2
        ⟨hlc.comp_continuous hcl.continuous, hcs.comp_isClosedEmbedding hcl⟩
    convert schwartzBruhatTensor_mem φ' hg' using 1
    funext t
    simp only [schwartzBruhatTensorPi, schwartzBruhatTensor, hφ']
    congr 2
    · funext i
      by_cases h : i = i₀
      · subst h
        simp [infPartPi]
      · simp only [infPartPi, Pi.single_eq_of_ne h]
        exact map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace k)
    · funext i
      by_cases h : i = i₀
      · subst h
        simp [finPartPi]
      · simp only [finPartPi, Pi.single_eq_of_ne h]
        rfl
  | zero => exact zero_mem _
  | add G H _ _ hG hH => exact add_mem hG hH
  | smul c G _ hG => exact Submodule.smul_mem _ c hG

theorem line_mem_schwartzBruhat {F : (ι → 𝔸[k]) → ℂ} (hF : F ∈ schwartzBruhatPi k ι)
    {ξ : ι → k} (hξ : ξ ≠ 0) : (fun t : 𝔸[k] ↦ F (t • ratV ξ)) ∈ schwartzBruhat k := by
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.1 hξ
  set M : Matrix ι ι k := (1 : Matrix ι ι k).updateCol i₀ ξ with hM
  have hdet : M.det ≠ 0 := by
    have : M.det = ξ i₀ := by
      rw [hM, ← Matrix.cramer_apply, Matrix.cramer_one]
      rfl
    rw [this]
    exact hi₀
  set A : GL ι 𝔸[k] := Matrix.GeneralLinearGroup.map (algebraMap k 𝔸[k])
    (Matrix.GeneralLinearGroup.mkOfDetNeZero M hdet) with hA
  have key : ∀ t : 𝔸[k], (A : Matrix ι ι 𝔸[k]) *ᵥ Pi.single i₀ t = t • ratV ξ := by
    intro t
    funext i
    have hAi : (A : Matrix ι ι 𝔸[k]) i i₀ = algebraMap k 𝔸[k] (ξ i) := by
      simp [hA, Matrix.GeneralLinearGroup.mkOfDetNeZero, hM, Matrix.updateCol_self]
    simp [Matrix.mulVec_single, hAi, ratV, mul_comm]
  have h := single_mem_schwartzBruhat (GlobalTheory.T.linearChange_mem_schwartzBruhatPi hF A) i₀
  simpa only [ltr, key] using h

end SlopeTestRemainingChoices

section Unfold

variable {k : Type} [Field k] [NumberField k] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem scalC_mulVec (a : IdeleGroup k) (v : ι → 𝔸[k]) :
    ((scalC a : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k]) *ᵥ v = (a : 𝔸[k]) • v := by
  funext i
  simp [scalC, Matrix.scalar_apply, Matrix.mulVec_diagonal]

theorem ratV_smul (d : k) (ξ : ι → k) : ratV (d • ξ) = algebraMap k 𝔸[k] d • ratV ξ := by
  funext i
  simp [ratV]

theorem ratV_zero : ratV (0 : ι → k) = 0 := by
  funext i
  simp [ratV]

theorem scalC_mul (a b : IdeleGroup k) : (scalC (a * b) : GL ι 𝔸[k]) = scalC a * scalC b :=
  map_mul (Units.map (Matrix.scalar ι : 𝔸[k] →+* Matrix ι ι 𝔸[k]).toMonoidHom) a b

theorem continuous_scalC : Continuous (scalC : IdeleGroup k → GL ι 𝔸[k]) := by
  refine Continuous.units_map _ ?_
  show Continuous fun a : 𝔸[k] ↦ Matrix.scalar ι a
  simp only [Matrix.scalar_apply]
  exact Continuous.matrix_diagonal (X := 𝔸[k]) (n := ι) (A := fun a _ ↦ a) (continuous_pi fun _ ↦ continuous_id)

noncomputable def lineMap (p : kˣ × Projectivization k (ι → k)) : {ξ : ι → k // ξ ≠ 0} :=
  ⟨(p.1 : k) • p.2.rep, smul_ne_zero p.1.ne_zero p.2.rep_nonzero⟩

theorem lineMap_injective : Function.Injective (lineMap (k := k) (ι := ι)) := by
  rintro ⟨d, l⟩ ⟨d', l'⟩ h
  have h' : (d : k) • l.rep = (d' : k) • l'.rep := congrArg Subtype.val h
  have hl : l = l' := by
    rw [← l.mk_rep, ← l'.mk_rep, Projectivization.mk_eq_mk_iff']
    refine ⟨(d : k)⁻¹ * d', ?_⟩
    rw [mul_smul, ← h', smul_smul, inv_mul_cancel₀ d.ne_zero, one_smul]
  subst hl
  have hd : d = d' := by
    obtain ⟨j, hj⟩ := Function.ne_iff.1 l.rep_nonzero
    have := congrFun h' j
    simp only [Pi.smul_apply, smul_eq_mul] at this
    exact Units.ext (mul_right_cancel₀ hj this)
  rw [hd]

theorem lineMap_surjective : Function.Surjective (lineMap (k := k) (ι := ι)) := by
  rintro ⟨ξ, hξ⟩
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep k ξ hξ
  refine ⟨(a⁻¹, Projectivization.mk k ξ hξ), Subtype.ext ?_⟩
  show ((a⁻¹ : kˣ) : k) • (Projectivization.mk k ξ hξ).rep = ξ
  rw [← ha, Units.smul_def, smul_smul, Units.inv_mul, one_smul]

noncomputable def lineEquiv : kˣ × Projectivization k (ι → k) ≃ {ξ : ι → k // ξ ≠ 0} :=
  Equiv.ofBijective lineMap ⟨lineMap_injective, lineMap_surjective⟩

theorem countable_proj : Countable (Projectivization k (ι → k)) := by
  haveI : Countable k := countable_numberField k
  exact ((lineEquiv (k := k) (ι := ι)).injective.comp (Prod.mk_right_injective (1 : kˣ))).countable

theorem summable_norm_col {F : (ι → 𝔸[k]) → ℂ} (hF : F ∈ schwartzBruhatPi k ι)
    (h : GL ι 𝔸[k]) :
    Summable fun ξ : ι → k ↦ ‖F ((h : Matrix ι ι 𝔸[k]) *ᵥ ratV ξ)‖ := by
  obtain ⟨u, hu, hb⟩ := GlobalTheory.T.exists_summable_majorant_lattice_sum hF (isCompact_singleton (x := h))
  exact Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun ξ ↦ hb h rfl ξ) hu

theorem summable_line {F : (ι → 𝔸[k]) → ℂ} (hF : F ∈ schwartzBruhatPi k ι) (h : GL ι 𝔸[k]) :
    Summable fun p : kˣ × Projectivization k (ι → k) ↦
      ‖F ((h : Matrix ι ι 𝔸[k]) *ᵥ ratV (lineEquiv p).1)‖ :=
  (lineEquiv (k := k) (ι := ι)).summable_iff.2 ((summable_norm_col hF h).subtype {ξ | ξ ≠ 0})

theorem tsum_finset_le {F : (ι → 𝔸[k]) → ℂ} (hF : F ∈ schwartzBruhatPi k ι)
    (h : GL ι 𝔸[k]) (S : Finset (Projectivization k (ι → k))) :
    ∑' d : kˣ, ∑ l ∈ S, ‖F ((h : Matrix ι ι 𝔸[k]) *ᵥ ratV ((d : k) • l.rep))‖ ≤
      ∑' ξ : {ξ : ι → k // ξ ≠ 0}, ‖F ((h : Matrix ι ι 𝔸[k]) *ᵥ ratV ξ.1)‖ := by
  have hf := summable_line hF h
  have h1 : ∑' ξ : {ξ : ι → k // ξ ≠ 0}, ‖F ((h : Matrix ι ι 𝔸[k]) *ᵥ ratV ξ.1)‖ =
      ∑' p : kˣ × Projectivization k (ι → k),
        ‖F ((h : Matrix ι ι 𝔸[k]) *ᵥ ratV (lineEquiv p).1)‖ :=
    ((lineEquiv (k := k) (ι := ι)).tsum_eq
      fun ξ ↦ ‖F ((h : Matrix ι ι 𝔸[k]) *ᵥ ratV ξ.1)‖).symm
  rw [h1, hf.tsum_prod]
  refine Summable.tsum_le_tsum (fun d ↦ ?_) ?_ hf.prod
  · exact (hf.prod_factor d).sum_le_tsum S fun c _ ↦ norm_nonneg _
  · refine summable_sum fun c _ ↦ ?_
    exact hf.comp_injective (i := fun d : kˣ ↦ (d, c)) fun a b hab ↦ (Prod.mk.inj hab).1

theorem thetaC_sub_eq {F : (ι → 𝔸[k]) → ℂ} (hF : F ∈ schwartzBruhatPi k ι) (h : GL ι 𝔸[k]) :
    thetaC F h - F 0 = ∑' ξ : {ξ : ι → k // ξ ≠ 0}, F ((h : Matrix ι ι 𝔸[k]) *ᵥ ratV ξ.1) := by
  classical
  have hs : Summable fun ξ : ι → k ↦ F ((h : Matrix ι ι 𝔸[k]) *ᵥ ratV ξ) :=
    (summable_norm_col hF h).of_norm
  have h3 := hs.tsum_eq_add_tsum_ite 0
  have h4 : ∑' ξ : {ξ : ι → k // ξ ≠ 0}, F ((h : Matrix ι ι 𝔸[k]) *ᵥ ratV ξ.1) =
      ∑' ξ : ι → k, if ξ = 0 then 0 else F ((h : Matrix ι ι 𝔸[k]) *ᵥ ratV ξ) := by
    have := tsum_subtype {ξ : ι → k | ξ ≠ 0} (fun ξ ↦ F ((h : Matrix ι ι 𝔸[k]) *ᵥ ratV ξ))
    refine this.trans (tsum_congr fun ξ ↦ ?_)
    by_cases hξ : ξ = 0 <;> simp [Set.indicator, hξ]
  rw [h4, thetaC, h3, ratV_zero, Matrix.mulVec_zero]
  ring

theorem tsum_tsum_eq {F : (ι → 𝔸[k]) → ℂ} (hF : F ∈ schwartzBruhatPi k ι) (h : GL ι 𝔸[k]) :
    ∑' d : kˣ, ∑' l : Projectivization k (ι → k),
        F ((h : Matrix ι ι 𝔸[k]) *ᵥ ratV ((d : k) • l.rep)) = thetaC F h - F 0 := by
  have hf : Summable fun p : kˣ × Projectivization k (ι → k) ↦
      F ((h : Matrix ι ι 𝔸[k]) *ᵥ ratV (lineEquiv p).1) := (summable_line hF h).of_norm
  rw [thetaC_sub_eq hF, ← (lineEquiv (k := k) (ι := ι)).tsum_eq
    fun ξ ↦ F ((h : Matrix ι ι 𝔸[k]) *ᵥ ratV ξ.1)]
  exact hf.tsum_prod.symm

noncomputable def Gc (F : (ι → 𝔸[k]) → ℂ) (ω : HeckeCharacter k) (z : ℂ)
    (l : Projectivization k (ι → k)) (x : IdeleGroup k) : ℂ :=
  F ((x : 𝔸[k]) • ratV l.rep) * (ω.toIdele x : ℂ) * ((ideleModule k x : ℝ) : ℂ) ^ z

theorem integrable_Gc {F : (ι → 𝔸[k]) → ℂ} (hF : F ∈ schwartzBruhatPi k ι)
    (ω : HeckeCharacter k) {z : ℂ} (hz : 1 < z.re) (l : Projectivization k (ι → k)) :
    Integrable (Gc F ω z l) (ideleMeasure k) :=
  integrable_globalZetaIntegrand (line_mem_schwartzBruhat hF l.rep_nonzero) ω hz

theorem continuous_Gc {F : (ι → 𝔸[k]) → ℂ} (hF : F ∈ schwartzBruhatPi k ι)
    (ω : HeckeCharacter k) (z : ℂ) (l : Projectivization k (ι → k)) : Continuous (Gc F ω z l) :=
  continuous_zetaIntegrand
    (continuous_of_mem_schwartzBruhat (line_mem_schwartzBruhat hF l.rep_nonzero)) ω z

theorem Gc_diagonal_mul (F : (ι → 𝔸[k]) → ℂ) (ω : HeckeCharacter k) (z : ℂ)
    (l : Projectivization k (ι → k)) (d : kˣ) (x : IdeleGroup k) :
    Gc F ω z l (diagonal k d * x) =
      F (((scalC x : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k]) *ᵥ ratV ((d : k) • l.rep)) *
        ((ω.toIdele x : ℂ) * ((ideleModule k x : ℝ) : ℂ) ^ z) := by
  have e : ((diagonal k d * x : IdeleGroup k) : 𝔸[k]) • ratV l.rep =
      ((scalC x : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k]) *ᵥ ratV ((d : k) • l.rep) := by
    rw [scalC_mulVec, ratV_smul, Units.val_mul, coe_diagonal, smul_smul, mul_comm]
  rw [Gc, e, map_mul, HeckeCharacter.toIdele_diagonal, map_mul, ideleModule_diagonal, one_mul,
    one_mul, mul_assoc]

theorem norm_Gc_diagonal_mul (F : (ι → 𝔸[k]) → ℂ) (ω : HeckeCharacter k) (z : ℂ)
    (l : Projectivization k (ι → k)) (d : kˣ) (x : IdeleGroup k) :
    ‖Gc F ω z l (diagonal k d * x)‖ =
      ‖F (((scalC x : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k]) *ᵥ ratV ((d : k) • l.rep))‖ *
        (ideleModule k x : ℝ) ^ z.re := by
  rw [Gc_diagonal_mul, norm_mul, norm_mul, Circle.norm_coe, one_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos (ideleModule k x).2]

theorem exists_bound (w : InfinitePlace k) {F : (ι → 𝔸[k]) → ℂ}
    (hF : F ∈ schwartzBruhatPi k ι) (r : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t : {x : ℝ // 0 < x}, ∀ u ∈ normOneFundamentalDomain k,
      (1 ≤ (t : ℝ) → ∑' ξ : {ξ : ι → k // ξ ≠ 0},
        ‖F (((scalC (moduleSection w t * (u : IdeleGroup k)) : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k]) *ᵥ
          ratV ξ.1)‖ ≤ ((t : ℝ) ^ r)⁻¹ * M) ∧
      ((t : ℝ) ≤ 1 → ∑' ξ : {ξ : ι → k // ξ ≠ 0},
        ‖F (((scalC (moduleSection w t * (u : IdeleGroup k)) : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k]) *ᵥ
          ratV ξ.1)‖ ≤ ((t : ℝ) ^ Fintype.card ι)⁻¹ * M) := by
  obtain ⟨G, hG, ρ, hGρ, hFρ⟩ := exists_schwartzBruhatPi_majorant hF
  have hρ0 : ∀ x, 0 ≤ ρ x := fun x ↦ (norm_nonneg _).trans (hFρ x)
  have hnorm : ∀ x, ‖G x‖ = ρ x := fun x ↦ by
    rw [hGρ, Complex.norm_real, Real.norm_of_nonneg (hρ0 x)]
  have hφ : Continuous fun u : normOneSubgroup k ↦ (scalC (u : IdeleGroup k) : GL ι 𝔸[k]) :=
    continuous_scalC.comp continuous_subtype_val
  have hφ' : Continuous fun u : normOneSubgroup k ↦ (scalC (u : IdeleGroup k)⁻¹ : GL ι 𝔸[k]) :=
    continuous_scalC.comp (continuous_inv.comp continuous_subtype_val)
  have hE := isCompact_closure_normOneFundamentalDomain k
  obtain ⟨M₁, h₁⟩ := GlobalTheory.T.theta_sub_value_zero_rapid_decay w hG (hE.image hφ) r
  obtain ⟨M₀, h₀⟩ := GlobalTheory.T.theta_sub_value_zero_rapid_decay w (adelicFourierPi_mem_schwartzBruhatPi hG) (hE.image hφ') 0
  set N := Fintype.card ι with hN

  have hsr : ∀ h : GL ι 𝔸[k], Summable fun ξ : ι → k ↦ ρ ((h : Matrix ι ι 𝔸[k]) *ᵥ ratV ξ) := by
    intro h
    simpa only [hnorm] using summable_norm_col hG h
  have hsF : ∀ h : GL ι 𝔸[k], ∑' ξ : {ξ : ι → k // ξ ≠ 0}, ‖F ((h : Matrix ι ι 𝔸[k]) *ᵥ ratV ξ.1)‖ ≤
      ∑' ξ : {ξ : ι → k // ξ ≠ 0}, ρ ((h : Matrix ι ι 𝔸[k]) *ᵥ ratV ξ.1) := fun h ↦
    ((summable_norm_col hF h).subtype _).tsum_le_tsum (fun ξ ↦ hFρ _) ((hsr h).subtype _)
  have htail : ∀ h : GL ι 𝔸[k], ∑' ξ : {ξ : ι → k // ξ ≠ 0}, ρ ((h : Matrix ι ι 𝔸[k]) *ᵥ ratV ξ.1) =
      ‖thetaC G h - G 0‖ := by
    intro h
    rw [thetaC_sub_eq hG]
    simp only [hGρ]
    rw [← Complex.ofReal_tsum, Complex.norm_real,
      Real.norm_of_nonneg (tsum_nonneg fun _ ↦ hρ0 _)]
  have hall : ∀ h : GL ι 𝔸[k], ∑' ξ : {ξ : ι → k // ξ ≠ 0}, ρ ((h : Matrix ι ι 𝔸[k]) *ᵥ ratV ξ.1) ≤
      ‖thetaC G h‖ := by
    intro h
    have h1 := Summable.tsum_subtype_le (fun ξ : ι → k ↦ ρ ((h : Matrix ι ι 𝔸[k]) *ᵥ ratV ξ))
      {ξ | ξ ≠ 0} (fun ξ ↦ hρ0 _) (hsr h)
    refine h1.trans (le_of_eq ?_)
    rw [thetaC]
    simp only [hGρ]
    rw [← Complex.ofReal_tsum, Complex.norm_real,
      Real.norm_of_nonneg (tsum_nonneg fun _ ↦ hρ0 _)]
  refine ⟨max (max M₁ (‖adelicFourierPi k G 0‖ + M₀)) 0, le_max_right _ _, fun t u hu ↦
    ⟨fun ht ↦ ?_, fun ht ↦ ?_⟩⟩
  · have hm : u ∈ closure (normOneFundamentalDomain k) := subset_closure hu
    have h2 := h₁ _ (Set.mem_image_of_mem _ hm) t ht
    rw [← scalC_mul] at h2
    refine (hsF _).trans ?_
    rw [htail]
    refine h2.trans (mul_le_mul_of_nonneg_left ?_ (by have := t.2; positivity))
    exact (le_max_left _ _).trans (le_max_left _ _)
  · have hm : u ∈ closure (normOneFundamentalDomain k) := subset_closure hu
    have ht0 : (0 : ℝ) < t := t.2
    have hT : (1 : ℝ) ≤ ((t⁻¹ : {x : ℝ // 0 < x}) : ℝ) := (one_le_inv₀ t.2).2 ht
    have h2 := h₀ _ (Set.mem_image_of_mem _ hm) t⁻¹ hT
    rw [pow_zero, inv_one, one_mul, map_inv, ← scalC_mul, ← mul_inv] at h2
    have hθ : ‖thetaC (adelicFourierPi k G)
        (scalC (moduleSection w t * (u : IdeleGroup k))⁻¹ : GL ι 𝔸[k])‖ ≤
        ‖adelicFourierPi k G 0‖ + M₀ := by
      have := norm_sub_norm_le
        (thetaC (adelicFourierPi k G)
          (scalC (moduleSection w t * (u : IdeleGroup k))⁻¹ : GL ι 𝔸[k]))
        (adelicFourierPi k G 0)
      linarith
    have hmod : (ideleModule k (moduleSection w t * (u : IdeleGroup k)) : ℝ) = t := by
      have hu1 : ideleModule k (u : IdeleGroup k) = 1 := u.2
      rw [map_mul, ideleModule_moduleSection, hu1, mul_one]
    refine ((hsF _).trans (hall _)).trans ?_
    rw [GlobalTheory.CompanionTheory.EpsteinRankN.Hd.thetaC_scalC_eq hG, hmod, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    refine mul_le_mul_of_nonneg_left (hθ.trans ?_) (by positivity)
    exact (le_max_right _ _).trans (le_max_left _ _)

theorem integrable_exp_neg_abs_log {δ : ℝ} (hδ : 0 < δ) :
    Integrable (fun t : {x : ℝ // 0 < x} ↦ Real.exp (-(δ * |Real.log t|))) posRealMeasure := by
  have hc : Continuous fun t : {x : ℝ // 0 < x} ↦ Real.exp (-(δ * |Real.log t|)) := by
    have : Continuous fun t : {x : ℝ // 0 < x} ↦ Real.log t :=
      continuous_subtype_val.log fun r ↦ r.2.ne'
    fun_prop
  rw [posRealMeasure_eq_map_expPos,
    integrable_map_measure hc.aestronglyMeasurable measurable_expPos.aemeasurable]
  have h1 : IntegrableOn (fun s : ℝ ↦ Real.exp (-(δ * |s|))) (Set.Ioi 0) := by
    refine (exp_neg_integrableOn_Ioi 0 hδ).congr_fun (fun s hs ↦ ?_) measurableSet_Ioi
    have : |s| = s := abs_of_pos hs
    simp [this]
  have h2 : IntegrableOn (fun s : ℝ ↦ Real.exp (-(δ * |s|))) (Set.Iic 0) := by
    refine (integrableOn_exp_mul_Iic hδ 0).congr_fun (fun s hs ↦ ?_) measurableSet_Iic
    have : |s| = -s := abs_of_nonpos hs
    simp [this]
  have h3 := h2.union h1
  rw [Set.Iic_union_Ioi, integrableOn_univ] at h3
  refine h3.congr (ae_of_all _ fun x ↦ ?_)
  have hlog : Real.log ((expPos x : {x : ℝ // 0 < x}) : ℝ) = x := Real.log_exp x
  simp only [Function.comp_apply, hlog]

theorem pow_bound {σ δ : ℝ} {r n : ℕ} (hδ1 : δ ≤ 1) (hδ2 : δ ≤ σ - n) (hδ : 0 < δ)
    (hr : σ + 1 ≤ r) {t : ℝ} (ht : 0 < t) :
    (1 ≤ t → (t ^ r)⁻¹ * t ^ σ ≤ Real.exp (-(δ * |Real.log t|))) ∧
    (t ≤ 1 → (t ^ n)⁻¹ * t ^ σ ≤ Real.exp (-(δ * |Real.log t|))) := by
  constructor
  · intro h1
    have hL : 0 ≤ Real.log t := Real.log_nonneg h1
    rw [← Real.rpow_natCast, ← Real.rpow_neg ht.le, ← Real.rpow_add ht, Real.rpow_def_of_pos ht,
      Real.exp_le_exp, abs_of_nonneg hL]
    nlinarith
  · intro h1
    have hL : Real.log t ≤ 0 := Real.log_nonpos ht.le h1
    rw [← Real.rpow_natCast, ← Real.rpow_neg ht.le, ← Real.rpow_add ht, Real.rpow_def_of_pos ht,
      Real.exp_le_exp, abs_of_nonpos hL]
    nlinarith

theorem sum_integral_norm_le (w : InfinitePlace k) {F : (ι → 𝔸[k]) → ℂ}
    (hF : F ∈ schwartzBruhatPi k ι) (ω : HeckeCharacter k) {z : ℂ} (hz : (Fintype.card ι : ℝ) < z.re)
    (hz1 : 1 < z.re) :
    ∃ B : ℝ, ∀ S : Finset (Projectivization k (ι → k)),
      ∑ l ∈ S, ∫ x, ‖Gc F ω z l x‖ ∂ideleMeasure k ≤ B := by
  obtain ⟨r, hr⟩ := exists_nat_ge (z.re + 1)
  set δ : ℝ := min (z.re - Fintype.card ι) 1 with hδdef
  have hδ : 0 < δ := lt_min (by linarith) one_pos
  have hδ1 : δ ≤ 1 := min_le_right _ _
  have hδ2 : δ ≤ z.re - Fintype.card ι := min_le_left _ _
  obtain ⟨M, hM0, hM⟩ := exists_bound w hF r
  set E := normOneFundamentalDomain k with hE
  haveI : IsFiniteMeasure ((normOneMeasure k).restrict E) :=
    ⟨by simpa using normOneMeasure_normOneFundamentalDomain_lt_top k⟩
  set V : ℝ := ((normOneMeasure k).restrict E).real Set.univ with hV
  set ρ : {x : ℝ // 0 < x} → ℝ := fun t ↦ M * Real.exp (-(δ * |Real.log t|)) with hρ
  have hρi : Integrable (fun t ↦ V • ρ t) posRealMeasure :=
    ((integrable_exp_neg_abs_log hδ).const_mul M).smul V
  refine ⟨∫ t, V • ρ t ∂posRealMeasure, fun S ↦ ?_⟩
  set ψ : IdeleGroup k → ℝ := fun x ↦ ∑ l ∈ S, ‖Gc F ω z l x‖ with hψdef
  have hψ : Integrable ψ (ideleMeasure k) :=
    integrable_finset_sum _ fun c _ ↦ (integrable_Gc hF ω hz1 c).norm
  have h1 : ∑ l ∈ S, ∫ x, ‖Gc F ω z l x‖ ∂ideleMeasure k = ∫ x, ψ x ∂ideleMeasure k :=
    (integral_finset_sum _ fun c _ ↦ (integrable_Gc hF ω hz1 c).norm).symm
  have hnn : ∀ x, 0 ≤ ψ x := fun x ↦ Finset.sum_nonneg fun c _ ↦ norm_nonneg _
  rw [h1, integral_ideleMeasure_eq_integral_fundamentalDomain w hψ]
  refine integral_mono_of_nonneg (ae_of_all _ fun t ↦ ?_) hρi (ae_of_all _ fun t ↦ ?_)
  · exact integral_nonneg fun u ↦ tsum_nonneg fun d ↦ hnn _
  · have hpt : ∀ u ∈ E, ∑' ξ : kˣ, ψ (diagonal k ξ * moduleSection w t * (u : IdeleGroup k)) ≤ ρ t := by
      intro u hu
      set x : IdeleGroup k := moduleSection w t * (u : IdeleGroup k) with hx
      have hmod : (ideleModule k x : ℝ) = t := by
        have hu1 : ideleModule k (u : IdeleGroup k) = 1 := u.2
        rw [hx, map_mul, ideleModule_moduleSection, hu1, mul_one]
      have h2 : ∀ ξ : kˣ, ψ (diagonal k ξ * moduleSection w t * (u : IdeleGroup k)) =
          (∑ l ∈ S, ‖F (((scalC x : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k]) *ᵥ ratV ((ξ : k) • l.rep))‖) *
            (t : ℝ) ^ z.re := by
        intro ξ
        have e : diagonal k ξ * moduleSection w t * (u : IdeleGroup k) = diagonal k ξ * x :=
          mul_assoc _ _ _
        rw [e]
        show ∑ l ∈ S, ‖Gc F ω z l (diagonal k ξ * x)‖ = _
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun c _ ↦ ?_
        rw [norm_Gc_diagonal_mul, hmod]
      simp only [h2]
      rw [tsum_mul_right]
      have ht0 : 0 < (t : ℝ) := t.2
      have hp : 0 ≤ (t : ℝ) ^ z.re := Real.rpow_nonneg ht0.le _
      have h3 := tsum_finset_le hF (scalC x) S
      obtain ⟨hb1, hb2⟩ := hM t u hu
      obtain ⟨hc1, hc2⟩ := pow_bound hδ1 hδ2 hδ hr ht0
      rcases le_total 1 (t : ℝ) with h | h
      · calc _ ≤ (((t : ℝ) ^ r)⁻¹ * M) * (t : ℝ) ^ z.re :=
              mul_le_mul_of_nonneg_right (h3.trans (hb1 h)) hp
          _ = M * (((t : ℝ) ^ r)⁻¹ * (t : ℝ) ^ z.re) := by ring
          _ ≤ ρ t := mul_le_mul_of_nonneg_left (hc1 h) hM0
      · calc _ ≤ (((t : ℝ) ^ Fintype.card ι)⁻¹ * M) * (t : ℝ) ^ z.re :=
              mul_le_mul_of_nonneg_right (h3.trans (hb2 h)) hp
          _ = M * (((t : ℝ) ^ Fintype.card ι)⁻¹ * (t : ℝ) ^ z.re) := by ring
          _ ≤ ρ t := mul_le_mul_of_nonneg_left (hc2 h) hM0
    have h4 := integral_mono_of_nonneg (μ := (normOneMeasure k).restrict E)
      (f := fun u : normOneSubgroup k ↦
        ∑' ξ : kˣ, ψ (diagonal k ξ * moduleSection w t * (u : IdeleGroup k)))
      (g := fun _ ↦ ρ t) (ae_of_all _ fun u ↦ tsum_nonneg fun d ↦ hnn _) (integrable_const _)
      ((ae_restrict_iff' (measurableSet_normOneFundamentalDomain k)).2 (ae_of_all _ hpt))
    simpa [hV] using h4

theorem summable_integral_norm_Gc (w : InfinitePlace k) {F : (ι → 𝔸[k]) → ℂ}
    (hF : F ∈ schwartzBruhatPi k ι) (ω : HeckeCharacter k) {z : ℂ}
    (hz : (Fintype.card ι : ℝ) < z.re) (hz1 : 1 < z.re) :
    Summable fun l : Projectivization k (ι → k) ↦ ∫ x, ‖Gc F ω z l x‖ ∂ideleMeasure k := by
  obtain ⟨B, hB⟩ := sum_integral_norm_le w hF ω hz hz1
  exact summable_of_sum_le (fun c ↦ integral_nonneg fun x ↦ norm_nonneg _) hB

theorem integrable_tsum_Gc (w : InfinitePlace k) {F : (ι → 𝔸[k]) → ℂ}
    (hF : F ∈ schwartzBruhatPi k ι) (ω : HeckeCharacter k) {z : ℂ}
    (hz : (Fintype.card ι : ℝ) < z.re) (hz1 : 1 < z.re) :
    Integrable (fun x ↦ ∑' l : Projectivization k (ι → k), Gc F ω z l x) (ideleMeasure k) := by
  haveI := countable_proj (k := k) (ι := ι)
  have hs := summable_integral_norm_Gc w hF ω hz hz1
  have hint := integrable_Gc hF ω hz1
  have hmeas : ∀ c, AEMeasurable (fun x ↦ ‖Gc F ω z c x‖ₑ) (ideleMeasure k) := fun c ↦
    (hint c).aemeasurable.enorm
  have hlin : ∫⁻ x, ∑' c, ‖Gc F ω z c x‖ₑ ∂ideleMeasure k ≠ ⊤ := by
    rw [lintegral_tsum hmeas]
    have : ∀ c, ∫⁻ x, ‖Gc F ω z c x‖ₑ ∂ideleMeasure k =
        ENNReal.ofReal (∫ x, ‖Gc F ω z c x‖ ∂ideleMeasure k) := fun c ↦
      (ofReal_integral_norm_eq_lintegral_enorm (hint c)).symm
    simp_rw [this]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun c ↦ integral_nonneg fun _ ↦ norm_nonneg _) hs]
    exact ENNReal.ofReal_ne_top
  refine ⟨(Measurable.tsum fun c ↦ (continuous_Gc hF ω z c).measurable).aestronglyMeasurable, ?_⟩
  exact lt_of_le_of_lt (lintegral_mono fun x ↦ enorm_tsum_le_tsum_enorm)
    (lt_top_iff_ne_top.2 hlin)

theorem integrableOn_thetaC_mul {F : (ι → 𝔸[k]) → ℂ} (hF : F ∈ schwartzBruhatPi k ι)
    (ω : HeckeCharacter k) (a : IdeleGroup k) :
    IntegrableOn (fun u : normOneSubgroup k ↦
      thetaC F (scalC (a * (u : IdeleGroup k))) * (ω.toIdele (u : IdeleGroup k) : ℂ))
      (normOneFundamentalDomain k) (normOneMeasure k) := by
  have hE := isCompact_closure_normOneFundamentalDomain k
  have hφ : Continuous fun u : normOneSubgroup k ↦
      (scalC (a * (u : IdeleGroup k)) : GL ι 𝔸[k]) :=
    continuous_scalC.comp (continuous_const.mul continuous_subtype_val)
  have hθ : ContinuousOn (thetaC F) ((fun u : normOneSubgroup k ↦
      (scalC (a * (u : IdeleGroup k)) : GL ι 𝔸[k])) '' closure (normOneFundamentalDomain k)) := by
    obtain ⟨v, hv, hb⟩ := GlobalTheory.T.exists_summable_majorant_lattice_sum hF (hE.image hφ)
    refine continuousOn_tsum (fun ξ ↦ Continuous.continuousOn ?_) hv fun ξ h hh ↦ hb h hh ξ
    refine (continuous_of_mem_schwartzBruhatPi hF).comp ?_
    exact Units.continuous_val.matrix_mulVec continuous_const
  have h1 : ContinuousOn (fun u : normOneSubgroup k ↦ thetaC F (scalC (a * (u : IdeleGroup k))))
      (closure (normOneFundamentalDomain k)) :=
    hθ.comp hφ.continuousOn (Set.mapsTo_image _ _)
  have h2 : Continuous fun u : normOneSubgroup k ↦ (ω.toIdele (u : IdeleGroup k) : ℂ) :=
    continuous_subtype_val.comp (ω.continuous_toIdele.comp continuous_subtype_val)
  exact ((h1.mul h2.continuousOn).integrableOn_compact hE).mono_set subset_closure

theorem integrableOn_char (ω : HeckeCharacter k) :
    IntegrableOn (fun u : normOneSubgroup k ↦ (ω.toIdele (u : IdeleGroup k) : ℂ))
      (normOneFundamentalDomain k) (normOneMeasure k) := by
  have hE := isCompact_closure_normOneFundamentalDomain k
  have h2 : Continuous fun u : normOneSubgroup k ↦ (ω.toIdele (u : IdeleGroup k) : ℂ) :=
    continuous_subtype_val.comp (ω.continuous_toIdele.comp continuous_subtype_val)
  exact (h2.continuousOn.integrableOn_compact hE).mono_set subset_closure

theorem inner_eq (w : InfinitePlace k) {F : (ι → 𝔸[k]) → ℂ}
    (hF : F ∈ schwartzBruhatPi k ι) (ω : HeckeCharacter k) (z : ℂ) (t : {r : ℝ // 0 < r}) :
    ∫ u in normOneFundamentalDomain k, ∑' ξ : kˣ, ∑' l : Projectivization k (ι → k),
        Gc F ω z l (diagonal k ξ * moduleSection w t * (u : IdeleGroup k)) ∂normOneMeasure k =
      (thetaCFun w F ω (t : ℝ) - thetaCConst F ω) *
        (((t : ℝ) : ℂ) ^ (z + (archExponent w ω : ℂ) * Complex.I)) := by
  have ht : ((t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 t.2.ne'
  have hpt : ∀ u : normOneSubgroup k, ∑' ξ : kˣ, ∑' l : Projectivization k (ι → k),
      Gc F ω z l (diagonal k ξ * moduleSection w t * (u : IdeleGroup k)) =
      (((t : ℝ) : ℂ) ^ (z + (archExponent w ω : ℂ) * Complex.I)) *
        (thetaC F (scalC (moduleSection w t * (u : IdeleGroup k))) *
            (ω.toIdele (u : IdeleGroup k) : ℂ) - F 0 * (ω.toIdele (u : IdeleGroup k) : ℂ)) := by
    intro u
    set x : IdeleGroup k := moduleSection w t * (u : IdeleGroup k) with hx
    have hmod : (ideleModule k x : ℝ) = t := by
      have hu1 : ideleModule k (u : IdeleGroup k) = 1 := u.2
      rw [hx, map_mul, ideleModule_moduleSection, hu1, mul_one]
    have e : ∀ ξ : kˣ, diagonal k ξ * moduleSection w t * (u : IdeleGroup k) = diagonal k ξ * x :=
      fun ξ ↦ mul_assoc _ _ _
    simp only [e, Gc_diagonal_mul]
    simp only [tsum_mul_right]
    rw [tsum_tsum_eq hF, hmod, hx, map_mul, Circle.coe_mul, archExponent_spec,
      Complex.cpow_add _ _ ht]
    ring
  simp only [hpt]
  rw [integral_const_mul, integral_sub (integrableOn_thetaC_mul hF ω _)
    ((integrableOn_char ω).const_mul _), integral_const_mul, thetaCFun, dif_pos t.2]
  simp only [thetaCInt, thetaCConst, volChar]
  ring

theorem integral_tsum_Gc_eq (w : InfinitePlace k) {F : (ι → 𝔸[k]) → ℂ}
    (hF : F ∈ schwartzBruhatPi k ι) (ω : HeckeCharacter k) {z : ℂ}
    (hz : (Fintype.card ι : ℝ) < z.re) (hz1 : 1 < z.re) :
    ∫ x, ∑' l : Projectivization k (ι → k), Gc F ω z l x ∂ideleMeasure k =
      mellin (fun x ↦ thetaCFun w F ω x - thetaCConst F ω)
        (z + (archExponent w ω : ℂ) * Complex.I) := by
  set y := z + (archExponent w ω : ℂ) * Complex.I with hy
  set g : ℝ → ℂ := fun x ↦ (thetaCFun w F ω x - thetaCConst F ω) * (x : ℂ) ^ y with hg
  rw [integral_ideleMeasure_eq_integral_fundamentalDomain w (integrable_tsum_Gc w hF ω hz hz1)]
  have h : (fun t : {r : ℝ // 0 < r} ↦ ∫ u in normOneFundamentalDomain k, ∑' ξ : kˣ,
        ∑' l : Projectivization k (ι → k),
        Gc F ω z l (diagonal k ξ * moduleSection w t * (u : IdeleGroup k)) ∂normOneMeasure k) =
      fun t : {r : ℝ // 0 < r} ↦ g (t : ℝ) := by
    funext t
    exact inner_eq w hF ω z t
  rw [h, integral_posRealMeasure g, mellin]
  refine setIntegral_congr_fun measurableSet_Ioi fun x hx ↦ ?_
  have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (ne_of_gt hx)
  simp only [hg, Complex.real_smul, smul_eq_mul]
  rw [Complex.cpow_sub _ _ hx0, Complex.cpow_one, Complex.ofReal_inv, div_eq_mul_inv]
  ring

theorem lines_eq_mellin (w : InfinitePlace k) (ω : HeckeCharacter k) {F : (ι → 𝔸[k]) → ℂ}
    (hF : F ∈ schwartzBruhatPi k ι) {z : ℂ} (hz : (Fintype.card ι : ℝ) < z.re) (hz1 : 1 < z.re) :
    Summable (fun l : Projectivization k (ι → k) ↦ ‖lineZeta F ω z (ratV l.rep)‖) ∧
      ∑' l : Projectivization k (ι → k), lineZeta F ω z (ratV l.rep) =
        mellin (fun x ↦ thetaCFun w F ω x - thetaCConst F ω)
          (z + (archExponent w ω : ℂ) * Complex.I) := by
  haveI := countable_proj (k := k) (ι := ι)
  have hsum := summable_integral_norm_Gc w hF ω hz hz1
  have hsec : ∀ l : Projectivization k (ι → k), lineZeta F ω z (ratV l.rep) =
      ∫ x, Gc F ω z l x ∂ideleMeasure k := fun l ↦ rfl
  refine ⟨Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun c ↦ ?_) hsum, ?_⟩
  · rw [hsec]
    exact norm_integral_le_integral_norm _
  · have hHS := hasSum_integral_of_summable_integral_norm
      (fun c ↦ integrable_Gc hF ω hz1 c) hsum
    simp only [hsec]
    rw [hHS.tsum_eq]
    exact integral_tsum_Gc_eq w hF ω hz hz1

theorem lineZeta_mulVec (Ψ : (ι → 𝔸[k]) → ℂ) (ω : HeckeCharacter k) (z : ℂ) (A : GL ι 𝔸[k])
    (v : ι → 𝔸[k]) :
    lineZeta Ψ ω z ((A : Matrix ι ι 𝔸[k]) *ᵥ v) = lineZeta (ltr A Ψ) ω z v := by
  simp only [lineZeta, ltr, Matrix.mulVec_smul]

theorem mellin_eq_zero_of_isEmpty [IsEmpty ι] (w : InfinitePlace k) (F : (ι → 𝔸[k]) → ℂ)
    (ω : HeckeCharacter k) (s : ℂ) :
    mellin (fun x ↦ thetaCFun w F ω x - thetaCConst F ω) s = 0 := by
  have hθ : ∀ h : GL ι 𝔸[k], thetaC F h = F 0 := by
    intro h
    rw [thetaC, tsum_eq_single (0 : ι → k) fun ξ hξ ↦ (hξ (Subsingleton.elim _ _)).elim]
    congr 1
    exact Subsingleton.elim _ _
  rw [mellin]
  have h0 : ∫ t in Set.Ioi (0 : ℝ), ((t : ℂ) ^ (s - 1)) •
      (thetaCFun w F ω t - thetaCConst F ω) = ∫ t in Set.Ioi (0 : ℝ), (0 : ℂ) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx ↦ ?_
    have hx' : (0 : ℝ) < x := hx
    simp only [thetaCFun, dif_pos hx', thetaCInt, hθ, thetaCConst, volChar]
    rw [integral_const_mul, sub_self, smul_zero]
  rw [h0]
  simp

end Unfold

theorem epstein_eq_mellin {k : Type} [Field k] [NumberField k] {ι : Type} [Fintype ι]
    [DecidableEq ι] (w : InfinitePlace k) (ω : HeckeCharacter k) {Ψ : (ι → 𝔸[k]) → ℂ}
    (hΨ : Ψ ∈ schwartzBruhatPi k ι) {z : ℂ} (hz : (Fintype.card ι : ℝ) < z.re)
    (m : GL ι 𝔸[k]) :
    Summable (fun l : Projectivization k (ι → k) ↦
        ‖lineZeta Ψ ω z (((m⁻¹ : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k]) *ᵥ ratV l.rep)‖) ∧
      epstein Ψ ω z m =
        mellin (fun x ↦ thetaCFun w (ltr m⁻¹ Ψ) ω x - thetaCConst (ltr m⁻¹ Ψ) ω)
          (z + (archExponent w ω : ℂ) * Complex.I) := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · haveI : IsEmpty (Projectivization k (ι → k)) :=
      ⟨fun l ↦ l.rep_nonzero (Subsingleton.elim _ _)⟩
    rw [mellin_eq_zero_of_isEmpty, epstein, tsum_empty]
    exact ⟨Summable.of_finite, rfl⟩
  · have hz1 : 1 < z.re := by
      have : (1 : ℝ) ≤ Fintype.card ι := by exact_mod_cast Fintype.card_pos
      linarith
    have h := lines_eq_mellin w ω (GlobalTheory.T.linearChange_mem_schwartzBruhatPi hΨ m⁻¹) hz hz1
    simp only [epstein, lineZeta_mulVec]
    exact h

end GlobalTheory.CompanionTheory.EpsteinUnfold.Hd
