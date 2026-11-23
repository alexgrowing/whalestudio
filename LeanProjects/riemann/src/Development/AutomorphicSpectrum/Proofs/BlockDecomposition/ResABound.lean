import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ResATranslate

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.ResMu

open Set GlobalTheory.Eis

variable {D : D7} {p : ℕ}

theorem resA_lim (hS : SphBound) (hp : 1 ≤ p) {H : G D p → ℝ≥0} (hH : IsHt H) {C : Set (G D p)} (hC : IsCompact C)
    (hcov : ∀ g, ∃ q ∈ P D p, ∃ c ∈ C, g = q * c) (f : ℝ → G D p → ℂ)
    (hc : ContinuousOn (fun u : ℝ × G D p => f u.1 u.2) (Icc ((p : ℝ) / 2) (p / 2 + 1) ×ˢ univ))
    (hl : ∀ σ ∈ Icc ((p : ℝ) / 2) (p / 2 + 1), IsLaw 1 (σ : ℂ) (f σ)) (a : ℂ)
    (ha : Tendsto (fun σ : ℝ => ((σ - p / 2 : ℝ) : ℂ) * eisS (f σ) 1) (𝓝[>] ((p : ℝ) / 2)) (𝓝 a)) :
    IsRho (f (p / 2)) ∧ a = resA H (f (p / 2)) 1 := by
  have hm : (p : ℝ) / 2 ∈ Icc ((p : ℝ) / 2) (p / 2 + 1) := ⟨le_rfl, by linarith⟩
  have hc0 : Continuous (f ((p : ℝ) / 2)) :=
      ContinuousOn.comp_continuous (f := fun g : G D p => (((p : ℝ) / 2, g) : ℝ × G D p)) hc
        (continuous_const.prodMk continuous_id) fun g => ⟨hm, mem_univ _⟩
  have h2 := hl _ hm
  have e : ((((p : ℝ) / 2 : ℝ)) : ℂ) = (p : ℂ) / 2 := by push_cast; ring
  rw [e] at h2
  have hf0 : IsRho (f (p / 2)) := And.intro hc0 h2
  refine ⟨hf0, ?_⟩
  have hc' : ContinuousOn (fun u : ℝ × G D p => fam H (f (p / 2)) ((p : ℂ) / 2) (u.1 : ℂ) u.2) (Icc ((p : ℝ) / 2) (p / 2 + 1) ×ˢ univ) :=
    (fam_cont hH hf0.1 _).continuousOn
  have h00 : f ((p : ℝ) / 2) = (fun σ : ℝ => fam H (f (p / 2)) ((p : ℂ) / 2) (σ : ℂ)) ((p : ℝ) / 2) := (fam_at H (f (p / 2))).symm
  have hd := tendsto_diff hS hp hH hC hcov (S := f) (S' := fun σ => fam H (f (p / 2)) ((p : ℂ) / 2) (σ : ℂ)) hc
    hc' hl (fun σ _ => fam_law_real hH hf0 σ) h00
  have h1 := (ha.sub hd).mono_left (ufil_le p)
  rw [sub_zero] at h1
  have h3 : Tendsto (fun σ => res H (f (p / 2)) σ 1) ((ufil p : Ultrafilter ℝ) : Filter ℝ) (𝓝 a) := by
    refine h1.congr fun σ => ?_
    simp only [res]
    ring
  exact tendsto_nhds_unique h3 (res_tendsto hS hp hH hC hcov hf0 1)

theorem rho_add {f f' : G D p → ℂ} (hf : IsRho f) (hf' : IsRho f') : IsRho (f + f') := by
  refine ⟨hf.1.add hf'.1, fun q hq a ha g => ?_⟩
  simp only [Pi.add_apply, hf.2 q hq a ha g, hf'.2 q hq a ha g]; ring

theorem rho_smul {f : G D p → ℂ} (hf : IsRho f) (c : ℂ) : IsRho (c • f) := by
  refine ⟨continuous_const.smul hf.1, fun q hq a ha g => ?_⟩
  simp only [Pi.smul_apply, smul_eq_mul, hf.2 q hq a ha g]; ring

theorem fam_add (H : G D p → ℝ≥0) (f f' : G D p → ℂ) (s z : ℂ) : fam H (f + f') s z = fam H f s z + fam H f' s z := by
  funext g; simp [fam, mul_add]

theorem fam_smul (H : G D p → ℝ≥0) (f : G D p → ℂ) (c s z : ℂ) : fam H (c • f) s z = c • fam H f s z := by
  funext g; simp only [fam, Pi.smul_apply, smul_eq_mul]; ring

theorem resA_add (hS : SphBound) (hp : 1 ≤ p) {H : G D p → ℝ≥0} (hH : IsHt H) {C : Set (G D p)} (hC : IsCompact C)
    (hcov : ∀ g, ∃ q ∈ P D p, ∃ c ∈ C, g = q * c) {f f' : G D p → ℂ} (hf : IsRho f) (hf' : IsRho f') (h : G D p) :
    resA H (f + f') h = resA H f h + resA H f' h := by
  refine tendsto_nhds_unique (res_tendsto hS hp hH hC hcov (rho_add hf hf') h) ?_
  refine ((res_tendsto hS hp hH hC hcov hf h).add (res_tendsto hS hp hH hC hcov hf' h)).congr' ?_
  refine ufil_le p ?_
  filter_upwards [ev_Ioc p] with σ hσ
  have c1 := conv_of_section hS hp hH hC hcov hσ (fam_cont_at hH hf.1 _ σ) (fam_law_real hH hf σ) h
  have c2 := conv_of_section hS hp hH hC hcov hσ (fam_cont_at hH hf'.1 _ σ) (fam_law_real hH hf' σ) h
  simp only [res, fam_add, eisS]
  rw [cosetSum_add c1 c2]; ring

theorem resA_smul (hS : SphBound) (hp : 1 ≤ p) {H : G D p → ℝ≥0} (hH : IsHt H) {C : Set (G D p)} (hC : IsCompact C)
    (hcov : ∀ g, ∃ q ∈ P D p, ∃ c ∈ C, g = q * c) {f : G D p → ℂ} (hf : IsRho f) (c : ℂ) (h : G D p) :
    resA H (c • f) h = c * resA H f h := by
  refine tendsto_nhds_unique (res_tendsto hS hp hH hC hcov (rho_smul hf c) h) ?_
  refine ((res_tendsto hS hp hH hC hcov hf h).const_mul c).congr fun σ => ?_
  simp only [res, fam_smul, eisS]
  rw [cosetSum_smul]; ring

theorem npow_real {r : ℝ≥0} (σ : ℝ) : npow r ((σ : ℂ) - (p : ℂ) / 2) = (((r : ℝ) ^ (σ - p / 2) : ℝ) : ℂ) := by
  rw [npow, Complex.ofReal_cpow r.coe_nonneg]; push_cast; rfl

theorem resA_pos (hS : SphBound) (hp : 1 ≤ p) {H : G D p → ℝ≥0} (hH : IsHt H) {C : Set (G D p)} (hC : IsCompact C)
    (hcov : ∀ g, ∃ q ∈ P D p, ∃ c ∈ C, g = q * c) {f : G D p → ℂ} (hf : IsRho f)
    (hpos : ∀ g, 0 ≤ (f g).re ∧ (f g).im = 0) (h : G D p) : 0 ≤ (resA H f h).re ∧ (resA H f h).im = 0 := by
  have hT := res_tendsto hS hp hH hC hcov hf h
  have hev : ∀ᶠ σ in ((ufil p : Ultrafilter ℝ) : Filter ℝ), 0 ≤ (res H f σ h).re ∧ (res H f σ h).im = 0 := by
    refine ufil_le p ?_
    filter_upwards [ev_Ioc p] with σ hσ
    have c1 := conv_of_section hS hp hH hC hcov hσ (fam_cont_at hH hf.1 _ σ) (fam_law_real hH hf σ) h
    have hsum : Summable (term (P D p) (GF D p) (fam H f ((p : ℂ) / 2) (σ : ℂ)) h) := c1.of_norm
    have hterm : ∀ q, 0 ≤ (term (P D p) (GF D p) (fam H f ((p : ℂ) / 2) (σ : ℂ)) h q).re ∧
        (term (P D p) (GF D p) (fam H f ((p : ℂ) / 2) (σ : ℂ)) h q).im = 0 := fun q => by
      simp only [term, fam]
      rw [npow_real, Complex.re_ofReal_mul, Complex.im_ofReal_mul, (hpos _).2, mul_zero]
      exact ⟨mul_nonneg (Real.rpow_nonneg (NNReal.coe_nonneg _) _) (hpos _).1, rfl⟩
    have e1 : (eisS (fam H f ((p : ℂ) / 2) (σ : ℂ)) h).re ≥ 0 := by
      simp only [eisS, cosetSum]
      rw [Complex.re_tsum hsum]
      exact tsum_nonneg fun q => (hterm q).1
    have e2 : (eisS (fam H f ((p : ℂ) / 2) (σ : ℂ)) h).im = 0 := by
      simp only [eisS, cosetSum]
      rw [Complex.im_tsum hsum]
      simp only [hterm, tsum_zero]
    simp only [res]
    rw [Complex.re_ofReal_mul, Complex.im_ofReal_mul, e2, mul_zero]
    exact ⟨mul_nonneg (by linarith [hσ.1]) e1, rfl⟩
  have hre := (Complex.continuous_re.tendsto _).comp hT
  have him := (Complex.continuous_im.tendsto _).comp hT
  exact ⟨ge_of_tendsto hre (hev.mono fun σ h => h.1),
    tendsto_nhds_unique him (tendsto_const_nhds.congr' (hev.mono fun σ h => h.2.symm))⟩

theorem resA_bound (hS : SphBound) (hp : 1 ≤ p) {H : G D p → ℝ≥0} (hH : IsHt H) {C : Set (G D p)} (hC : IsCompact C)
    (hcov : ∀ g, ∃ q ∈ P D p, ∃ c ∈ C, g = q * c) (H' : G D p → ℝ≥0) (hH' : IsHt H') :
    ∃ K : ℝ, ∀ f, IsRho f → ∀ B : ℝ, (∀ g, ‖f g‖ ≤ B * (H' g : ℝ) ^ p) → ‖resA H f 1‖ ≤ K * B := by
  have hs : IsRho fun g => npow (H' g) (p : ℂ) := by
    refine ⟨continuous_npow hH'.1 hH'.2.1 _, fun q hq a ha g => ?_⟩
    show npow (H' (q * g)) (p : ℂ) = _ * npow (absA D _) ((p : ℂ) / 2 + (p : ℂ) / 2) * npow (H' g) (p : ℂ)
    rw [hH'.2.2 q hq a ha g, npow_mul, show (p : ℂ) / 2 + (p : ℂ) / 2 = p by ring]
    simp
  obtain ⟨δ, hδ⟩ := rho_bound hH hC hcov hs
  have hle : ∀ g, (H' g : ℝ) ^ p ≤ δ * (H g : ℝ) ^ p := fun g => by
    have := hδ g
    rwa [norm_npow (hH'.2.1 g), show ((p : ℂ)).re = (p : ℝ) by simp, Real.rpow_natCast] at this
  obtain ⟨B₁, -, hB₁⟩ := res_bound hS hp hH (isCompact_singleton (x := (1 : G D p)))
  refine ⟨δ * B₁, fun f hf B hB => ?_⟩
  have hB0 : 0 ≤ B := by
    have h1 := (norm_nonneg _).trans (hB 1)
    exact nonneg_of_mul_nonneg_left h1 (pow_pos (NNReal.coe_pos.2 (hH'.2.1 1)) p)
  have hf2 : ∀ g, ‖f g‖ ≤ (B * δ) * (H g : ℝ) ^ p := fun g =>
    (hB g).trans (by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (hle g) hB0)
  have hlim := (res_tendsto hS hp hH hC hcov hf 1).norm
  refine le_of_tendsto hlim ?_
  refine ufil_le p ?_
  filter_upwards [ev_Ioc p] with σ hσ
  have := hB₁ f _ hf2 σ hσ 1 rfl
  calc _ ≤ B * δ * B₁ := this
    _ = _ := by ring

end GlobalTheory.CompanionTheory.ResMu
