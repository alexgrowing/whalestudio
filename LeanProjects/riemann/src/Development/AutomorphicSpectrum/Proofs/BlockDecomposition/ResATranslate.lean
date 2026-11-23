import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EventuallySmall

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

theorem law_ratInv {n : ℕ} {z : ℂ} {s : G D n → ℂ} (hs : IsLaw 1 z s) : LeftInv (P D n ⊓ GF D n) s := fun γ hγ g => by
  obtain ⟨a, ha⟩ := GlobalTheory.StdUnn.LeftInvSect.exists_blkA hγ.1
  obtain ⟨u, hu⟩ := GlobalTheory.StdUnn.LeftInvSect.det_rat hγ.2 a ha
  have h1 : absA D (Units.map (incA D).toMonoidHom u) = 1 := absE_inclR u
  rw [hs γ hγ.1 a ha g, hu, h1]
  simp

theorem rho_right {f : G D p → ℂ} (hf : IsRho f) (x : G D p) : IsRho fun g => f (g * x) :=
  ⟨hf.1.comp (continuous_id.mul continuous_const), law_right hf.2 x⟩

theorem fam_law_real {H : G D p → ℝ≥0} (hH : IsHt H) {f : G D p → ℂ} (hf : IsRho f) (σ : ℝ) :
    IsLaw 1 (σ : ℂ) (fam H f ((p : ℂ) / 2) (σ : ℂ)) := fam_law hH hf.2 σ

theorem fam_cont_at {H : G D p → ℝ≥0} (hH : IsHt H) {f : G D p → ℂ} (hf : Continuous f) (s₁ : ℂ) (σ : ℝ) :
    Continuous (fam H f s₁ (σ : ℂ)) :=
  (fam_cont hH hf s₁).comp (f := fun g : G D p => ((σ, g) : ℝ × G D p)) (by fun_prop)

theorem fam_at (H : G D p → ℝ≥0) (f : G D p → ℂ) : fam H f ((p : ℂ) / 2) (((p : ℝ) / 2 : ℝ) : ℂ) = f := by
  funext g
  have : ((((p : ℝ) / 2 : ℝ) : ℂ)) - (p : ℂ) / 2 = 0 := by push_cast; ring
  simp [fam, this]

theorem res_leftInv {H : G D p → ℝ≥0} (hH : IsHt H) {f : G D p → ℂ} (hf : IsRho f) (σ : ℝ) :
    LeftInv (GF D p) (res H f σ) := fun γ hγ g => by
  simp only [res, eisS]
  rw [leftInv_cosetSum (law_ratInv (fam_law_real hH hf σ)) γ hγ g]

theorem eis_right (s : G D p → ℂ) (x : G D p) : eisS s x = eisS (fun g => s (g * x)) 1 := by
  simp only [eisS]
  rw [cosetSum_mul_right, one_mul]

theorem res_equi (hS : SphBound) (hp : 1 ≤ p) {H : G D p → ℝ≥0} (hH : IsHt H) {C : Set (G D p)} (hC : IsCompact C)
    (hcov : ∀ g, ∃ q ∈ P D p, ∃ c ∈ C, g = q * c) {f : G D p → ℂ} (hf : IsRho f) (x : G D p) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x' in 𝓝 x, ∀ σ ∈ Ioc ((p : ℝ) / 2) (p / 2 + 1), ‖res H f σ x' - res H f σ x‖ ≤ ε := by
  obtain ⟨B, hB0, hB⟩ := eis_bound hS hp hH (isCompact_singleton (x := (1 : G D p)))
  have hK : IsCompact (Icc ((p : ℝ) / 2) (p / 2 + 1) ×ˢ C) := isCompact_Icc.prod hC
  have hε' : 0 < ε / (2 * (B + 1)) := by positivity
  have hfc := fam_cont hH hf.1 ((p : ℂ) / 2)
  have hev : ∀ᶠ x' in 𝓝 x, ∀ y ∈ Icc ((p : ℝ) / 2) (p / 2 + 1) ×ˢ C,
      ‖fam H f ((p : ℂ) / 2) (y.1 : ℂ) (y.2 * x') - fam H f ((p : ℂ) / 2) (y.1 : ℂ) (y.2 * x)‖ <
        ε / (2 * (B + 1)) * (H y.2 : ℝ) ^ (y.1 + p / 2) := by
    refine hK.eventually_forall_of_forall_eventually fun y _ => ?_
    have c1 : Continuous fun u : G D p × (ℝ × G D p) => fam H f ((p : ℂ) / 2) (u.2.1 : ℂ) (u.2.2 * u.1) :=
      hfc.comp (f := fun u : G D p × (ℝ × G D p) => ((u.2.1, u.2.2 * u.1) : ℝ × G D p)) (by fun_prop)
    have c2 : Continuous fun u : G D p × (ℝ × G D p) => fam H f ((p : ℂ) / 2) (u.2.1 : ℂ) (u.2.2 * x) :=
      hfc.comp (f := fun u : G D p × (ℝ × G D p) => ((u.2.1, u.2.2 * x) : ℝ × G D p)) (by fun_prop)
    have c3 : Continuous fun u : G D p × (ℝ × G D p) => ε / (2 * (B + 1)) * (H u.2.2 : ℝ) ^ (u.2.1 + p / 2) :=
      continuous_const.mul ((NNReal.continuous_coe.comp (hH.1.comp (continuous_snd.comp continuous_snd))).rpow
        ((continuous_fst.comp continuous_snd).add continuous_const) fun u => Or.inl (NNReal.coe_pos.2 (hH.2.1 _)).ne')
    refine ((c1.sub c2).norm.continuousAt.eventually_lt c3.continuousAt ?_)
    simp only [Pi.sub_apply, sub_self, norm_zero]
    exact mul_pos hε' (Real.rpow_pos_of_pos (NNReal.coe_pos.2 (hH.2.1 _)) _)
  filter_upwards [hev] with x' hx' σ hσ
  have hI' : σ ∈ Icc ((p : ℝ) / 2) (p / 2 + 1) := ⟨hσ.1.le, hσ.2⟩
  have hl := fam_law_real hH hf σ
  have hc := fam_cont_at hH hf.1 ((p : ℂ) / 2) σ
  have hct : ∀ y : G D p, Continuous fun g => fam H f ((p : ℂ) / 2) (σ : ℂ) (g * y) := fun y =>
    hc.comp (continuous_id.mul continuous_const)
  have hb := law_bound hH hcov (law_sub (law_right hl x') (law_right hl x)) (δ := ε / (2 * (B + 1))) (fun c hc =>
    (hx' (σ, c) ⟨hI', hc⟩).le)
  have hf' := (hB σ hσ 1 rfl _ _ hb).2
  rw [eis_sub (conv_of_section hS hp hH hC hcov hσ (hct x') (law_right hl x') 1)
    (conv_of_section hS hp hH hC hcov hσ (hct x) (law_right hl x) 1), ← eis_right, ← eis_right] at hf'
  have e : res H f σ x' - res H f σ x =
      ((σ - p / 2 : ℝ) : ℂ) * (eisS (fam H f ((p : ℂ) / 2) (σ : ℂ)) x' - eisS (fam H f ((p : ℂ) / 2) (σ : ℂ)) x) := by
    simp only [res]; ring
  rw [e, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by linarith [hσ.1])]
  have : ε / (2 * (B + 1)) * B ≤ ε := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  linarith

theorem res_cont (hS : SphBound) (hp : 1 ≤ p) {H : G D p → ℝ≥0} (hH : IsHt H) {C : Set (G D p)} (hC : IsCompact C)
    (hcov : ∀ g, ∃ q ∈ P D p, ∃ c ∈ C, g = q * c) {f : G D p → ℂ} (hf : IsRho f) {σ : ℝ}
    (hσ : σ ∈ Ioc ((p : ℝ) / 2) (p / 2 + 1)) : Continuous (res H f σ) := by
  rw [continuous_iff_continuousAt]
  intro x
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [res_equi hS hp hH hC hcov hf x (half_pos hε)] with x' hx'
  rw [dist_eq_norm]
  linarith [hx' σ hσ]

theorem resA_near (hS : SphBound) (hp : 1 ≤ p) {H : G D p → ℝ≥0} (hH : IsHt H) {C : Set (G D p)} (hC : IsCompact C)
    (hcov : ∀ g, ∃ q ∈ P D p, ∃ c ∈ C, g = q * c) {f : G D p → ℂ} (hf : IsRho f) (x : G D p) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x' in 𝓝 x, ‖resA H f x' - resA H f x‖ ≤ ε := by
  filter_upwards [res_equi hS hp hH hC hcov hf x hε] with x' hx'
  have h1 := ((res_tendsto hS hp hH hC hcov hf x').sub (res_tendsto hS hp hH hC hcov hf x)).norm
  refine le_of_tendsto h1 ?_
  refine ufil_le p ?_
  filter_upwards [ev_Ioc p] with σ hσ using hx' σ hσ

theorem resA_cont (hS : SphBound) (hp : 1 ≤ p) {H : G D p → ℝ≥0} (hH : IsHt H) {C : Set (G D p)} (hC : IsCompact C)
    (hcov : ∀ g, ∃ q ∈ P D p, ∃ c ∈ C, g = q * c) {f : G D p → ℂ} (hf : IsRho f) : Continuous (resA H f) := by
  rw [continuous_iff_continuousAt]
  intro x
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [resA_near hS hp hH hC hcov hf x (half_pos hε)] with x' hx'
  rw [dist_eq_norm]
  linarith

theorem resA_leftInv (hS : SphBound) (hp : 1 ≤ p) {H : G D p → ℝ≥0} (hH : IsHt H) {C : Set (G D p)} (hC : IsCompact C)
    (hcov : ∀ g, ∃ q ∈ P D p, ∃ c ∈ C, g = q * c) {f : G D p → ℂ} (hf : IsRho f) : LeftInv (GF D p) (resA H f) := fun γ hγ g => by
  refine tendsto_nhds_unique (res_tendsto hS hp hH hC hcov hf (γ * g)) ?_
  have := res_tendsto hS hp hH hC hcov hf g
  refine this.congr fun σ => ?_
  rw [res_leftInv hH hf σ γ hγ g]

theorem resA_unif (hS : SphBound) (hp : 1 ≤ p) {H : G D p → ℝ≥0} (hH : IsHt H) {C : Set (G D p)} (hC : IsCompact C)
    (hcov : ∀ g, ∃ q ∈ P D p, ∃ c ∈ C, g = q * c) {f : G D p → ℂ} (hf : IsRho f) {C' : Set (G D p)} (hC' : IsCompact C')
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ σ in ((ufil p : Ultrafilter ℝ) : Filter ℝ), ∀ c ∈ C', ‖res H f σ c - resA H f c‖ ≤ ε := by
  refine hC'.induction_on (p := fun S => ∀ᶠ σ in ((ufil p : Ultrafilter ℝ) : Filter ℝ), ∀ c ∈ S, ‖res H f σ c - resA H f c‖ ≤ ε)
    (by simp) (fun s t hst h => h.mono fun σ hσ c hc => hσ c (hst hc))
    (fun s t hs ht => by
      filter_upwards [hs, ht] with σ h1 h2 c hc
      exact hc.elim (h1 c) (h2 c)) fun x _ => ?_
  have hε3 : 0 < ε / 3 := by positivity
  refine ⟨_, mem_nhdsWithin_of_mem_nhds ((res_equi hS hp hH hC hcov hf x hε3).and (resA_near hS hp hH hC hcov hf x hε3)), ?_⟩
  have h1 : ∀ᶠ σ in ((ufil p : Ultrafilter ℝ) : Filter ℝ), ‖res H f σ x - resA H f x‖ < ε / 3 := by
    have := (res_tendsto hS hp hH hC hcov hf x)
    rw [Metric.tendsto_nhds] at this
    filter_upwards [this _ hε3] with σ hσ
    rwa [dist_eq_norm] at hσ
  filter_upwards [h1, ufil_le p (ev_Ioc p)] with σ hσ hI c hc
  have a1 := hc.1 σ hI
  have a2 := hc.2
  calc ‖res H f σ c - resA H f c‖ = ‖(res H f σ c - res H f σ x) + (res H f σ x - resA H f x) - (resA H f c - resA H f x)‖ := by
        congr 1; ring
    _ ≤ ‖res H f σ c - res H f σ x‖ + ‖res H f σ x - resA H f x‖ + ‖resA H f c - resA H f x‖ :=
        (norm_sub_le _ _).trans (by gcongr; exact norm_add_le _ _)
    _ ≤ ε := by linarith

theorem resA_translate (hS : SphBound) (hp : 1 ≤ p) {H : G D p → ℝ≥0} (hH : IsHt H) {C : Set (G D p)} (hC : IsCompact C)
    (hcov : ∀ g, ∃ q ∈ P D p, ∃ c ∈ C, g = q * c) {f : G D p → ℂ} (hf : IsRho f) (x : G D p) :
    resA H f x = resA H (fun g => f (g * x)) 1 := by
  have hfx := rho_right hf x
  have hd := tendsto_diff hS hp hH hC hcov
    (S := fun σ g => fam H f ((p : ℂ) / 2) (σ : ℂ) (g * x)) (S' := fun σ => fam H (fun g => f (g * x)) ((p : ℂ) / 2) (σ : ℂ))
    ((fam_cont hH hf.1 _).comp (f := fun u : ℝ × G D p => ((u.1, u.2 * x) : ℝ × G D p)) (by fun_prop)).continuousOn
    (fam_cont hH hfx.1 _).continuousOn
    (fun σ _ => law_right (fam_law_real hH hf σ) x) (fun σ _ => fam_law_real hH hfx σ)
    (by simp only [fam_at])
  have h1 := (hd.mono_left (ufil_le p)).add (res_tendsto hS hp hH hC hcov hfx 1)
  rw [zero_add] at h1
  refine tendsto_nhds_unique (res_tendsto hS hp hH hC hcov hf x) (h1.congr fun σ => ?_)
  simp only [res]
  rw [eis_right (fam H f ((p : ℂ) / 2) (σ : ℂ)) x]
  ring

end GlobalTheory.CompanionTheory.ResMu
