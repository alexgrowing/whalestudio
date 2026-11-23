import Development.WeilBound.CoreStatements.CentralCharts.PshAt0Logdet

noncomputable section

namespace AnalyticReference.An

open ReciprocityTheory.AnForm GlobalTheory.CompanionTheory.Ar Filter Topology

variable {n a : ℕ} {f g : (Fin n → ℂ) → ℝ}

theorem Tame.add (hf : Tame a f) (hg : Tame a g) : Tame a fun t => f t + g t :=
  H.add hf hg

theorem Tame.const_mul (c : ℝ) (hf : Tame a f) : Tame a fun t => c * f t :=
  H.const_mul c hf

theorem Tame.sum {ι : Type} (s : Finset ι) {F : ι → (Fin n → ℂ) → ℝ} (h : ∀ i ∈ s, Tame a (F i)) :
    Tame a fun t => ∑ i ∈ s, F i t :=
  H.sum s h

theorem Tame.congr (hf : Tame a f) (h : ∀ᶠ t in 𝓝 (0 : Fin n → ℂ), (∀ i : Fin n, (i : ℕ) < a → t i ≠ 0) → g t = f t) :
    Tame a g :=
  H.congr hf h

theorem tame_log_norm (a : ℕ) {F : (Fin n → ℂ) → ℂ} (hF : AnalyticAt ℂ F 0) (h0 : F 0 ≠ 0) :
    Tame a fun t => Real.log ‖F t‖ :=
  H.tame_log_norm a hF h0

theorem tame_logdet {a₀ k r : ℕ} {Λ : Type} [AddCommGroup Λ] (L : Flat.LogPeriods n a₀ k Λ)
    (U : Fin r → (Fin n → ℂ) → Fin k → ℂ) (π : Equiv.Perm (Fin n)) (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hU : ∀ j, DifferentiableOn ℂ (U j) (Metric.ball 0 1)) (hli : LinearIndependent ℂ fun j => U j 0)
    (ha : ∀ i : Fin n, (i : ℕ) < a₀ → ((π.symm i : Fin n) : ℕ) < a) :
    Tame a fun t => Real.log (HodgeMetric.periodGram L U (HodgeMetric.uncentre 0 ρ π t)).det.re :=
  H.tame_logdet L U π ρ hρ hρ1 hU hli ha

theorem PshAt0.add (hf : PshAt0 f) (hg : PshAt0 g) : PshAt0 fun t => f t + g t :=
  H.padd hf hg

theorem PshAt0.const_mul {c : ℝ} (hc : 0 ≤ c) (hf : PshAt0 f) : PshAt0 fun t => c * f t :=
  H.pconst_mul hc hf

theorem PshAt0.sum {ι : Type} (s : Finset ι) {F : ι → (Fin n → ℂ) → ℝ} (h : ∀ i ∈ s, PshAt0 (F i)) :
    PshAt0 fun t => ∑ i ∈ s, F i t :=
  H.psum s h

theorem PshAt0.congr (hf : PshAt0 f) (h : g =ᶠ[𝓝 0] f) : PshAt0 g :=
  H.pcongr hf h

theorem pshAt0_log_norm (c d : ℝ) {F : (Fin n → ℂ) → ℂ} (hF : AnalyticAt ℂ F 0) (h0 : F 0 ≠ 0) :
    PshAt0 fun t => c * Real.log ‖F t‖ + d :=
  H.plog_norm c d hF h0

theorem pshAt0_logdet {k r : ℕ} {Λ : Type} [AddCommGroup Λ] (L : Flat.LogPeriods n 0 k Λ)
    (U : Fin r → (Fin n → ℂ) → Fin k → ℂ) (π : Equiv.Perm (Fin n)) (ρ : ℝ) (hρ : 0 < ρ)
    (hU : ∀ j, DifferentiableOn ℂ (U j) (Metric.ball 0 1)) (hli : LinearIndependent ℂ fun j => U j 0) :
    PshAt0 fun t => Real.log (HodgeMetric.periodGram L U (HodgeMetric.uncentre 0 ρ π t)).det.re :=
  H.pshAt0_logdet L U π ρ hρ hU hli

end AnalyticReference.An
