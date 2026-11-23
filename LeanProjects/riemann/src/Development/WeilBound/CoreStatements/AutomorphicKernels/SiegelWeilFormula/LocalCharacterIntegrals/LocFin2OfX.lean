import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalCharacterIntegrals.ContinuousLatticeNorm
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalCharacterIntegrals.DifferentiableSetIntegralFz

noncomputable section

namespace PositivityTheory.SiegelWeilFormula.SwLocFin

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory GlobalTheory.Cont PositivityTheory.PfSWUS.Loc PositivityTheory.SiegelWeilFormula.Gen Filter Topology
open scoped TensorProduct Matrix

theorem whI_eq {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {M n : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F))
    (μv : Measure (Fin n → Fin M → Fv F v ⊗[F] E)) (lam : Measure (Fin n → Fv F v ⊗[F] E))
    (L₁ L₂ : AddSubgroup (Fin n → Fv F v ⊗[F] E)) (Φv : (Fin n → Fin M → Fv F v ⊗[F] E) → ℂ)
    (T : HermR (Fv F v) σ n) (z : ℂ) (b : HermR (Fv F v) σ n) :
    whI (Fv F v) σ J (psiV F ψ v) μv Φv (nu2 lam L₁ L₂) T.1 z b =
      fz (fun b : HermR (Fv F v) σ n => nu2 lam L₁ L₂ b.1) (uu σ J ψ v μv Φv T) (((M : ℂ) - n) / 2) z b := by
  simp only [whI, fz, uu, mul_assoc]

theorem locFinX_of (hS : ShellP) (hC : ConvP) (hD : DualP) : LocFinX := by
  intro F E _ _ _ _ _ σ hcm M J hJ n ψ hψ v μv νv lam L₁ L₂ hμ hν hlam h₁ h₂ Φv hΦ g hg T hT
  have h : Hyp σ M J n ψ v μv νv lam L₁ L₂ Φv g T := ⟨hcm, hJ, hψ, hμ, hν, hlam, h₁, h₂, hΦ, hg, hT⟩
  haveI : νv.IsAddHaarMeasure := hν.1
  obtain ⟨R₀, hR₀⟩ := hS F E σ M J n ψ v μv νv lam L₁ L₂ Φv g T h 2 one_lt_two
  set R₁ : ℝ := max R₀ 1 with hR₁
  have hR₁pos : 0 < R₁ := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  set B : ℕ → Set (HermR (Fv F v) σ n) := fun j => {b | nM v b.1 ≤ R₁ * 2 ^ j} with hB
  have hWeq : ∀ z, whI (Fv F v) σ J (psiV F ψ v) μv Φv (nu2 lam L₁ L₂) T.1 z =
      fz (fun b : HermR (Fv F v) σ n => nu2 lam L₁ L₂ b.1) (uu σ J ψ v μv Φv T) (((M : ℂ) - n) / 2) z :=
    fun z => funext fun b => whI_eq σ J ψ v μv lam L₁ L₂ Φv T z b
  obtain ⟨W, hWd, hW0, t, hWt⟩ := core νv (fun b : HermR (Fv F v) σ n => nu2 lam L₁ L₂ b.1) (uu σ J ψ v μv Φv T)
    (((M : ℂ) - n) / 2) (g T) B
    (fun j => measurableSet_ballH _)
    (fun i j hij => by
      intro b hb
      simp only [hB, Set.mem_setOf_eq] at hb ⊢
      exact hb.trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ one_le_two hij) hR₁pos.le))
    (by
      refine Set.eq_univ_of_forall fun b => ?_
      obtain ⟨j, hj⟩ := pow_unbounded_of_one_lt (nM v b.1 / R₁) one_lt_two
      refine Set.mem_iUnion.2 ⟨j, ?_⟩
      simp only [hB, Set.mem_setOf_eq]
      rw [div_lt_iff₀ hR₁pos] at hj
      linarith)
    (fun j => (isCompact_ballH _).measure_lt_top)
    (lattice_norm_ge_one h)
    (continuous_lattice_norm h).measurable
    (fun j => by
      obtain ⟨C, hC⟩ := (isCompact_ballH (σ := σ) (n := n) (v := v) (R₁ * 2 ^ j)).exists_bound_of_continuousOn
        (continuous_lattice_norm h).continuousOn
      exact ⟨C, fun b hb => (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hC b hb)⟩)
    (continuous_uu h).aestronglyMeasurable
    (uu_bound h)
    (fun z j => by
      have hset : B (j + 1) \ B j = {b : HermR (Fv F v) σ n | R₁ * 2 ^ j < nM v b.1 ∧ nM v b.1 ≤ 2 * (R₁ * 2 ^ j)} := by
        ext b
        simp only [hB, Set.mem_diff, Set.mem_setOf_eq, not_le, pow_succ]
        constructor
        · rintro ⟨h1, h2⟩; exact ⟨h2, by linarith⟩
        · rintro ⟨h1, h2⟩; exact ⟨by linarith, h1⟩
      rw [hset, ← hWeq z]
      exact hR₀ _ ((le_max_left _ _).trans (le_mul_of_one_le_right hR₁pos.le (one_le_pow₀ one_le_two))) z)
    (by
      obtain ⟨t, ht⟩ := hC F E σ M J n ψ v μv νv lam L₁ L₂ Φv g T h
      exact ⟨t, fun z hz => by rw [← hWeq z]; exact ht z hz⟩)
    ((hD F E σ M J n ψ v μv νv lam L₁ L₂ Φv g T h).comp
      (Tendsto.const_mul_atTop hR₁pos (tendsto_pow_atTop_atTop_of_one_lt one_lt_two)))
  refine ⟨W, hWd, hW0, t, fun z hz => ?_⟩
  rw [hWeq z]
  exact hWt z hz

theorem locFin2_of_X (h : LocFinX) : LocFin2 := by
  intro F E _ _ _ _ _ σ hcm M J hJ n _ ψ hψ v μv νv lam L₁ L₂ hμ hν hlam h₁ h₂ Φv hΦ g hg T hT
  exact h F E σ hcm M J hJ n ψ hψ v μv νv lam L₁ L₂ hμ hν hlam h₁ h₂ Φv hΦ g hg T hT

end PositivityTheory.SiegelWeilFormula.SwLocFin
