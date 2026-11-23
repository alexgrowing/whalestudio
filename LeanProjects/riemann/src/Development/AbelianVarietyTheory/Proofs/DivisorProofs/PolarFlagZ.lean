import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SuperFact
import Development.AbelianVarietyTheory.Definitions.Divisors.NormSqColGrLineOfOrthogonal
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RenameSwapAtMonomial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ArBirational
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OfSwap2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OddHarmZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsometricCombEquiv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagVarietyGradedLinesIsometricStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericDegreeEqFlagDegreeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SwapSymmetricImpliesSwapFlagStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SwapIdentityFromRegularBaseStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericDegreePullbackFormulaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithCalcSwapRegularStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SwapPolynomialIdentityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockPointHarmonicDegreeFlag

open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published GlobalTheory.FlagForm
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt GlobalTheory.CovTest.SwapZ GlobalTheory.BlockPoint
open scoped Classical

noncomputable section

namespace GlobalTheory.FlagSwapDefect

theorem swap_flagZ
    (hM : ∀ (ι : Type) [Fintype ι] (N : ℕ), ∃ (E : ι → (Sp ℤ).Modules) (h : ∀ a, VMetric (𝟙 (Sp ℤ)) (E a) N) (H : ∀ a, (h a).IsCInf) (fl : ∀ a, GlobalTheory.Vert.Flag ((Scheme.Modules.pullback (GlobalTheory.FlagZ.flStr ι N)).obj (E a)) N), IsFlagBundle (GlobalTheory.FlagZ.flStr ι N) E (fun _ => N) fl ∧ ∀ (a : ι) (i : Fin N), (VMetric.grLB (fl a) i ((H a).pull (GlobalTheory.FlagZ.flStr ι N) (Category.comp_id _))).Isometric (GlobalTheory.FlagZ.grLine (a, i)))
    (hD : ∀ (ι : Type) [Fintype ι] (N : ℕ) (n : ι × Fin N → ℤ), gdeg (comb (GlobalTheory.FlagZ.grLine (ι := ι) (N := N)) n) (dimFl ι N) = degFl ι N (lin (fun x => (n x : ℝ)) ^ dimFl ι N))
    (G : ℕ → ℤ → ℤ → MvPolynomial (Fin 3) ℝ) (hG : SwapFl G) (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ)
    (hh : Pol ι N →ₗ[ℝ] ℝ) (H : GlobalTheory.FlagZ.IsHh ι N hh) (τ : ι) (a b : Fin N) (hab : (b : ℕ) = a + 1)
    (n : ι × Fin N → ℤ) :
    hh (lin (fun z => (n z : ℝ)) ^ (dimFl ι N + 1)) +
        hh (lin (fun z => (n (swapAt τ a b z) : ℝ)) ^ (dimFl ι N + 1)) =
      degFl ι N (swapPol G (dimFl ι N) (τ, a) (τ, b) n) := by
  obtain ⟨E, h, Hc, fl, hfl, hiso⟩ := hM ι N
  have hX := (GlobalTheory.FlagZ.isArithVar_hasHh_unique ι N).1
  let e : (Σ _ : ι, Fin N) ≃ ι × Fin N := Equiv.sigmaEquivProd _ _
  have hΨ : IsGeoFun (GlobalTheory.FlagZ.grLine (ι := ι) (N := N)) (dimFl ι N) (degFlLin _ _) :=
    ⟨fun m => (degFlLin_apply _ _ _).trans (hD _ _ m).symm,
      fun P d hd hP => (degFlLin_apply _ _ _).trans (degFl_of_ne hP hd)⟩
  have key := hG ℤ (Sp ℤ) _ (𝟙 _) (GlobalTheory.FlagZ.flStr ι N) 0 _ ArithBase.isArithVar_int hX _
    (Category.comp_id _) ι E (fun _ => N) h Hc fl hfl _ _
    (isArFun_equiv hX e (fun z => hiso z.1 z.2) H) (isGeoFun_equiv e (fun z => hiso z.1 z.2) hΨ) τ a b hab
    fun z => n (e z)
  simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, map_pow] at key
  rw [rename_swapPol e G _ _ _ n, rename_lin e fun z => (n z : ℝ), degFlLin_apply] at key
  have hz : ∀ {inst : DecidableEq (Σ _ : ι, Fin N)} (z : Σ _ : ι, Fin N),
      e (@Equiv.swap _ inst ⟨τ, a⟩ ⟨τ, b⟩ z) = swapAt τ a b (e z) := by
    intro inst z
    obtain ⟨s, i⟩ := z
    rw [swapAt_eq]
    simp only [Equiv.swap_apply_def]
    split_ifs with h₁ h₂ h₃ h₄ h₃ h₄ <;> simp_all [e, Sigma.ext_iff, Prod.ext_iff]
  simp only [hz] at key
  rw [rename_lin e fun w => ((n (swapAt τ a b w) : ℤ) : ℝ)] at key
  convert key using 3 <;> rfl

theorem polar_flagZ
    (hM : ∀ (ι : Type) [Fintype ι] (N : ℕ), ∃ (E : ι → (Sp ℤ).Modules) (h : ∀ a, VMetric (𝟙 (Sp ℤ)) (E a) N) (H : ∀ a, (h a).IsCInf) (fl : ∀ a, GlobalTheory.Vert.Flag ((Scheme.Modules.pullback (GlobalTheory.FlagZ.flStr ι N)).obj (E a)) N), IsFlagBundle (GlobalTheory.FlagZ.flStr ι N) E (fun _ => N) fl ∧ ∀ (a : ι) (i : Fin N), (VMetric.grLB (fl a) i ((H a).pull (GlobalTheory.FlagZ.flStr ι N) (Category.comp_id _))).Isometric (GlobalTheory.FlagZ.grLine (a, i)))
    (hD : ∀ (ι : Type) [Fintype ι] (N : ℕ) (n : ι × Fin N → ℤ), gdeg (comb (GlobalTheory.FlagZ.grLine (ι := ι) (N := N)) n) (dimFl ι N) = degFl ι N (lin (fun x => (n x : ℝ)) ^ dimFl ι N))
    (hG : SwapFl swapG) (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ)
    (hh : Pol ι N →ₗ[ℝ] ℝ) (H : GlobalTheory.FlagZ.IsHh ι N hh) (σ : ι) (a b : Fin N) (hab : (b : ℕ) = a + 1)
    (k : ℕ) (M : Pol ι N) :
    hh ((X (σ, b) - X (σ, a)) ^ (2 * k) * mid (σ, a) (σ, b) M) =
      oddHarm k * degFl ι N ((X (σ, b) - X (σ, a)) ^ (2 * k - 1) * mid (σ, a) (σ, b) M) := by
  have hne : ((σ, a) : ι × Fin N) ≠ (σ, b) := fun h => by
    have := congrArg (fun p : ι × Fin N => (p.2 : ℕ)) h
    simp only at this
    omega
  have key := GlobalTheory.T.swap_polynomial_identity (ι × Fin N) (σ, a) (σ, b) hne (dimFl ι N) hh (degFlLin ι N)
    (fun P d hd hP => H.eq_zero hd hP) (fun P d hd hP => (degFlLin_apply _ _ _).trans (degFl_of_ne hP hd))
    (fun n => by
      rw [degFlLin_apply]
      have := swap_flagZ hM hD swapG hG ι N hh H σ a b hab n
      simp only [swapAt_eq] at this
      convert this using 3) k M
  rw [degFlLin_apply] at key
  convert key using 2
  congr

theorem swap_defect : ArCalc → RegularAlteration → GlobalTheory.CovTop.Hypotheses2 → GlobalTheory.Published.ArDegree → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ) (hh : Pol ι N →ₗ[ℝ] ℝ), GlobalTheory.FlagZ.IsHh ι N hh → ∀ (τ σ : ι) (a b : Fin N), (b : ℕ) = a + 1 → ∀ Q : Pol ι N, Q.IsHomogeneous (dimFl ι N - 1) → hh (pSum τ 2 * rename (swapAt σ a b) Q) - formDeg (bcForm τ * toForm (rename (swapAt σ a b) Q)) = -(hh (pSum τ 2 * Q) - formDeg (bcForm τ * toForm Q)) := by
  intro hAr hRA hP hAD ι _ _ N hh H τ σ a b hab Q hQ
  have hS2 : Swap2 swapG := GlobalTheory.T.swap_identity_from_regular_base hAr hRA GlobalTheory.T.generic_degree_pullback_formula swapG (GlobalTheory.T.arith_calc_swap_regular hAr)
  have hSF : SwapFl swapG := GlobalTheory.T.swap_symmetric_implies_swap_flag hAr swapG homog_swapG hS2
  exact GlobalTheory.T.block_point_harmonic_degree_flag ι N hh (fun P d hd hP => H.eq_zero hd hP) τ σ a b hab
    (fun k M => polar_flagZ GlobalTheory.T.flag_variety_graded_lines_isometric (GlobalTheory.T.generic_degree_eq_flag_degree hP hAD) hSF ι N hh H σ a b hab k M) Q hQ

end GlobalTheory.FlagSwapDefect
