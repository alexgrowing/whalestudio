import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsArithVarHasHhUnique
import Development.AbelianVarietyTheory.Definitions.Divisors.GenericPointAsIdeal
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.VolHomog
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightLineSelfIntersectionZeroOfEqualStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightLineIsNefOfAntitoneStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfInterGrLineShiftCoordinateStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfInterGrLinePermuteIndexStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TendstoIntegralWeightsApproxRealStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarizationDerivativeVanishStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical

noncomputable section
namespace GlobalTheory.FlagHtObj
open MvPolynomial GlobalTheory.FlagPoly GlobalTheory.FlagZ GlobalTheory.ArInt Formalism.DegreeFormula Filter Topology

theorem eq_zero_of_pow_hom {σ : Type} [Fintype σ] (d : ℕ) (ψ : MvPolynomial σ ℝ →ₗ[ℝ] ℝ)
    (h : ∀ n : σ → ℤ, ψ (lin (fun i => (n i : ℝ)) ^ d) = 0) (P : MvPolynomial σ ℝ) (hP : P.IsHomogeneous d) :
    ψ P = 0 := by
  have hc {Q : MvPolynomial σ ℝ} {e : ℕ} (hQ : Q.IsHomogeneous e) :
      homogeneousComponent d Q = if d = e then Q else 0 :=
    homogeneousComponent_of_mem ((mem_homogeneousSubmodule _ _).2 hQ)
  have hl (n : σ → ℝ) : (lin n ^ d).IsHomogeneous d := by
    have h1 : (lin n).IsHomogeneous 1 := IsHomogeneous.sum _ _ _ fun i _ => isHomogeneous_C_mul_X (n i) i
    simpa using h1.pow d
  have key := GlobalTheory.ArInt.Model.eq_zero_of_pow d (ψ ∘ₗ homogeneousComponent d)
    (fun n => by rw [LinearMap.comp_apply, hc (hl _), if_pos rfl, h n])
    (fun Q e he hQ => by rw [LinearMap.comp_apply, hc hQ, if_neg (Ne.symm he), map_zero])
  have := LinearMap.congr_fun key P
  rwa [LinearMap.comp_apply, hc hP, if_pos rfl] at this

theorem lin_add_pSum {ι : Type} [Fintype ι] [DecidableEq ι] {N : ℕ} (τ : ι) (n : ι × Fin N → ℤ) (t : ℤ) :
    lin (fun x : ι × Fin N => ((n x + if x.1 = τ then t else 0 : ℤ) : ℝ)) =
      lin (fun x => (n x : ℝ)) + C (t : ℝ) * pSum τ 1 := by
  simp only [lin, pSum, Int.cast_add, C_add, add_mul, Finset.sum_add_distrib, pow_one, Finset.mul_sum]
  congr 1
  rw [Fintype.sum_prod_type, Finset.sum_eq_single τ]
  · simp
  · intro b _ hb
    simp [hb]
  · simp

theorem rename_lin {ι : Type} [Fintype ι] {N : ℕ} (σ : Equiv.Perm ι) (n : ι × Fin N → ℝ) :
    rename (Prod.map σ id) (lin n) = lin (fun x => n (σ.symm x.1, x.2)) := by
  simp only [lin, map_sum, map_mul, rename_C, rename_X]
  exact (Equiv.sum_comp (Equiv.prodCongr σ (Equiv.refl _)) (fun y => C (n (σ.symm y.1, y.2)) * X y)).symm.trans
    (Finset.sum_congr rfl fun x _ => by simp) |>.symm

theorem flagHt_obj : Hypotheses2 → ∀ (ι : Type) [Fintype ι] (N : ℕ), GlobalTheory.FlagZ.HasHh ι N ∧ ∀ hh, GlobalTheory.FlagZ.IsHh ι N hh → FlagHt ι N hh := by
  intro hP ι _ N
  obtain ⟨hX, hE, -⟩ := isArithVar_hasHh_unique ι N
  refine ⟨hE hP.p4.arExists, fun Φ hΦ => ?_⟩
  refine ⟨fun j τ lam hj hjN _ hg => ?_, fun lam hd => ?_, fun τ Q hQ => ?_, fun σ F hF => ?_⟩
  · obtain ⟨u, c, hc, hu, ht⟩ := GlobalTheory.T.tendsto_integral_weights_approx_real ι N Φ (dimFl ι N + 1) lam
    have h0 (m : ℕ) : c m * Φ (linRoot (fun τ i => (u m τ i : ℝ)) ^ (dimFl ι N + 1)) = 0 := by
      have g := GlobalTheory.T.weight_line_selfIntersection_zero_of_equal hP ι N (u m) j τ hj hjN fun a b h₁ h₂ =>
        le_antisymm (hu m τ a b (hg a b h₁ h₂).le) (hu m τ b a (hg a b h₁ h₂).ge)
      rw [(hΦ.isSelfInter (u m)).unique hX g, mul_zero]
    simp only [h0] at ht
    exact tendsto_nhds_unique ht tendsto_const_nhds
  · obtain ⟨u, c, hc, hu, ht⟩ := GlobalTheory.T.tendsto_integral_weights_approx_real ι N Φ (dimFl ι N + 1) lam
    refine ge_of_tendsto' ht fun m => mul_nonneg (hc m).le ?_
    have hn := GlobalTheory.T.weight_line_isNef_of_antitone hP ι N (u m) fun τ a b hab => hu m τ b a (hd τ a b hab)
    have e := hP.p3 ℤ (Fl ι N) (flStr ι N) (dimFl ι N) hX _ _ hn (hΦ.isSelfInter (u m))
    exact EReal.coe_nonneg.1 (e ▸ GlobalTheory.ArInt.Model.arVol_nonneg _ _)
  · refine eq_zero_of_pow_hom (dimFl ι N) (Φ ∘ₗ LinearMap.mulLeft ℝ (pSum τ 1)) (fun n => ?_) Q hQ
    rw [LinearMap.comp_apply, LinearMap.mulLeft_apply]
    refine GlobalTheory.T.polarization_derivative_vanish _ Φ _ _ _ fun t => ?_
    rw [← lin_add_pSum]
    exact ((hΦ.1 _)).unique hX (GlobalTheory.T.selfInter_grLine_shift_coordinate hP ι N τ n t _ (hΦ.1 n))
  · have key := eq_zero_of_pow_hom (dimFl ι N + 1) (Φ ∘ₗ (rename (Prod.map (⇑σ) id)).toLinearMap - Φ) (fun n => ?_) F hF
    · rwa [LinearMap.sub_apply, sub_eq_zero] at key
    rw [LinearMap.sub_apply, sub_eq_zero, LinearMap.comp_apply, AlgHom.toLinearMap_apply, map_pow, rename_lin]
    have := GlobalTheory.T.selfInter_grLine_permute_index hP ι N σ.symm n _ (hΦ.1 n)
    exact (hΦ.1 _).unique hX this

end GlobalTheory.FlagHtObj
