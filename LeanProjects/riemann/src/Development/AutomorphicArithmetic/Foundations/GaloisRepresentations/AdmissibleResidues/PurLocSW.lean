import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.PurityTempered.AlgPowConst
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.RealDefs
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.StringRepresentations.MonodromyFreeOfEigenvalueRatio
import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CharpolySmulScaleRoots
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitaryDualGL.GenericUnitaryDual.GenericUnitaryDualGLHolds

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Th
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.GalN.V
open private ex_elt algPow_const flag_cont cyc_cont from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.PurityTempered.AlgPowConst

private theorem map_zpow_eq_intCast_mul_of_map_mul_eq_add {Γ R : Type} [Group Γ] [Ring R] (f : Γ → R) (hf : ∀ a b, f (a * b) = f a + f b)
    (g : Γ) (m : ℤ) : f (g ^ m) = (m : R) * f g := by
  let D : Γ →* Multiplicative R := MonoidHom.mk' (fun x => Multiplicative.ofAdd (f x)) (by
    intro a b
    rw [hf]
    rfl)
  have h := congrArg Multiplicative.toAdd (map_zpow D g m)
  simp only [toAdd_zpow] at h
  rw [zsmul_eq_mul] at h
  exact h

private theorem int_zero {Γ : Type} [Group Γ] (d : Γ → ℤ) (L : Γ → ℝ) (hd : ∀ a b, d (a * b) = d a + d b)
    (hL : ∀ a b, L (a * b) = L a + L b) (φ : Γ) (hφ : d φ = 1) {c : ℝ} (hc : 0 < c) (hw : ∀ g, d g = 1 → |L g| < c)
    (s : Γ) (hs : d s ≠ 0) (k : ℤ) (hk : L s = k * d s * c) : k = 0 := by
  have hD := map_zpow_eq_intCast_mul_of_map_mul_eq_add d hd
  have hLz := map_zpow_eq_intCast_mul_of_map_mul_eq_add L hL
  have key : ∀ m : ℤ, |(m : ℝ) * (d s : ℝ) * (k * c - L φ) + L φ| < c := by
    intro m
    have h1 : d (s ^ m * φ ^ (1 - m * d s)) = 1 := by
      rw [hd, hD, hD, hφ]
      push_cast
      ring
    have h2 := hw _ h1
    rw [hL, hLz, hLz, hk] at h2
    convert h2 using 2
    push_cast
    ring
  have hδ : k * c - L φ = 0 := by
    by_contra hne
    have hpos : 0 < |k * c - L φ| := abs_pos.mpr hne
    obtain ⟨n, hn⟩ := exists_nat_gt (2 * c / |k * c - L φ|)
    have h1 := key n
    have h0 := key 0
    simp only [Int.cast_zero, zero_mul, zero_add] at h0
    have hds : (1 : ℝ) ≤ |(d s : ℝ)| := by
      have : (1 : ℤ) ≤ |d s| := Int.one_le_abs hs
      exact_mod_cast this
    have h3 : |(n : ℝ) * (d s : ℝ) * (k * c - L φ)| < 2 * c := by
      have := abs_sub (((n : ℤ) : ℝ) * (d s : ℝ) * (k * c - L φ) + L φ) (L φ)
      simp only [add_sub_cancel_right, Int.cast_natCast] at this
      simp only [Int.cast_natCast] at h1
      linarith
    rw [abs_mul, abs_mul, Nat.abs_cast] at h3
    rw [div_lt_iff₀ hpos] at hn
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith [mul_le_mul_of_nonneg_left hds (mul_nonneg hn0 hpos.le)]
  have hLφ : L φ = k * c := by linarith
  have h := hw φ hφ
  rw [hLφ, abs_mul, abs_of_pos hc] at h
  have hk1 : |(k : ℝ)| < 1 := by
    by_contra hh
    push_neg at hh
    nlinarith
  have : |k| < 1 := by exact_mod_cast hk1
  exact Int.abs_lt_one_iff.mp this

section

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
  {w : HeightOneSpectrum (𝓞 F)} {A : ValuationSubring Ω} {h : IsPlaceOver A w}

private theorem mono0_of_charPol_eq_prod_of_ne_normV_pow_mul {n : ℕ} (x : WD h) (μ : Fin n → Weil h →* ℂˣ) (hμ : ∀ i, GlobalTheory.WeilDeligne.IsSmooth (μ i))
    (hx : ∀ s, x.charPol s = ∏ i, (X - C (μ i s : ℂ)))
    (hne : ∀ i j, ∃ s, (μ i s : ℂ) ≠ ((normV w : ℕ) : ℂ) ^ deg s * μ j s) : x.mono0 := by
  obtain ⟨na, a, rfl⟩ := x.exists_rep
  rw [WD.monodromyZero_ofWeilDeligneRepClass_iff]
  let b := WDRep.ofChars h μ hμ
  have hc : ∀ σ, (a.ρ σ).charpoly = (b.ρ σ).charpoly := by
    intro σ
    rw [← WD.charPol_mk, hx, WDRep.ofChars_ρ, charpoly_diagEnd]
  obtain ⟨e, he⟩ := GlobalTheory.T.weilRep_equiv_of_charpoly_eq F Ω A w h na n a b hc
  have hes : ∀ σ z, e.symm (b.ρ σ z) = a.ρ σ (e.symm z) := by
    intro σ z
    apply e.injective
    rw [he, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  let N' : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ) := e.toLinearMap ∘ₗ a.N ∘ₗ e.symm.toLinearMap
  have hN' : ∀ σ z, b.ρ σ (N' z) = ((normV w : ℕ) : ℂ) ^ deg σ • N' (b.ρ σ z) := by
    intro σ z
    simp only [N', LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [← he, WDRep.comm_apply, hes, LinearEquiv.map_smul]
  have hsingle : ∀ σ j, b.ρ σ (Pi.single j 1) = (μ j σ : ℂ) • Pi.single j 1 := by
    intro σ j
    funext i
    rw [WDRep.ofChars_ρ, diagEnd_apply, Pi.smul_apply, smul_eq_mul]
    by_cases hij : i = j
    · subst hij
      simp
    · simp [Pi.single_apply, hij]
  have hM : ∀ i j, N' (Pi.single j 1) i = 0 := by
    intro i j
    obtain ⟨σ, hσ⟩ := hne i j
    have h1 := congrFun (hN' σ (Pi.single j 1)) i
    rw [hsingle, LinearMap.map_smul, WDRep.ofChars_ρ, diagEnd_apply, Pi.smul_apply, Pi.smul_apply,
      smul_eq_mul, smul_eq_mul] at h1
    have h2 : ((μ i σ : ℂ) - ((normV w : ℕ) : ℂ) ^ deg σ * μ j σ) * N' (Pi.single j 1) i = 0 := by
      rw [sub_mul, h1]
      ring
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact absurd (sub_eq_zero.mp h3) hσ
    · exact h3
  have hN0 : N' = 0 := by
    apply LinearMap.pi_ext'
    intro j
    apply LinearMap.ext_ring
    funext i
    simp only [LinearMap.comp_apply, LinearMap.coe_single, LinearMap.zero_comp, LinearMap.zero_apply, Pi.zero_apply]
    exact hM i j
  apply LinearMap.ext
  intro v
  have h4 := LinearMap.congr_fun hN0 (e v)
  simp only [N', LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, LinearMap.zero_apply] at h4
  rw [LinearMap.zero_apply]
  exact (LinearEquiv.map_eq_zero_iff e).mp h4

private theorem ratio_lt {n : ℕ} (x : WD h) (μ : Fin n → Weil h →* ℂˣ) (hμ : ∀ i, GlobalTheory.WeilDeligne.IsSmooth (μ i))
    (hx : ∀ s, x.charPol s = ∏ i, (X - C (μ i s : ℂ))) (ht : x.mono0 → RatioW x)
    (hor : (∀ i j, ∃ s, (μ i s : ℂ) ≠ ((normV w : ℕ) : ℂ) ^ deg s * μ j s) ∨ x.mono0) (i j : Fin n) (s : Weil h) (hs : deg s ≠ 0) (k : ℤ)
    (hk : ‖(μ i s : ℂ)‖ = ((normV w : ℕ) : ℝ) ^ (k * deg s) * ‖(μ j s : ℂ)‖) : k = 0 := by
  have hm : x.mono0 := by
    rcases hor with h1 | h1
    · exact mono0_of_charPol_eq_prod_of_ne_normV_pow_mul x μ hμ hx h1
    · exact h1
  have hR := ht hm
  have hq1 : (1 : ℝ) < ((normV w : ℕ) : ℝ) := by exact_mod_cast one_lt_normV w
  have hq0 : (0 : ℝ) < ((normV w : ℕ) : ℝ) := by linarith
  have hpos : ∀ l g, 0 < ‖(μ l g : ℂ)‖ := fun l g => norm_pos_iff.mpr (Units.ne_zero _)
  have hmem : ∀ g l, (μ l g : ℂ) ∈ x.eig g := by
    intro g l
    show (μ l g : ℂ) ∈ (x.charPol g).roots
    rw [hx]
    have hmon : (∏ k, (X - C (μ k g : ℂ))).Monic := monic_prod_of_monic _ _ (fun k _ => monic_X_sub_C _)
    rw [mem_roots hmon.ne_zero, IsRoot, eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ l) (by simp)
  refine int_zero (Γ := Weil h) deg (fun g => Real.log ‖(μ i g : ℂ)‖ - Real.log ‖(μ j g : ℂ)‖) deg_mul ?_ (frob h)
    deg_frob (Real.log_pos hq1) ?_ s hs k ?_
  · intro a b
    simp only [map_mul, Units.val_mul, norm_mul]
    rw [Real.log_mul (hpos i a).ne' (hpos i b).ne', Real.log_mul (hpos j a).ne' (hpos j b).ne']
    ring
  · intro g hg
    have h1 := hR g hg _ (hmem g i) _ (hmem g j)
    have h2 := hR g hg _ (hmem g j) _ (hmem g i)
    have l1 := Real.log_lt_log (hpos i g) h1
    have l2 := Real.log_lt_log (hpos j g) h2
    rw [Real.log_mul hq0.ne' (hpos j g).ne'] at l1
    rw [Real.log_mul hq0.ne' (hpos i g).ne'] at l2
    rw [abs_lt]
    constructor <;> linarith
  · beta_reduce
    rw [hk, Real.log_mul (zpow_pos hq0 _).ne' (hpos j s).ne', Real.log_zpow]
    push_cast
    ring

end
