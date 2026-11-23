import Mathlib
import ReciprocityTheory.ThetaQuasiPeriods.ThetaQuasiPeriodStatement
import ReciprocityTheory.ThetaQuasiPeriods.Transl
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.FourierCoeffUnitCubeTranslateOfEntirePeriodic
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.EntirePeriodicEqZeroOfFourierCoeffEqZero
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.CardLePowOfLinearIndependent
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ClassicalThetaLevelAndLinearIndependent
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.MemSpanThetaOfLevel
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.RiemannThetaLevelOneNeZero
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsApplySubSmulNeZeroAndApplyAddNeZero

open ReciprocityTheory.PTheta Complex Matrix

namespace GlobalTheory.ThetaDivisionPoints

theorem theta_add_int_div {g : ℕ} {τ : Matrix (Fin g) (Fin g) ℂ} (hτ : τ.IsSymm) {N : ℕ}
    (hN : (N : ℂ) ≠ 0) (a : Fin g → ℝ) (z : Fin g → ℂ) (m : Fin g → ℤ) :
    theta a 0 ((N : ℂ) • (z + (N : ℂ)⁻¹ • ofIntVec m)) ((N : ℂ) • τ) =
      eC (ofRealVec a ⬝ᵥ ofIntVec m) * theta a 0 ((N : ℂ) • z) ((N : ℂ) • τ) := by
  have h := thetaQuasiPeriod_holds (Fin g) a 0 ((N : ℂ) • z) ((N : ℂ) • τ) 0 m (hτ.smul _)
  rw [ofIntVec_zero, mulVec_zero, add_zero] at h
  rw [smul_add, smul_smul, mul_inv_cancel₀ hN, one_smul, h]
  congr 1
  simp [autFactor, ofIntVec_zero, eC_zero]

theorem theta_add_tau_div {g : ℕ} {τ : Matrix (Fin g) (Fin g) ℂ} (hτ : τ.IsSymm) {N : ℕ}
    (hN : (N : ℂ) ≠ 0) (a : Fin g → ℝ) (z : Fin g → ℂ) (n : Fin g → ℤ) :
    ∃ u : ℂ, u ≠ 0 ∧ theta a 0 ((N : ℂ) • (z + (N : ℂ)⁻¹ • τ *ᵥ ofIntVec n)) ((N : ℂ) • τ) =
      u * theta (a + fun i => (n i : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ) := by
  have h := thetaRealTransl_holds (Fin g) a 0 (fun i => (n i : ℝ) / N) 0 ((N : ℂ) • z)
    ((N : ℂ) • τ) (hτ.smul _)
  have e0 : ofRealVec (0 : Fin g → ℝ) = 0 := by ext i; simp [ofRealVec]
  have e1 : ofRealVec (fun i => (n i : ℝ) / N) = (N : ℂ)⁻¹ • ofIntVec n := by
    ext i; simp [ofRealVec, ofIntVec, div_eq_inv_mul]
  have e2 : ((N : ℂ) • τ) *ᵥ ((N : ℂ)⁻¹ • ofIntVec n) = (N : ℂ) • (N : ℂ)⁻¹ • τ *ᵥ ofIntVec n := by
    rw [Matrix.smul_mulVec, Matrix.mulVec_smul]
  rw [e0, add_zero, add_zero (0 : Fin g → ℝ)] at h
  rw [smul_add, ← e2, ← e1]
  exact ⟨_, Complex.exp_ne_zero _, h⟩

noncomputable def intChar {g : ℕ} (N : ℕ) (c : Fin g → Fin N) : Multiplicative (Fin g → ℤ) →* ℂ where
  toFun m := eC (ofRealVec (fun i => ((c i : ℕ) : ℝ) / N) ⬝ᵥ ofIntVec m.toAdd)
  map_one' := by simp [ofIntVec_zero, eC_zero]
  map_mul' m m' := by rw [toAdd_mul, ofIntVec_add, dotProduct_add, eC_add]

theorem intChar_injective {g : ℕ} {N : ℕ} (hN : N ≠ 0) :
    Function.Injective (intChar (g := g) N) := by
  intro c c' h
  funext i
  have key : ∀ d : Fin g → Fin N, intChar N d (Multiplicative.ofAdd (Pi.single i 1)) =
      cexp (2 * Real.pi * I / N) ^ (d i : ℕ) := by
    intro d
    change eC (ofRealVec (fun i => ((d i : ℕ) : ℝ) / N) ⬝ᵥ ofIntVec (Pi.single i 1)) = _
    rw [GlobalTheory.ThetaSpan.ofIntVec_single, dotProduct_single_one, ← Complex.exp_nat_mul, eC]
    congr 1
    simp only [ofRealVec]
    push_cast
    ring
  have h1 := key c
  rw [h, key c'] at h1
  exact Fin.ext ((Complex.isPrimitiveRoot_exp N hN).pow_inj (c i).2 (c' i).2 h1.symm)

theorem mem_span_of_laws {g : ℕ} {τ : Matrix (Fin g) (Fin g) ℂ} (hτ : τ ∈ SiegelH (Fin g)) {N : ℕ}
    (hN : 1 ≤ N) {f : (Fin g → ℂ) → ℂ} (hf : Differentiable ℂ f ∧
      (∀ (i : Fin g) z, f (z + Pi.single i 1) = f z) ∧
      ∀ (j : Fin g) z, f (z + τ.mulVec (Pi.single j 1)) =
        eC (-(τ j j) / 2) ^ N * cexp (-(2 * Real.pi * I) * N * z j) * f z) :
    f ∈ Submodule.span ℂ (Set.range (fun (c : Fin g → Fin N) (z : Fin g → ℂ) =>
      theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ))) := by
  have f4 := @GlobalTheory.fourierCoeff_unitCube_translate_of_entire_periodic
  have f5 := @GlobalTheory.entire_periodic_eq_zero_of_fourierCoeff_eq_zero f4
  have hdim := @GlobalTheory.ClassicalTheta.card_le_pow_of_linearIndependent f4 f5
  obtain ⟨hlev, hli⟩ := classicalTheta_level_and_linearIndependent' g τ hτ N hN
  by_contra hnot
  have hopt := hli.option hnot
  have hcard : Fintype.card (Option (Fin g → Fin N)) = N ^ g + 1 := by simp
  let e := (Fintype.equivFinOfCardEq hcard).symm
  have hli' := hopt.comp e e.injective
  have := hdim g N τ (fun j => eC (-(τ j j) / 2)) hN (fun j => Complex.exp_ne_zero _)
    (N ^ g + 1) _ (fun k => ?_) hli'
  · omega
  · simp only [Function.comp_apply]
    rcases e k with _ | c
    · exact hf
    · exact ⟨(hlev c).1, GlobalTheory.ThetaSpan.laws_of_level τ N _ (hlev c).2⟩

theorem exists_theta_ne_zero {g : ℕ} {τ : Matrix (Fin g) (Fin g) ℂ} (hτ : τ ∈ SiegelH (Fin g))
    {N : ℕ} (hN : 2 ≤ N) (z : Fin g → ℂ) : ∃ c : Fin g → Fin N,
      theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ) ≠ 0 := by
  have f8 := @GlobalTheory.riemannTheta_level_one_ne_zero classicalTheta_level_and_linearIndependent'
  obtain ⟨f, hf, hz⟩ := GlobalTheory.exists_level_apply_ne_zero_of_two_le f8 g τ hτ N hN z
  have hs := mem_span_of_laws hτ (by omega : 1 ≤ N) ⟨hf.1, GlobalTheory.ThetaSpan.laws_of_level τ N f hf.2⟩
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hs
  by_contra hcon
  push Not at hcon
  apply hz
  rw [← ha]
  simp [Finset.sum_apply, hcon]

theorem exists_division_point_ne_zero :
    ∀ (g N : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ) (β : Fin g → ℂ) (f : (Fin g → ℂ) → ℂ), τ.IsSymm → (τ.map Complex.im).PosDef → 2 ≤ N → (∀ j, β j ≠ 0) → Differentiable ℂ f → f ≠ 0 → (∀ (i : Fin g) z, f (z + Pi.single i 1) = f z) → (∀ (j : Fin g) z, f (z + τ.mulVec (Pi.single j 1)) = β j * cexp (-(2 * Real.pi * I) * N * z j) * f z) → ∃ m n : Fin g → ℤ, f ((N : ℂ)⁻¹ • ((fun i => (m i : ℂ)) + τ.mulVec (fun i => (n i : ℂ)))) ≠ 0 := by
  intro g N τ β f hs hp hN hβ hd hf0 hper hlaw
  have hτ : τ ∈ SiegelH (Fin g) := ⟨hs, hp⟩
  have hN0 : N ≠ 0 := by omega
  have hNC : (N : ℂ) ≠ 0 := by exact_mod_cast hN0
  have hπ : (2 * Real.pi * I : ℂ) ≠ 0 := Complex.two_pi_I_ne_zero
  let w : Fin g → ℂ := fun j => Complex.log (β j) / (2 * Real.pi * I * N) + τ j j / 2
  have hw : ∀ j, β j * cexp (-(2 * Real.pi * I) * N * w j) = eC (-(τ j j) / 2) ^ N := by
    intro j
    rw [eC, ← Complex.exp_nat_mul]
    conv_lhs => rw [← Complex.exp_log (hβ j), ← Complex.exp_add]
    congr 1
    simp only [w]
    field_simp
    ring
  have hF := mem_span_of_laws (f := fun z => f (z + w)) hτ (by omega : 1 ≤ N)
    ⟨hd.comp (by fun_prop), fun i z => by
      rw [add_right_comm, hper], fun j z => by
      rw [add_right_comm, hlaw, ← hw j, Pi.add_apply, mul_add, Complex.exp_add]
      ring⟩
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hF
  obtain ⟨c₀, hc₀⟩ : ∃ c, a c ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hf0
    funext z
    have := congrFun ha (z - w)
    simpa [hcon] using this.symm
  by_contra hcon
  push Not at hcon
  have hvan : ∀ n : Fin g → ℤ, theta (fun i => ((c₀ i : ℕ) : ℝ) / N) 0
      ((N : ℂ) • (-w + (N : ℂ)⁻¹ • τ *ᵥ ofIntVec n)) ((N : ℂ) • τ) = 0 := by
    intro n
    have hli := (linearIndependent_monoidHom (Multiplicative (Fin g → ℤ)) ℂ).comp _
      (intChar_injective (g := g) hN0)
    have := Fintype.linearIndependent_iff.1 hli
      (fun c => a c * theta (fun i => ((c i : ℕ) : ℝ) / N) 0
        ((N : ℂ) • (-w + (N : ℂ)⁻¹ • τ *ᵥ ofIntVec n)) ((N : ℂ) • τ)) (by
        funext m
        have h1 := congrFun ha (-w + (N : ℂ)⁻¹ • τ *ᵥ ofIntVec n + (N : ℂ)⁻¹ • ofIntVec m.toAdd)
        have h2 := hcon m.toAdd n
        have e : -w + (N : ℂ)⁻¹ • τ *ᵥ ofIntVec n + (N : ℂ)⁻¹ • ofIntVec m.toAdd + w =
            (N : ℂ)⁻¹ • ((fun i => (m.toAdd i : ℂ)) + τ.mulVec (fun i => (n i : ℂ))) := by
          rw [smul_add]
          change _ = (N : ℂ)⁻¹ • ofIntVec m.toAdd + (N : ℂ)⁻¹ • τ *ᵥ ofIntVec n
          abel
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h1 ⊢
        rw [e, h2] at h1
        rw [Pi.zero_apply, ← h1]
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [theta_add_int_div hs hNC, mul_assoc, mul_comm (eC _)]
        rfl) c₀
    exact (mul_eq_zero.1 this).resolve_left hc₀
  obtain ⟨c, hc⟩ := exists_theta_ne_zero hτ hN (-w)
  obtain ⟨u, hu, h⟩ := theta_add_tau_div hs hNC (fun i => ((c₀ i : ℕ) : ℝ) / N) (-w)
    (fun i => ((c i : ℕ) : ℤ) - ((c₀ i : ℕ) : ℤ))
  rw [hvan] at h
  have e : ((fun i => ((c₀ i : ℕ) : ℝ) / N) +
      fun i => ((((c i : ℕ) : ℤ) - ((c₀ i : ℕ) : ℤ) : ℤ) : ℝ) / N) =
      fun i => ((c i : ℕ) : ℝ) / N := by
    funext i
    simp only [Pi.add_apply]
    push_cast
    ring
  rw [e] at h
  exact mul_ne_zero hu hc h.symm

end GlobalTheory.ThetaDivisionPoints
