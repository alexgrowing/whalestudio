import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsDCReps
import Development.AbelianVarietyTheory.Definitions.Foundations.PetEqRelIndexMulPetProd
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EichlerShimuraConjCocyclesCoboundariesPeriodSmul
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeBoundMain
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsEichlerShimuraDecompositionCocycleStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CuspFormsEqZeroOfPeriodSubConjCoboundaryStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CuspidalOfEichlerPeriodSubConjMemCoboundariesStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PeriodMapEquivariantStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeDoubleCosetRepsGammaOneGammaZeroLevelStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeOperatorOnCocycleMapsCocycleCoboundaryConjStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TendstoSlashValueAtInfty
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TqFSemisimple
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DiamondGenEigenEigen
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SlashSmulPos
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeOperatorsOnHalfPlaneFunctionsAgreeExplicit
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DiamondOperatorOfMatrixModularFormGamma1InterGamStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DiamondOperatorOfMatrixCuspFormGamma1InterGamma0Statement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeUOperatorPreservesModularFormGamma1InterGamStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsZeroAtFinsetSum
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeTOperatorExplicitModularFormStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeTOperatorExplicitCuspFormStatement

open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm

namespace GlobalTheory.HeckeFamilyMatrices.Semi

theorem integrand_cont (f : ℍ → ℂ) (hf : Continuous f) (τ : ℍ) :
    ContinuousOn (fun t : ℝ => (f ∘ UpperHalfPlane.ofComplex) (Complex.I + t * ((τ : ℂ) - Complex.I)))
      (Set.uIcc (0 : ℝ) 1) := by
  have h1 : ContinuousOn (f ∘ UpperHalfPlane.ofComplex) {z : ℂ | 0 < z.im} := by
    intro z hz
    exact (hf.continuousAt.comp (UpperHalfPlane.contMDiffAt_ofComplex (n := 0) hz).continuousAt).continuousWithinAt
  refine h1.comp (f := fun t : ℝ => Complex.I + t * ((τ : ℂ) - Complex.I)) (by fun_prop) ?_
  intro t ht
  rw [Set.uIcc_of_le zero_le_one] at ht
  have := τ.im_pos
  simp only [Set.mem_setOf_eq, Complex.add_im, Complex.I_im, Complex.mul_im, Complex.ofReal_re,
    Complex.sub_im, Complex.ofReal_im, zero_mul, add_zero, UpperHalfPlane.coe_im]
  rcases eq_or_lt_of_le ht.1 with h | h
  · rw [← h]; norm_num
  · nlinarith [mul_pos h this, ht.2]

theorem eichler_add_of_cont (w : ℕ) (f g : ℍ → ℂ) (hf : Continuous f) (hg : Continuous g) (τ : ℍ) :
    eichler w (f + g) τ = eichler w f τ + eichler w g τ := by
  simp only [eichler, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← add_mul, ← C_add, ← mul_add, ← intervalIntegral.integral_add]
  · congr 3
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp only [Function.comp_apply, Pi.add_apply]
    ring
  · refine ContinuousOn.intervalIntegrable ?_
    exact ((integrand_cont f hf τ).mul (by fun_prop)).mul (by fun_prop)
  · refine ContinuousOn.intervalIntegrable ?_
    exact ((integrand_cont g hg τ).mul (by fun_prop)).mul (by fun_prop)

theorem per_sub_smul (Γ : Subgroup SL(2, ℤ)) (w : ℕ) (f g : ℍ → ℂ) (hf : Continuous f) (hg : Continuous g) (a : ℂ) :
    per Γ w (f - a • g) = per Γ w f - a • per Γ w g := by
  have : f - a • g = f + (-a) • g := by rw [_root_.neg_smul, sub_eq_add_neg]
  rw [this, sub_eq_add_neg, ← _root_.neg_smul, ← (GlobalTheory.HeckeFamilyMatrices.cj_mem_Z1_cj_mem_B1_per_smul Γ w).2.2]
  funext γ
  simp only [per, Pi.add_apply]
  rw [eichler_add_of_cont w f _ hf (hg.const_smul (-a)), map_add]

theorem cj_sub {Γ : Type} (x y : Γ → ℂ[X]) : cj (x - y) = cj x - cj y := by
  funext γ; simp [cj]

theorem cj_smul {Γ : Type} (a : ℂ) (x : Γ → ℂ[X]) : cj (starRingEnd ℂ a • x) = a • cj x := by
  funext γ; simp [cj, smul_eq_C_mul]

theorem cj_pow {Γ : Type} (A : Module.End ℂ (Γ → ℂ[X])) (hA : ∀ z, cj (A z) = A (cj z)) (a : ℂ) (n : ℕ)
    (y : Γ → ℂ[X]) : cj (((A - starRingEnd ℂ a • 1) ^ n) y) = ((A - a • 1) ^ n) (cj y) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, ← ih]
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply]
    rw [cj_sub, hA, cj_smul]

theorem pow_mem {V : Type} [AddCommGroup V] [Module ℂ V] (B : Submodule ℂ V) (A : Module.End ℂ V)
    (hA : ∀ z ∈ B, A z ∈ B) (a : ℂ) (n : ℕ) : ∀ z ∈ B, ((A - a • 1) ^ n) z ∈ B := by
  induction n with
  | zero => intro z hz; simpa using hz
  | succ n ih =>
    intro z hz
    rw [pow_succ, Module.End.mul_apply]
    refine ih _ ?_
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply]
    exact B.sub_mem (hA z hz) (B.smul_mem a hz)

theorem per_iter (Γ : Subgroup SL(2, ℤ)) (k : ℕ) (A : Module.End ℂ (Γ → ℂ[X])) (F : (ℍ → ℂ) → ℍ → ℂ)
    (hB : ∀ z ∈ B1 Γ (k - 2), A z ∈ B1 Γ (k - 2))
    (hM : ∀ f : ModularForm Γ (k : ℤ), ∃ f' : ModularForm Γ (k : ℤ), ⇑f' = F ⇑f)
    (hE : ∀ f : ModularForm Γ (k : ℤ), per Γ (k - 2) (F ⇑f) - A (per Γ (k - 2) ⇑f) ∈ B1 Γ (k - 2))
    (a : ℂ) (n : ℕ) : ∀ f : ModularForm Γ (k : ℤ),
      ((A - a • 1) ^ n) (per Γ (k - 2) ⇑f) - per Γ (k - 2) ((fun G => F G - a • G)^[n] ⇑f) ∈ B1 Γ (k - 2) := by
  induction n with
  | zero => intro f; simp
  | succ n ih =>
    intro f
    obtain ⟨f', hf'⟩ := hM f
    have e : ⇑(f' - a • f) = F ⇑f - a • ⇑f := by rw [← hf']; rfl
    rw [Function.iterate_succ_apply, ← e, pow_succ, Module.End.mul_apply]
    have h1 := ih (f' - a • f)
    have h2 : (A - a • 1) (per Γ (k - 2) ⇑f) - per Γ (k - 2) ⇑(f' - a • f) ∈ B1 Γ (k - 2) := by
      have e' : ⇑(f' - a • f) = ⇑f' - a • ⇑f := rfl
      rw [e', per_sub_smul Γ _ _ _ (ModularFormClass.continuous f') (ModularFormClass.continuous f), hf']
      have := (B1 Γ (k - 2)).neg_mem (hE f)
      convert this using 1
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply]
      abel
    have h3 := pow_mem _ A hB a n _ h2
    rw [map_sub] at h3
    convert (B1 Γ (k - 2)).add_mem h3 h1 using 1
    abel

theorem iter_mf (Γ : Subgroup SL(2, ℤ)) (k : ℕ) (F : (ℍ → ℂ) → ℍ → ℂ)
    (hM : ∀ f : ModularForm Γ (k : ℤ), ∃ f' : ModularForm Γ (k : ℤ), ⇑f' = F ⇑f) (a : ℂ) (n : ℕ) :
    ∀ f : ModularForm Γ (k : ℤ), ∃ f' : ModularForm Γ (k : ℤ), ⇑f' = (fun G => F G - a • G)^[n] ⇑f := by
  induction n with
  | zero => intro f; exact ⟨f, rfl⟩
  | succ n ih =>
    intro f
    obtain ⟨f', hf'⟩ := hM f
    have e : ⇑(f' - a • f) = F ⇑f - a • ⇑f := by rw [← hf']; rfl
    rw [Function.iterate_succ_apply, ← e]
    exact ih _

theorem iter_cf (Γ : Subgroup SL(2, ℤ)) (k : ℕ) (F : (ℍ → ℂ) → ℍ → ℂ)
    (hS : ∀ f : CuspForm Γ (k : ℤ), ∃ f' : CuspForm Γ (k : ℤ), ⇑f' = F ⇑f) (a : ℂ) (n : ℕ) :
    ∀ f : CuspForm Γ (k : ℤ), ∃ f' : CuspForm Γ (k : ℤ), ⇑f' = (fun G => F G - a • G)^[n] ⇑f := by
  induction n with
  | zero => intro f; exact ⟨f, rfl⟩
  | succ n ih =>
    intro f
    obtain ⟨f', hf'⟩ := hS f
    have e : ⇑(f' - a • f) = F ⇑f - a • ⇑f := by rw [← hf']; rfl
    rw [Function.iterate_succ_apply, ← e]
    exact ih _

theorem direct (N : ℕ) (Γ : Subgroup SL(2, ℤ)) (k : ℕ) (hN : 5 ≤ N) (hΓ : Γ ≤ CongruenceSubgroup.Gamma1 N)
    (hfi : Γ.FiniteIndex) (hk : 3 ≤ k) (f : ModularForm Γ (k : ℤ)) (h : CuspForm Γ (k : ℤ))
    (H : per Γ (k - 2) ⇑f + cj (per Γ (k - 2) ⇑h) ∈ B1 Γ (k - 2)) : ⇑f = 0 ∧ ⇑h = 0 := by
  have e : cj (per Γ (k - 2) ⇑(-h)) = - cj (per Γ (k - 2) ⇑h) := by
    have : ⇑(-h) = starRingEnd ℂ (-1) • ⇑h := by simp
    rw [this, (GlobalTheory.HeckeFamilyMatrices.cj_mem_Z1_cj_mem_B1_per_smul Γ (k - 2)).2.2, cj_smul]; simp
  have H' : per Γ (k - 2) ⇑f - cj (per Γ (k - 2) ⇑(-h)) ∈ B1 Γ (k - 2) := by
    rw [e, sub_neg_eq_add]; exact H
  obtain ⟨f', hf'⟩ := GlobalTheory.T.cuspidal_of_eichlerPeriod_sub_conj_mem_coboundaries N Γ k hN hΓ hfi hk f (-h) H'
  rw [← hf'] at H' ⊢
  obtain ⟨h1, h2⟩ := GlobalTheory.T.cuspForms_eq_zero_of_period_sub_conj_coboundary N Γ k hN hΓ hfi hk f' (-h) H'
  rw [neg_eq_zero] at h2
  rw [h1, h2]
  exact ⟨rfl, rfl⟩

theorem key (N : ℕ) (Γ : Subgroup SL(2, ℤ)) (k : ℕ) (hN : 5 ≤ N) (hΓ : Γ ≤ CongruenceSubgroup.Gamma1 N)
    (hfi : Γ.FiniteIndex) (hk : 3 ≤ k) (A : Module.End ℂ (Γ → ℂ[X])) (F : (ℍ → ℂ) → ℍ → ℂ)
    (hB : ∀ z ∈ B1 Γ (k - 2), A z ∈ B1 Γ (k - 2)) (hA : ∀ z, cj (A z) = A (cj z))
    (hM : ∀ f : ModularForm Γ (k : ℤ), ∃ f' : ModularForm Γ (k : ℤ), ⇑f' = F ⇑f)
    (hS : ∀ f : CuspForm Γ (k : ℤ), ∃ f' : CuspForm Γ (k : ℤ), ⇑f' = F ⇑f)
    (hE : ∀ f : ModularForm Γ (k : ℤ), per Γ (k - 2) (F ⇑f) - A (per Γ (k - 2) ⇑f) ∈ B1 Γ (k - 2))
    (z : Γ → ℂ[X]) (f : ModularForm Γ (k : ℤ)) (h : CuspForm Γ (k : ℤ))
    (hz : z - per Γ (k - 2) ⇑f - cj (per Γ (k - 2) ⇑h) ∈ B1 Γ (k - 2)) (a : ℂ) (n : ℕ) :
    ((A - a • 1) ^ n) z ∈ B1 Γ (k - 2) ↔
      (fun G => F G - a • G)^[n] ⇑f = 0 ∧ (fun G => F G - starRingEnd ℂ a • G)^[n] ⇑h = 0 := by
  have h1 := pow_mem _ A hB a n _ hz
  rw [map_sub, map_sub] at h1
  have h2 := per_iter Γ k A F hB hM hE a n f
  have h3 := (GlobalTheory.HeckeFamilyMatrices.cj_mem_Z1_cj_mem_B1_per_smul Γ (k - 2)).2.1 _
    (per_iter Γ k A F hB hM hE (starRingEnd ℂ a) n (CuspForm.toModularFormₗ h))
  have eh : ⇑(CuspForm.toModularFormₗ h) = ⇑h := rfl
  rw [cj_sub, cj_pow A hA, eh] at h3
  obtain ⟨f', hf'⟩ := iter_mf Γ k F hM a n f
  obtain ⟨h', hh'⟩ := iter_cf Γ k F hS (starRingEnd ℂ a) n h
  rw [← hf'] at h2 ⊢
  rw [← hh'] at h3 ⊢
  have h4 : ((A - a • 1) ^ n) z - (per Γ (k - 2) ⇑f' + cj (per Γ (k - 2) ⇑h')) ∈ B1 Γ (k - 2) := by
    convert (B1 Γ (k - 2)).add_mem ((B1 Γ (k - 2)).add_mem h1 h2) h3 using 1
    abel
  constructor
  · intro H
    refine direct N Γ k hN hΓ hfi hk f' h' ?_
    convert (B1 Γ (k - 2)).sub_mem H h4 using 1
    abel
  · rintro ⟨e1, e2⟩
    have p0 : per Γ (k - 2) 0 = 0 := by
      have := (GlobalTheory.HeckeFamilyMatrices.cj_mem_Z1_cj_mem_B1_per_smul Γ (k - 2)).2.2 0 0
      simpa using this
    have c0 : cj (0 : Γ → ℂ[X]) = 0 := by funext γ; simp [cj]
    rw [e1, e2, p0, c0] at h4
    simpa using h4

theorem cusp_of_iter (Γ : Subgroup SL(2, ℤ)) (k : ℕ) (F : (ℍ → ℂ) → ℍ → ℂ) (c a : ℂ) (hca : a ≠ c)
    (hF : ∀ f : ModularForm Γ (k : ℤ), ∃ h : CuspForm Γ (k : ℤ), ⇑h = F ⇑f - c • ⇑f) (n : ℕ)
    (f : ModularForm Γ (k : ℤ)) (hf : (fun G => F G - a • G)^[n] ⇑f = 0) :
    ∃ h : CuspForm Γ (k : ℤ), ⇑h = ⇑f := by
  have main : ∀ (n : ℕ) (f : ModularForm Γ (k : ℤ)), ∃ h : CuspForm Γ (k : ℤ),
      (fun G => F G - a • G)^[n] ⇑f = (c - a) ^ n • ⇑f + ⇑h := by
    intro n
    induction n with
    | zero => intro f; exact ⟨0, by simp⟩
    | succ n ih =>
      intro f
      obtain ⟨h, hh⟩ := hF f
      have e : ⇑((c - a) • f + CuspForm.toModularFormₗ h) = (c - a) • ⇑f + ⇑h := rfl
      have e' : F ⇑f - a • ⇑f = (c - a) • ⇑f + ⇑h := by rw [hh, sub_smul]; abel
      obtain ⟨h', hh'⟩ := ih ((c - a) • f + CuspForm.toModularFormₗ h)
      refine ⟨(c - a) ^ n • h + h', ?_⟩
      have e2 : ⇑((c - a) ^ n • h + h') = (c - a) ^ n • ⇑h + ⇑h' := rfl
      rw [Function.iterate_succ_apply, e', ← e, hh', e, e2, smul_add, smul_smul, ← pow_succ, add_assoc]
  obtain ⟨h, hh⟩ := main n f
  have hne : (c - a) ^ n ≠ 0 := pow_ne_zero _ (sub_ne_zero.2 hca.symm)
  refine ⟨(-((c - a) ^ n)⁻¹) • h, ?_⟩
  have e : ⇑((-((c - a) ^ n)⁻¹) • h) = (-((c - a) ^ n)⁻¹) • ⇑h := rfl
  rw [hf] at hh
  have : ⇑h = -((c - a) ^ n • ⇑f) := by rw [eq_neg_iff_add_eq_zero, add_comm, ← hh]
  rw [e, this, smul_neg, _root_.neg_smul, neg_neg, smul_smul, inv_mul_cancel₀ hne, one_smul]

theorem DdF_eq (k : ℤ) (σ : SL(2, ℤ)) (f : ℍ → ℂ) : DdF k σ f = f ∣[k] σ := by
  have : toGL (mat σ) = (σ : GL (Fin 2) ℝ) := by
    have hd : ¬ (mat σ).det = 0 := by simp
    rw [toGL, dif_neg hd]
    ext i j
    rfl
  simp only [DdF, hkF, Finset.univ_unique, Finset.sum_singleton, this]
  rfl

theorem char_of_dia (N l k : ℕ) (χ : DirichletCharacter ℂ N) (σD : (ZMod N)ˣ → SL(2, ℤ))
    (hD : ∀ d : (ZMod N)ˣ, IsDiam N l (d : ZMod N) (σD d)) (f : CuspForm (Lev N l) (k : ℤ))
    (hf : ∀ d : (ZMod N)ˣ, DdF (k : ℤ) (σD d) ⇑f = χ (d : ZMod N) • ⇑f) (γ : SL(2, ℤ))
    (hγ : γ ∈ CongruenceSubgroup.Gamma0 (N * l)) :
    ⇑f ∣[(k : ℤ)] γ = χ ((mat γ 1 1 : ℤ) : ZMod N) • ⇑f := by
  have red : ∀ δ : SL(2, ℤ), δ ∈ CongruenceSubgroup.Gamma0 (N * l) →
      ((δ 1 0 : ℤ) : ZMod N) = 0 ∧ ((δ 1 0 : ℤ) : ZMod l) = 0 ∧
        ((δ 0 0 : ℤ) : ZMod N) * ((δ 1 1 : ℤ) : ZMod N) = 1 := by
    intro δ hδ
    rw [CongruenceSubgroup.Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd] at hδ
    push_cast at hδ
    have h1 : ((δ 1 0 : ℤ) : ZMod N) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 ((dvd_mul_right _ _).trans hδ)
    refine ⟨h1, (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 ((dvd_mul_left _ _).trans hδ), ?_⟩
    have := δ.det_coe
    rw [Matrix.det_fin_two] at this
    have := congrArg (Int.cast : ℤ → ZMod N) this
    push_cast at this
    rw [h1] at this
    simpa using this
  obtain ⟨g1, g2, g3⟩ := red γ hγ
  let d : (ZMod N)ˣ := ⟨((γ 1 1 : ℤ) : ZMod N), ((γ 0 0 : ℤ) : ZMod N), by rw [mul_comm]; exact g3, g3⟩
  obtain ⟨s0, s4⟩ := hD d
  obtain ⟨s1, s2, s3⟩ := red _ s0
  have s4' : (((σD d) 1 1 : ℤ) : ZMod N) = ((γ 1 1 : ℤ) : ZMod N) := s4
  have hm : γ * (σD d)⁻¹ ∈ Lev N l := by
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · rw [CongruenceSubgroup.Gamma1_mem]
      simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two,
        Matrix.mul_apply, Fin.sum_univ_two]
      simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      push_cast
      rw [s1, g1, s4']
      refine ⟨by rw [g3]; simp, ?_, by simp⟩
      rw [← s4', mul_comm _ (((σD d) 0 0 : ℤ) : ZMod N), s3]; simp
    · rw [CongruenceSubgroup.Gamma0_mem]
      simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two,
        Matrix.mul_apply, Fin.sum_univ_two]
      simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      push_cast
      rw [s2, g2]; simp
  have hinv : ⇑f ∣[(k : ℤ)] (γ * (σD d)⁻¹) = ⇑f :=
    SlashInvariantFormClass.slash_action_eq f _ (Subgroup.mem_map_of_mem _ hm)
  have : γ = (γ * (σD d)⁻¹) * σD d := by simp
  have h2 := hf d
  rw [DdF_eq] at h2
  calc ⇑f ∣[(k : ℤ)] γ = ⇑f ∣[(k : ℤ)] ((γ * (σD d)⁻¹) * σD d) := by rw [← this]
    _ = ⇑f ∣[(k : ℤ)] (σD d) := by rw [SlashAction.slash_mul, hinv]
    _ = _ := h2

theorem gamma_le_lev (N l : ℕ) : CongruenceSubgroup.Gamma (N * l) ≤ Lev N l := by
  intro γ hγ
  rw [CongruenceSubgroup.Gamma_mem] at hγ
  obtain ⟨h1, -, h3, h4⟩ := hγ
  have c1 := fun (x : ℤ) => map_intCast (ZMod.castHom (dvd_mul_right N l) (ZMod N)) x
  have c2 := fun (x : ℤ) => map_intCast (ZMod.castHom (dvd_mul_left l N) (ZMod l)) x
  refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
  · rw [CongruenceSubgroup.Gamma1_mem]
    refine ⟨?_, ?_, ?_⟩
    · rw [← c1, h1, map_one]
    · rw [← c1, h4, map_one]
    · rw [← c1, h3, map_zero]
  · rw [CongruenceSubgroup.Gamma0_mem, ← c2, h3, map_zero]

theorem pres (N l : ℕ) (k : ℤ) (hN : 0 < N) (hl : l.Prime) :
    (∀ (q : ℕ) (σ : SL(2, ℤ)), q.Prime → ¬ q ∣ N * l → IsDiam N l (q : ZMod N) σ →
      (∀ f : ModularForm (Lev N l) k, ∃ f' : ModularForm (Lev N l) k, ⇑f' = TqF k q σ ⇑f) ∧
      (∀ f : CuspForm (Lev N l) k, ∃ f' : CuspForm (Lev N l) k, ⇑f' = TqF k q σ ⇑f)) ∧
    (∀ f : ModularForm (Lev N l) k, ∃ f' : ModularForm (Lev N l) k, ⇑f' = UlF k l ⇑f) ∧
    (∀ f : CuspForm (Lev N l) k, ∃ f' : CuspForm (Lev N l) k, ⇑f' = UlF k l ⇑f) ∧
    ∀ (d : ZMod N) (σ : SL(2, ℤ)), IsDiam N l d σ →
      (∀ f : ModularForm (Lev N l) k, ∃ f' : ModularForm (Lev N l) k, ⇑f' = DdF k σ ⇑f) ∧
      (∀ f : CuspForm (Lev N l) k, ∃ f' : CuspForm (Lev N l) k, ⇑f' = DdF k σ ⇑f) := by
  obtain ⟨bU, bD, bT, bI, -⟩ := GlobalTheory.SlashUpperTriangularMatrices.bridge
  refine ⟨fun q σ hq hqn hσ => ?_, fun f => ?_, fun f => ?_, fun d σ hσ => ?_⟩
  · have hσ' : GlobalTheory.Hk.IsDia N l q σ := (bI N l q σ).1 (by simpa using hσ)
    refine ⟨fun f => ?_, fun f => ?_⟩
    · rw [bT k q σ _ hq.pos]; exact GlobalTheory.T.heckeTOperatorExplicit_modularForm N l q k σ hN hq hqn hσ' f
    · rw [bT k q σ _ hq.pos]; exact GlobalTheory.T.heckeTOperatorExplicit_cuspForm N l q k σ hN hq hqn hσ' f
  · rw [bU k l _ hl.pos]; exact GlobalTheory.T.heckeUOperator_preserves_modularForm_gamma1InterGamma0 N l l k hN hl.pos hl (dvd_mul_left l N) f
  · rw [bU k l _ hl.pos]; exact GlobalTheory.Hk.uOp_cuspForm N l l k hN hl.pos hl (dvd_mul_left l N) f
  · have hσ' : GlobalTheory.Hk.IsDia N l (mat σ 1 1) σ := (bI N l _ σ).1 ⟨hσ.1, rfl⟩
    refine ⟨fun f => ?_, fun f => ?_⟩
    · rw [bD]; exact GlobalTheory.T.diamondOperatorOfMatrix_modularForm_gamma1InterGamma0 N l k _ σ hN hσ' f
    · rw [bD]; exact GlobalTheory.T.diamondOperatorOfMatrix_cuspForm_gamma1InterGamma0 N l k _ σ hN hσ' f

end GlobalTheory.HeckeFamilyMatrices.Semi

open GlobalTheory.HeckeFamilyMatrices.Semi in

theorem GlobalTheory.HeckeFamilyMatrices.hecke_semisimple_at_newform : ∀ (k : ℕ) (g : UpperTheory.V.Af.Newform k) (N l : ℕ) (hN : g.M ∣ N), 5 ≤ N → l.Prime → ¬ l ∣ N → Odd k → 3 ≤ k →
  ∀ α : ℂ, α ^ 2 - g.a l * α + g.χ (l : ZMod g.M) * (l : ℂ) ^ (k - 1) = 0 →
  α ^ 2 ≠ g.χ (l : ZMod g.M) * (l : ℂ) ^ (k - 1) → α ^ 2 ≠ g.χ (l : ZMod g.M) * (l : ℂ) ^ (k - 2) →
  ∀ (σT : ℕ → SL(2, ℤ)) (σD : (ZMod N)ˣ → SL(2, ℤ)),
    (∀ q : ℕ, q.Prime → ¬ q ∣ N * l → IsDiam N l (q : ZMod N) (σT q)) →
    (∀ d : (ZMod N)ˣ, IsDiam N l (d : ZMod N) (σD d)) →
  ∀ z ∈ Z1 (Lev N l) (k - 2), ∀ n : ℕ,
    (∀ q : ℕ, q.Prime → ¬ q ∣ N * l →
      ((TqZ (Lev N l) (k - 2) q (σT q) - g.a q • 1) ^ n) z ∈ B1 (Lev N l) (k - 2)) →
    ((UlZ (Lev N l) (k - 2) l - α • 1) ^ n) z ∈ B1 (Lev N l) (k - 2) →
    (∀ d : (ZMod N)ˣ, ((DdZ (Lev N l) (k - 2) (σD d) - g.χ (ZMod.castHom hN (ZMod g.M) (d : ZMod N)) • 1) ^ n) z ∈ B1 (Lev N l) (k - 2)) →
    (∀ q : ℕ, q.Prime → ¬ q ∣ N * l →
      (TqZ (Lev N l) (k - 2) q (σT q) - g.a q • 1) z ∈ B1 (Lev N l) (k - 2)) ∧
    (UlZ (Lev N l) (k - 2) l - α • 1) z ∈ B1 (Lev N l) (k - 2) ∧
    (∀ d : (ZMod N)ˣ, (DdZ (Lev N l) (k - 2) (σD d) - g.χ (ZMod.castHom hN (ZMod g.M) (d : ZMod N)) • 1) z ∈ B1 (Lev N l) (k - 2)) := by
  intro k g N l hMN hN hl hlN hodd hk α _ hα1 hα2 σT σD hT hD z hz n zT zU zD
  have hle : Lev N l ≤ CongruenceSubgroup.Gamma1 N := inf_le_left
  have hpos : 0 < N * l := Nat.mul_pos (by omega) hl.pos
  have hfi : (Lev N l).FiniteIndex := by
    haveI : NeZero (N * l) := ⟨hpos.ne'⟩
    exact Subgroup.finiteIndex_of_le (gamma_le_lev N l)
  obtain ⟨f, h, hfh⟩ := GlobalTheory.T.exists_eichlerShimura_decomposition_cocycle N (N * l) (Lev N l) k hN hpos (gamma_le_lev N l) hle hodd hk z hz
  obtain ⟨rT, rU, rD⟩ := GlobalTheory.T.heckeDoubleCosetReps_gammaOneGammaZeroLevel N l hN hl hlN
  obtain ⟨pT, pU1, pU2, pD⟩ := pres N l (k : ℤ) (by omega) hl
  have keyT := fun (q : ℕ) (hq : q.Prime) (hqn : ¬ q ∣ N * l) =>
    have hk' := GlobalTheory.T.heckeOperatorOnCocycleMaps_cocycle_coboundary_conj (Lev N l) (k - 2) _ _ _
      (by simpa [dg, Matrix.det_fin_two] using hq.pos) (rT q (σT q) hq hqn (hT q hq hqn))
    have hp := pT q (σT q) hq hqn (hT q hq hqn)
    key N (Lev N l) k hN hle hfi hk (TqZ (Lev N l) (k - 2) q (σT q)) (TqF (k : ℤ) q (σT q))
      hk'.2.1 hk'.2.2 hp.1 hp.2
      (fun f => (GlobalTheory.T.per_hecke_and_diamond_sub_mem_b1_of_lev N l k hN hl hlN hk f).1 q (σT q) hq hqn (hT q hq hqn)) z f h hfh (g.a q)
  have keyU :=
    have hk' := GlobalTheory.T.heckeOperatorOnCocycleMaps_cocycle_coboundary_conj (Lev N l) (k - 2) _ _ _
      (by simpa [dg, Matrix.det_fin_two] using hl.pos) rU
    key N (Lev N l) k hN hle hfi hk (UlZ (Lev N l) (k - 2) l) (UlF (k : ℤ) l)
      hk'.2.1 hk'.2.2 pU1 pU2
      (fun f => (GlobalTheory.T.per_hecke_and_diamond_sub_mem_b1_of_lev N l k hN hl hlN hk f).2.1) z f h hfh α
  have keyD := fun d : (ZMod N)ˣ =>
    have hk' := GlobalTheory.T.heckeOperatorOnCocycleMaps_cocycle_coboundary_conj (Lev N l) (k - 2) _ _ _ (by simp) (rD d (σD d) (hD d))
    key N (Lev N l) k hN hle hfi hk (DdZ (Lev N l) (k - 2) (σD d)) (DdF (k : ℤ) (σD d))
      hk'.2.1 hk'.2.2 (pD d (σD d) (hD d)).1 (pD d (σD d) (hD d)).2
      (fun f => (GlobalTheory.T.per_hecke_and_diamond_sub_mem_b1_of_lev N l k hN hl hlN hk f).2.2 d (σD d) (hD d)) z f h hfh (g.χ (ZMod.castHom hMN (ZMod g.M) (d : ZMod N)))

  obtain ⟨f', hf'⟩ : ∃ f' : CuspForm (Lev N l) (k : ℤ), ⇑f' = ⇑f := by
    obtain ⟨q, hq, hgt, hmod⟩ := Nat.exists_prime_gt_modEq_one (N * l) hpos.ne'
    have hqn : ¬ q ∣ N * l := fun hd => absurd (Nat.le_of_dvd hpos hd) (not_le.2 hgt)
    have h1 : 1 < N * l := by nlinarith [hl.two_le]
    have hm : q % (N * l) = 1 := by rw [hmod, Nat.mod_eq_of_lt h1]
    exact cusp_of_iter (Lev N l) k (TqF (k : ℤ) q (σT q)) _ (g.a q)
      (GlobalTheory.HeckeFamilyMatrices.hecke_bound_main k g q hk hq (fun hd => hqn ((hd.trans hMN).mul_right l))).2
      (GlobalTheory.HeckeFamilyMatrices.EisT.tq_sub_smul_cuspForm N l k hN hl hlN hk q (σT q) hq hm (hT q hq hqn)) n f
      ((keyT q hq hqn n).1 (zT q hq hqn)).1
  have eD1 : ∀ d : (ZMod N)ˣ, DdF (k : ℤ) (σD d) ⇑f' = g.χ (ZMod.castHom hMN (ZMod g.M) (d : ZMod N)) • ⇑f' := fun d => by
    rw [hf']
    exact GlobalTheory.HeckeFamilyMatrices.diamond_genEigen_eigen N l k hN hl hlN hk d (σD d) (hD d) f _ n ((keyD d n).1 (zD d)).1
  have eD2 : ∀ d : (ZMod N)ˣ, DdF (k : ℤ) (σD d) ⇑h = starRingEnd ℂ (g.χ (ZMod.castHom hMN (ZMod g.M) (d : ZMod N))) • ⇑h := fun d =>
    GlobalTheory.HeckeFamilyMatrices.diamond_genEigen_eigen N l k hN hl hlN hk d (σD d) (hD d) (CuspForm.toModularFormₗ h) _ n ((keyD d n).1 (zD d)).2
  refine ⟨fun q hq hqn => ?_, ?_, fun d => ?_⟩
  · have H := (keyT q hq hqn n).1 (zT q hq hqn)
    have := (keyT q hq hqn 1).2 ⟨?_, ?_⟩
    · rwa [pow_one] at this
    · rw [← hf'] at H ⊢
      exact sub_eq_zero.2 (GlobalTheory.HeckeFamilyMatrices.tqF_semisimple N l k hN hl hlN hk q (σT q) hq hqn (hT q hq hqn) f' _ n H.1)
    · exact sub_eq_zero.2 (GlobalTheory.HeckeFamilyMatrices.tqF_semisimple N l k hN hl hlN hk q (σT q) hq hqn (hT q hq hqn) h _ n H.2)
  · have H := (keyU n).1 zU
    let χ : DirichletCharacter ℂ N := DirichletCharacter.changeLevel hMN g.χ
    have hχ : ∀ d : (ZMod N)ˣ, χ (d : ZMod N) = g.χ (ZMod.castHom hMN (ZMod g.M) (d : ZMod N)) := fun d =>
      DirichletCharacter.changeLevel_eq_cast_of_dvd g.χ hMN d
    have hχl : χ (l : ZMod N) = g.χ (l : ZMod g.M) := by
      have := hχ (ZMod.unitOfCoprime l ((Nat.Prime.coprime_iff_not_dvd hl).2 hlN))
      rwa [ZMod.coe_unitOfCoprime, map_natCast (ZMod.castHom hMN (ZMod g.M))] at this
    rw [← hχl] at hα1 hα2
    simp only [← hχ] at eD1 eD2
    have := (keyU 1).2 ⟨?_, ?_⟩
    · rwa [pow_one] at this
    · rw [← hf'] at H ⊢
      exact sub_eq_zero.2 (GlobalTheory.HeckeFamilyMatrices.ul_semisimple N l k hN hl hlN hk χ α hα1 hα2 f'
        (char_of_dia N l k χ σD hD f' eD1) n H.1)
    · refine sub_eq_zero.2 (GlobalTheory.HeckeFamilyMatrices.ul_semisimple N l k hN hl hlN hk (χ.ringHomComp (starRingEnd ℂ))
        (starRingEnd ℂ α) (fun e => hα1 ?_) (fun e => hα2 ?_) h
        (char_of_dia N l k _ σD hD h eD2) n H.2)
      · apply (starRingEnd ℂ).injective
        simpa using e
      · apply (starRingEnd ℂ).injective
        simpa using e
  · have := (keyD d 1).2 ⟨?_, ?_⟩
    · rwa [pow_one] at this
    · rw [← hf']; exact sub_eq_zero.2 (eD1 d)
    · exact sub_eq_zero.2 (eD2 d)
