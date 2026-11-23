import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ArchimedeanSchwartz.NormChar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExpOfMultiset
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsUnitaryTwistAbsPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdelicAbsValueCpowCharacterStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalLetterCentralExponentPropertiesStatement
import GroundTheory.AutomorphicForms.TensorProductTheorem.CentralCusp
import GroundTheory.AutomorphicForms.UnitaryAdmissible.CuspCentral

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.ResW GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
  GroundTheory.Automorphic.UnitaryAdmissible UpperTheory.V.Cm

attribute [local instance 100] LieRing.ofAssociativeRing

namespace UpperTheory.V.Z.Inf

private theorem exists_pullback {V C L G : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup C] [Module ℂ C]
    [NormedAddCommGroup L] [InnerProductSpace ℂ L] (j : V →ₗ[ℂ] C) (p : C →ₗ[ℂ] L) (T : G → V → V) (S : G → C → C)
    (P : C → Prop) (hP : ∀ x, P (j x)) (h1 : ∀ x, P x → inner ℂ (p x) (p x) = 0 → x = 0) (hj : ∀ x, j x = 0 → x = 0)
    (hT : ∀ g x, j (T g x) = S g (j x)) (hS : ∀ g x y, P x → P y → inner ℂ (p (S g x)) (p (S g y)) = inner ℂ (p x) (p y)) :
    ∃ Bf : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ, (∀ x y, Bf y x = starRingEnd ℂ (Bf x y)) ∧ (∀ x, x ≠ 0 → 0 < (Bf x x).re) ∧
      ∀ g x y, Bf (T g x) (T g y) = Bf x y := by
  refine ⟨LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) (fun φ ψ => inner ℂ (p (j φ)) (p (j ψ)))
    (fun _ _ _ => by rw [map_add, map_add, inner_add_left]) (fun _ _ _ => by rw [map_smul, map_smul, inner_smul_left]; rfl)
    (fun _ _ _ => by rw [map_add, map_add, inner_add_right]) (fun _ _ _ => by rw [map_smul, map_smul, inner_smul_right]; rfl),
    fun x y => (inner_conj_symm (p (j y)) (p (j x))).symm,
    fun x hx => re_inner_self_pos (𝕜 := ℂ).2 fun h => hx (hj x (h1 _ (hP x) (by rw [h, inner_zero_left]))), fun g x y => ?_⟩
  change inner ℂ (p (j (T g x))) (p (j (T g y))) = inner ℂ (p (j x)) (p (j y))
  rw [hT, hT]
  exact hS g _ _ (hP x) (hP y)

private theorem exists_form {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ} (π : CuspSub E a)
    (h0 : ∀ φ ∈ π.V, lie E a (oneL E a) φ = 0) (w : HeightOneSpectrum (𝓞 E)) :
    ∃ Bf : π.V →ₗ⋆[ℂ] π.V →ₗ[ℂ] ℂ, (∀ x y, Bf y x = starRingEnd ℂ (Bf x y)) ∧ (∀ x, x ≠ 0 → 0 < (Bf x x).re) ∧
      ∀ g x y, Bf (π.locRep w g x) (π.locRep w g y) = Bf x y := by
  obtain ⟨j, hj⟩ : ∃ j : π.V →ₗ[ℂ] cuspForms E a, ∀ φ : π.V, ofCusp E a (j φ) = φ.1 ∧ j φ ∈ carrier π :=
    ⟨(carrier π).subtype ∘ₗ (carrierEq π).symm.toLinearMap, fun φ => ⟨by
      have := coe_carrierEq π ((carrierEq π).symm φ)
      rw [LinearEquiv.apply_symm_apply] at this
      exact this.symm, ((carrierEq π).symm φ).2⟩⟩
  have hc : ∀ φ, j φ ∈ centralCuspForms E a := fun φ => carrier_le_central π h0 (hj φ).2
  have hτ : ∀ g φ, j (π.locRep w g φ) = finRepCusp E a (locGL E a w g) (j φ) := fun g φ => by
    refine ofCusp_injective ?_
    rw [(hj _).1, ofCusp_τ, (hj _).1]
    rfl
  have hinj : ∀ x, j x = 0 → x = 0 := fun x h1 => by
    have := (hj x).1
    rw [h1, map_zero] at this
    exact Subtype.ext this.symm
  exact exists_pullback j (CuspidalSpectrum.cuspToL2 (Measure.haar : Measure (Reduction.normOneGL E a)))
    (fun g => π.locRep w g) (fun g => finRepCusp E a (locGL E a w g)) (· ∈ centralCuspForms E a) hc
    (fun x hx h => eq_zero_of_petersson_inner_self_eq_zero _ hx h) hinj hτ
    fun g x y hx hy => petersson_inner_finiteAdelic_invariant _ _ hx hy

private theorem exists_twist {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ} (ha : 1 ≤ a) (σ : CuspSub E a) :
    ∃ (χ : HChar E) (s : ℝ), (∀ φ ∈ (σ.twist χ).V, lie E a (oneL E a) φ = 0) ∧
      ∀ w : HeightOneSpectrum (𝓞 E), χ.UnrAt w ∧ ‖((χ.val w : ℂˣ) : ℂ)‖ = (Ideal.absNorm w.asIdeal : ℝ) ^ s := by
  have hd : ((a : ℂ) * (Module.finrank ℚ E : ℂ)) ≠ 0 :=
    mul_ne_zero (Nat.cast_ne_zero.2 (by omega)) (Nat.cast_ne_zero.2 Module.finrank_pos.ne')
  set c : ℂ := GlobalTheory.ResW.cex (⟨a, σ⟩ : GlobalTheory.ResW.Letter E) with hc
  obtain ⟨χ, hz, hv, -, -⟩ := GlobalTheory.T.exists_idelic_absValue_cpow_character E (-c / ((a : ℂ) * (Module.finrank ℚ E : ℂ)))
  refine ⟨χ, -(-c / ((a : ℂ) * (Module.finrank ℚ E : ℂ))).re, ?_, fun w => ⟨(hv w).1, ?_⟩⟩
  · rintro _ ⟨φ, hφ, rfl⟩
    have e1 : GlobalTheory.ResW.zc E a φ = c • φ := (GlobalTheory.T.cuspidalLetter_centralExponent_properties E ⟨a, σ⟩).1 φ hφ
    have e2 : GlobalTheory.ResW.zc E a (mulChi a χ φ) = 0 := by
      rw [hz, e1, ← add_smul, mul_div_cancel₀ _ hd, add_neg_cancel, zero_smul, map_zero]
    exact e2
  · have hq : 0 < Ideal.absNorm w.asIdeal := zero_lt_one.trans (NumberField.HeightOneSpectrum.one_lt_absNorm w)
    rw [(hv w).2, Complex.norm_natCast_cpow_of_pos hq, Complex.neg_re]

theorem satBd : SatBd := by
  intro K _ _ _ n σ
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine ⟨0, fun w B hB b hb => ?_⟩
    have h0 : Multiset.card B = 0 := GlobalTheory.LFun.HasSatGL.card hB
    rw [Multiset.card_eq_zero.1 h0] at hb
    exact absurd hb (Multiset.notMem_zero b)
  obtain ⟨χ, s, h0, hχ⟩ := exists_twist hn σ
  set A : ℝ := ((n * n + n : ℕ) : ℝ) with hA
  have hA0 : 0 ≤ A := Nat.cast_nonneg _
  have hAn : 0 ≤ A * n := by positivity
  refine ⟨A * n + A + |s|, fun w B hB b hb => ?_⟩
  obtain ⟨Bf, f1, f2, f3⟩ := exists_form (σ.twist χ) h0 w
  set q : ℝ := (Ideal.absNorm w.asIdeal : ℝ) with hq
  have hq1 : 1 ≤ q := by
    rw [hq]
    exact_mod_cast (NumberField.HeightOneSpectrum.one_lt_absNorm w).le
  have hq0 : 0 < q := by linarith
  have hB' : GlobalTheory.LFun.HasSatGL w ((σ.twist χ).locRep w) (B.map (· * χ.val w)) := CG.HasSat.twist hB (hχ w).1
  obtain ⟨k1, k2⟩ := GlobalTheory.HenQ.local_bound K w n _ _ Bf f1 f2 f3 _ hB' _ (Multiset.mem_map_of_mem _ hb)
  rw [← pow_mul] at k2
  rw [← Real.rpow_natCast] at k1 k2
  replace k1 : ‖((b * χ.val w : ℂˣ) : ℂ)‖ ≤ q ^ A := k1
  replace k2 : ‖(((b * χ.val w)⁻¹ : ℂˣ) : ℂ)‖ ≤ q ^ (((n * n + n) * n : ℕ) : ℝ) := k2
  have eA : (((n * n + n) * n : ℕ) : ℝ) = A * n := by simp [hA]
  rw [eA] at k2
  have hc : ‖((χ.val w : ℂˣ) : ℂ)‖ = q ^ s := (hχ w).2
  have hcpos : 0 < q ^ s := Real.rpow_pos_of_pos hq0 s
  constructor
  · have e : (b : ℂ) = ((b * χ.val w : ℂˣ) : ℂ) * (((χ.val w)⁻¹ : ℂˣ) : ℂ) := by
      rw [← Units.val_mul, mul_inv_cancel_right]
    rw [e, norm_mul, Units.val_inv_eq_inv_val, norm_inv, hc, ← Real.rpow_neg hq0.le]
    calc _ ≤ q ^ A * q ^ (-s) := mul_le_mul_of_nonneg_right k1 (by positivity)
      _ = q ^ (A + -s) := (Real.rpow_add hq0 _ _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hq1 (by linarith [neg_le_abs s])
  · have e : ((b⁻¹ : ℂˣ) : ℂ) = (((b * χ.val w)⁻¹ : ℂˣ) : ℂ) * ((χ.val w : ℂˣ) : ℂ) := by
      rw [← Units.val_mul, mul_inv, inv_mul_cancel_right]
    rw [e, norm_mul, hc]
    calc _ ≤ q ^ (A * n) * q ^ s := mul_le_mul_of_nonneg_right k2 hcpos.le
      _ = q ^ (A * n + s) := (Real.rpow_add hq0 _ _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hq1 (by linarith [le_abs_self s])

end UpperTheory.V.Z.Inf
