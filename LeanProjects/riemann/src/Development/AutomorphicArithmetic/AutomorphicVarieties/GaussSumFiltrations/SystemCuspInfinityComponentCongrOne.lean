import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.EvenPos
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.SlashAddSmulPow
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.HilbertSlashUnnormalizedConstMul
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.HilbertSlashRationalMatrixProperties
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.ExistsDifferentGeneratorTotallyPositiveTranslate
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.ExistsInGScalarMulAndAbsNormDetMulAbsFEq
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.HasQExpansionAffineTranslateCoeff
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.HilbertQExpPadicBoundAlgebraProperties
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ScalarStabilizers.FinSupp
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

namespace GlobalTheory.HilbertThetaSeries.CuspOne

theorem pow_sub_one_small (p : ℕ) [Fact p.Prime] (r : ℚ) (hr : ‖(r : ℚ_[p])‖ = 1) (k : ℕ) (hk : p - 1 ∣ k) :
    ‖((r : ℚ_[p]) ^ k - 1)‖ ≤ (p : ℝ)⁻¹ := by
  set x : ℤ_[p] := ⟨(r : ℚ_[p]), hr.le⟩ with hx
  have hxu : ‖x‖ = 1 := hr
  have h1 : PadicInt.toZMod x ≠ 0 := by
    intro h0
    have : x ∈ IsLocalRing.maximalIdeal ℤ_[p] := by rw [← PadicInt.ker_toZMod]; exact h0
    rw [IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits] at this
    linarith
  obtain ⟨m, rfl⟩ := hk
  have h2 : PadicInt.toZMod (x ^ ((p - 1) * m) - 1) = 0 := by
    rw [map_sub, map_pow, map_one, pow_mul, ZMod.pow_card_sub_one_eq_one h1, one_pow, sub_self]
  have h3 : x ^ ((p - 1) * m) - 1 ∈ IsLocalRing.maximalIdeal ℤ_[p] := by rw [← PadicInt.ker_toZMod]; exact h2
  rw [IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits] at h3
  have h4 : ‖x ^ ((p - 1) * m) - 1‖ ≤ (p : ℝ) ^ (-1 : ℤ) :=
    (PadicInt.norm_le_pow_iff_norm_lt_pow_add_one _ (-1)).2 (by simpa using h3)
  have h5 : ((x ^ ((p - 1) * m) - 1 : ℤ_[p]) : ℚ_[p]) = (r : ℚ_[p]) ^ ((p - 1) * m) - 1 := by
    push_cast; rfl
  rw [← h5, ← PadicInt.norm_def]
  simpa using h4

theorem norm_qbar_rat (p : ℕ) [Fact p.Prime] (q : ℚ) : ‖((q : ℚ) : Qbar p)‖ = ‖(q : ℚ_[p])‖ := by
  have : ((q : ℚ) : Qbar p) = algebraMap ℚ_[p] (Qbar p) (q : ℚ_[p]) := by simp
  rw [this]
  exact PadicAlgCl.norm_extends p _

theorem toFin_aff {F : Type} [Field F] [NumberField F] (ξ : Fˣ) :
    toFin (aff ξ 0) = aff (Units.map (algebraMap F (Af F)).toMonoidHom ξ) 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [toFin, aff]

theorem aff_mul {R : Type} [CommRing R] (a b : Rˣ) : aff (a * b) 0 = aff a 0 * aff b 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [aff, Matrix.mul_apply, Fin.sum_univ_succ]

theorem det_aff {R : Type} [CommRing R] (a : Rˣ) : (aff a 0).val.det = a := by
  simp [aff, Matrix.det_fin_two]

theorem weightSlash_hilbertAffine_apply {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (ξ : Fˣ) (g : Hn F → ℂ) :
    sl0 k (toInf (aff ξ 0)) g = fun z => g (act (toInf (aff ξ 0)) z) := by
  funext z
  simp [sl0, toInf, cmp, aff, UpperHalfPlane.denom]

theorem cusp_inf_one : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (p : ℕ) [Fact p.Prime] (ι : Qbar p ≃+* ℂ), p ≠ 2 → ∀ δ : F, IsDel p δ → ∀ (k : ℕ), p - 1 ∣ k → ∀ (Ψ : GL (Fin 2) (Af F) → Hn F → ℂ), Sys k Ψ → ∀ (y y' z : (Af F)ˣ) (f : Hn F → ℂ), AtP p δ y' → (∀ γ, InG p δ γ → Small ι (p : ℝ)⁻¹ (sl0 k (toInf γ) f - 1)) → ∀ (γ : GL (Fin 2) F) (u : GL (Fin 2) (Af F)), TP γ.val.det → u ∈ KLev F 2 1 → toFin γ * aff y 0 = Matrix.GeneralLinearGroup.scalar (Fin 2) z * aff y' 0 * u → Ψ (aff y 0) = sl k (toInf γ) (((absF y' ^ ((k : ℝ) / 2) : ℝ) : ℂ) • f) → Small ι (p : ℝ)⁻¹ ((((absF y ^ ((k : ℝ) / 2) : ℝ) : ℂ))⁻¹ • Ψ (aff y 0) - 1) := by
  intro F _ _ _ p _ ι hp2 δ hδ k hk Ψ _ y y' z f hy' hf γ u hγ hu hmat hΨ
  have hpp : p.Prime := Fact.out
  have hkev : Even k := by
    have ho : Odd p := hpp.odd_of_ne_two hp2
    have : Even (p - 1) := Nat.Odd.sub_odd ho odd_one
    exact even_iff_two_dvd.2 ((even_iff_two_dvd.1 this).trans hk)
  have R := fun (g : Hn F → ℂ) => GlobalTheory.HilbertThetaSeries.RatSlash.rat_slash F k g
  have hrhom : ∀ v (x : F), rhom x v = reAt v x := (R f).1
  obtain ⟨-, hdel⟩ := GlobalTheory.T.exists_different_generator_totallyPositive_translate F p hpp
  obtain ⟨ξ, hξTP, hξy⟩ := hdel δ hδ y
  set ξa : (Af F)ˣ := Units.map (algebraMap F (Af F)).toMonoidHom ξ with hξa
  set γ₁ : GL (Fin 2) F := γ * (aff ξ 0)⁻¹ with hγ₁
  have hγeq : γ = γ₁ * aff ξ 0 := by simp [γ₁]
  have hmat₁ : toFin γ₁ * aff (ξa * y) 0 = Matrix.GeneralLinearGroup.scalar (Fin 2) z * aff y' 0 * u := by
    rw [← hmat, aff_mul, hγ₁, map_mul, map_inv, toFin_aff]
    simp only [← hξa, mul_assoc, inv_mul_cancel_left]
  have hdet₁ : γ₁.val.det = γ.val.det / ξ := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply, hγ₁, map_mul, map_inv, Units.val_mul, Units.val_inv_eq_inv_val,
      Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply, det_aff, div_eq_mul_inv]
  have hTP₁ : TP γ₁.val.det := fun v => by
    have h1 : γ.val.det = γ₁.val.det * ξ := by rw [hdet₁, div_mul_cancel₀ _ ξ.ne_zero]
    have h2 := hγ v
    rw [h1, ← hrhom, map_mul, Pi.mul_apply, hrhom, hrhom] at h2
    exact (mul_pos_iff_of_pos_right (hξTP v)).1 h2
  obtain ⟨-, -, hgp⟩ := GlobalTheory.T.exists_inG_scalar_mul_and_abs_norm_det_mul_absF_eq F p δ hδ
  obtain ⟨η, r, hInG, hr0, hrn, hnorm⟩ := hgp (ξa * y) y' z γ₁ u hξy hy' hTP₁ hu hmat₁
  set γ₂ : GL (Fin 2) F := Matrix.GeneralLinearGroup.scalar (Fin 2) η * γ₁ with hγ₂
  set G : Hn F → ℂ := sl0 k (toInf γ₂) f with hGdef
  have hG := hf γ₂ hInG
  have hPos₁ : Pos (toInf γ₁) := ((R f).2.1 γ₁).1.2 hTP₁
  have hPosξ : Pos (toInf (aff ξ 0)) := ((R f).2.1 _).1.2 (by rw [det_aff]; exact hξTP)
  set c' : ℂ := ((absF y' ^ ((k : ℝ) / 2) : ℝ) : ℂ) with hc'
  set Nd : ℝ := |((Algebra.norm ℚ γ₂.val.det : ℚ) : ℝ)| with hNd
  set Nξ : ℝ := |((Algebra.norm ℚ (aff ξ 0).val.det : ℚ) : ℝ)| with hNξ
  have e1 : sl k (toInf γ) (c' • f) = sl k (toInf (aff ξ 0)) (sl k (toInf γ₁) (c' • f)) := by
    rw [hγeq, map_mul]
    exact (GlobalTheory.HilbertThetaSeries.SlashCocycle.slash_cocycle F k _ _ _ hPos₁ hPosξ).2.2.2.1
  have e2 : sl k (toInf γ₁) (c' • f) = sl k (toInf γ₂) (c' • f) := by
    have h := ((R (c' • f)).2.2.1 hkev (Units.map (rhom (F := F)).toMonoidHom η) (toInf γ₁) hPos₁).2
    rw [← (R f).2.2.2.1 η, ← map_mul] at h
    exact h.symm
  have e3 : sl k (toInf γ₂) (c' • f) = ((Nd ^ ((k : ℝ) / 2) : ℝ) : ℂ) • (c' • G) := by
    rw [((R (c' • f)).2.1 γ₂).2, (GlobalTheory.HilbertThetaSeries.slash_add_smul_pow F k 1 (toInf γ₂) f f c').2.1]
  have e4 : sl k (toInf (aff ξ 0)) (((Nd ^ ((k : ℝ) / 2) : ℝ) : ℂ) • (c' • G)) =
      (((Nd ^ ((k : ℝ) / 2) : ℝ) : ℂ) * c' * ((Nξ ^ ((k : ℝ) / 2) : ℝ) : ℂ)) • sl0 k (toInf (aff ξ 0)) G := by
    rw [smul_smul, (GlobalTheory.HilbertThetaSeries.slash_add_smul_pow F k 1 (toInf (aff ξ 0)) G G _).2.2.2.2.1, ((R G).2.1 (aff ξ 0)).2, smul_smul]

  obtain ⟨hA0, hAmul, -, hAprod⟩ := UpperTheory.V.Sd.Hm.absf F
  have hNξ' : Nξ * absF ξa = 1 := by
    rw [hNξ, det_aff, ← ((R f).2.2.2.2 (ξ : F)).1, Finset.abs_prod]
    exact hAprod ξ
  have hreal : Nd ^ ((k : ℝ) / 2) * absF y' ^ ((k : ℝ) / 2) * Nξ ^ ((k : ℝ) / 2) =
      ((r : ℝ) ^ k) * absF y ^ ((k : ℝ) / 2) := by
    have h0 : Nd * absF y' * Nξ = (r : ℝ) ^ 2 * absF y := by
      rw [hNd, hnorm, hAmul]
      calc (r : ℝ) ^ 2 * (absF ξa * absF y) * Nξ = (r : ℝ) ^ 2 * absF y * (Nξ * absF ξa) := by ring
        _ = _ := by rw [hNξ', mul_one]
    have hNd0 : 0 ≤ Nd := abs_nonneg _
    have hNξ0 : 0 ≤ Nξ := abs_nonneg _
    have hy'0 : 0 ≤ absF y' := (hA0 y').le
    rw [← Real.mul_rpow hNd0 hy'0, ← Real.mul_rpow (mul_nonneg hNd0 hy'0) hNξ0, h0,
      Real.mul_rpow (sq_nonneg _) (hA0 y).le, ← Real.rpow_natCast ((r : ℝ)) 2, ← Real.rpow_mul (by exact_mod_cast hr0.le)]
    congr 1
    rw [← Real.rpow_natCast]
    congr 1
    push_cast; ring
  have hy0 : ((absF y ^ ((k : ℝ) / 2) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.rpow_pos_of_pos (hA0 y) _).ne'
  set H : Hn F → ℂ := sl0 k (toInf (aff ξ 0)) G with hHdef
  set c : ℂ := ((r : ℚ) : ℂ) ^ k with hcdef
  have key : (((absF y ^ ((k : ℝ) / 2) : ℝ) : ℂ))⁻¹ * (((Nd ^ ((k : ℝ) / 2) : ℝ) : ℂ) * c' * ((Nξ ^ ((k : ℝ) / 2) : ℝ) : ℂ)) = c := by
    rw [hc', inv_mul_eq_iff_eq_mul₀ hy0]
    have := congrArg (fun x : ℝ => (x : ℂ)) hreal
    push_cast at this ⊢
    rw [this, hcdef]
    ring
  have hΨ' : (((absF y ^ ((k : ℝ) / 2) : ℝ) : ℂ))⁻¹ • Ψ (aff y 0) = c • H := by
    rw [hΨ, e1, e2, e3, e4, smul_smul, key]
  rw [hΨ']

  obtain ⟨a, ha, hb⟩ := hG
  have S1 : Small ι (p : ℝ)⁻¹ (H - 1) := by
    have hq := GlobalTheory.T.hasQExpansion_affineTranslate_coeff F k (G - 1) a ξ 0 hξTP ha
    have hH1 : sl0 k (toInf (aff ξ 0)) (G - 1) = H - 1 := by
      rw [hHdef, weightSlash_hilbertAffine_apply, weightSlash_hilbertAffine_apply]; funext w; simp
    rw [hH1] at hq
    refine ⟨_, hq, fun x => ?_⟩
    simpa [et] using hb (x / ξ)
  have Q := GlobalTheory.T.hilbertQExp_padicBound_algebra_properties F p ι
  have hc : ‖ι.symm c‖ = 1 := by
    rw [hcdef, map_pow, map_ratCast, norm_pow, norm_qbar_rat, hrn, one_pow]
  have hc1 : ‖ι.symm (c - 1)‖ ≤ (p : ℝ)⁻¹ := by
    have : ι.symm (c - 1) = (((r ^ k - 1 : ℚ)) : Qbar p) := by
      rw [hcdef, map_sub, map_pow, map_ratCast, map_one]; push_cast; rfl
    rw [this, norm_qbar_rat]
    have h := pow_sub_one_small p r hrn k hk
    push_cast
    exact h
  have hS2 := (Q _ _ (H - 1) (H - 1) c S1 S1).2.2.1
  have hS3 := (Q _ _ (H - 1) (H - 1) (c - 1) S1 S1).2.2.2.2.2
  have hsum := (Q _ _ _ _ 0 hS2 hS3).1
  have heq : c • H - 1 = c • (H - 1) + fun _ => c - 1 := by
    funext w; simp; ring
  rw [heq]
  exact (Q _ _ _ _ 0 hsum S1).2.2.2.1 (by rw [hc, one_mul]; exact max_le le_rfl hc1)

end GlobalTheory.HilbertThetaSeries.CuspOne

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.system_cusp_infinity_component_congr_one : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (p : ℕ) [Fact p.Prime] (ι : Qbar p ≃+* ℂ), p ≠ 2 → ∀ δ : F, IsDel p δ → ∀ (k : ℕ), p - 1 ∣ k → ∀ (Ψ : GL (Fin 2) (Af F) → Hn F → ℂ), Sys k Ψ → ∀ (y y' z : (Af F)ˣ) (f : Hn F → ℂ), AtP p δ y' → (∀ γ, InG p δ γ → Small ι (p : ℝ)⁻¹ (sl0 k (toInf γ) f - 1)) → ∀ (γ : GL (Fin 2) F) (u : GL (Fin 2) (Af F)), TP γ.val.det → u ∈ KLev F 2 1 → toFin γ * aff y 0 = Matrix.GeneralLinearGroup.scalar (Fin 2) z * aff y' 0 * u → Ψ (aff y 0) = sl k (toInf γ) (((absF y' ^ ((k : ℝ) / 2) : ℝ) : ℂ) • f) → Small ι (p : ℝ)⁻¹ ((((absF y ^ ((k : ℝ) / 2) : ℝ) : ℂ))⁻¹ • Ψ (aff y 0) - 1) := by
  first | exact @GlobalTheory.HilbertThetaSeries.CuspOne.cusp_inf_one | exact GlobalTheory.HilbertThetaSeries.CuspOne.cusp_inf_one | (intros; apply GlobalTheory.HilbertThetaSeries.CuspOne.cusp_inf_one <;> assumption)
