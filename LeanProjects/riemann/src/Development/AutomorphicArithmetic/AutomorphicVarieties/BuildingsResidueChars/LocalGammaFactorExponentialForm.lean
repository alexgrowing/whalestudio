import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.AdjointEta.EtaOK
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.PolFacts

open NumberField IsDedekindDomain Polynomial Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.LocGL GlobalTheory.SplitWeil GlobalTheory.SmGL
open UpperTheory.V.Z.Gam UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter GlobalTheory.HenQ UpperTheory.V.Z.Inf UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.Ad
open GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.LocalField
open GroundTheory.Automorphic.GodementSection (localChar)
open Ad3P.DihedralUnramifiedPlaces (toH)
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

namespace UpperTheory.V.T.GamFac

section Loc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

private theorem lt_one_iff {x : k} (hx : x ≠ 0) : ValuativeRel.valuation k x < 1 ↔ 1 ≤ ord x := by
  have h := mem_valBall_iff_le_ord (n := 1) hx
  rwa [mem_valBall_one_iff] at h

private theorem le_one_iff {x : k} (hx : x ≠ 0) : ValuativeRel.valuation k x ≤ 1 ↔ 0 ≤ ord x := by
  have h := mem_valBall_iff_le_ord (n := 0) hx
  rwa [mem_valBall_zero_iff, Valuation.mem_integer_iff] at h

private theorem val_eq_one_iff {x : k} (hx : x ≠ 0) : ValuativeRel.valuation k x = 1 ↔ ord x = 0 := by
  constructor
  · intro h
    have h1 := (le_one_iff hx).1 h.le
    have h2 : ¬ 1 ≤ ord x := fun h3 => absurd ((lt_one_iff hx).2 h3) (by rw [h]; exact lt_irrefl _)
    omega
  · intro h
    refine le_antisymm ((le_one_iff hx).2 h.ge) (not_lt.1 fun h3 => ?_)
    have := (lt_one_iff hx).1 h3
    omega

private theorem unram_iff (μ : kˣ →* ℂˣ) : IsUnram μ ↔ IsUnramifiedChar μ := by
  rw [isUnramifiedChar_iff]
  exact ⟨fun h u hu => h u ((val_eq_one_iff u.ne_zero).2 hu), fun h u hu => h u ((val_eq_one_iff u.ne_zero).1 hu)⟩

private theorem ord_unif_eq : ord ((UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.unif k : kˣ) : k) = 1 := by
  obtain ⟨h1, h2⟩ := (polFacts k).1
  have a := (lt_one_iff (UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.unif k).ne_zero).1 h1
  have b := h2 _ ((lt_one_iff (unifUnit k).ne_zero).2 ord_unifUnit.ge)
  have c : ValuativeRel.valuation k ((unifUnit k * (UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.unif k)⁻¹ : kˣ) : k) ≤ 1 := by
    rw [Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀]
    exact mul_inv_le_one_of_le₀ b zero_le'
  have d := (le_one_iff (Units.ne_zero _)).1 c
  rw [ord_units_mul, ord_units_inv, ord_unifUnit] at d
  omega

end Loc

private theorem alg (a A q X : ℂ) (n : ℤ) (hA : A ≠ 0) (hq : q ≠ 0) (hX : X ≠ 0) :
    a * X ^ n * (1 - A⁻¹ * (q * X)⁻¹)⁻¹ / (1 - A * X)⁻¹ =
      -(A * q * a) * X ^ (n + 1) * (1 - A * X) / (1 - A * (q * X)) := by
  have hy : A * (q * X) ≠ 0 := mul_ne_zero hA (mul_ne_zero hq hX)
  have e : (1 - A⁻¹ * (q * X)⁻¹)⁻¹ = -(A * (q * X)) / (1 - A * (q * X)) := by
    rw [← mul_inv]
    by_cases h : A * (q * X) = 1
    · simp [h]
    · have h' : 1 - A * (q * X) ≠ 0 := sub_ne_zero.2 (Ne.symm h)
      have h'' : 1 - (A * (q * X))⁻¹ ≠ 0 := by
        intro h3
        apply h
        have := sub_eq_zero.1 h3
        rw [eq_comm, inv_eq_one] at this
        exact this
      rw [eq_div_iff h', inv_mul_eq_div, div_eq_iff h'']
      field_simp
      ring
  rw [e, zpow_add_one₀ hX, div_inv_eq_mul]
  ring

private theorem zpow_qpow (n : ℕ) (hn : 1 < n) (m : ℤ) (s : ℂ) :
    ((n : ℂ) ^ (-s)) ^ m = Complex.exp (((-(m * Real.log n) : ℝ) : ℂ) * s) := by
  have h0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  rw [Complex.cpow_def_of_ne_zero h0, ← Complex.exp_int_mul]
  congr 1
  push_cast
  ring

end UpperTheory.V.T.GamFac

open UpperTheory.V.T.GamFac in
theorem UpperTheory.local_gamma_factor_exponential_form :
    ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F]
        (ψ : AddChar F Circle) (μ : Fˣ →* ℂˣ), Continuous μ →
        ∃ (c : ℂ) (t : ℝ), ∀ s : ℂ, Ad3.gam ψ μ s = fac c t (residueCard F : ℝ) (lin μ) s := by
  intro F _ _ _ _ _ _ ψ μ _
  obtain ⟨a, n, hε⟩ := exists_localEpsilon_eq_mul_zpow (χ := μ) (ψ := ψ)
  have hq1 : 1 < residueCard F := one_lt_residueCard
  have hq0 : (residueCard F : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  by_cases h : IsUnram μ
  · have hu := (unram_iff μ).1 h
    have hu' : IsUnramifiedChar μ⁻¹ := isUnramifiedChar_iff.2 fun u hu2 => by
      rw [MonoidHom.inv_apply, isUnramifiedChar_iff.1 hu u hu2, inv_one]
    have hval : μ (UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.unif F) = μ (unifUnit F) :=
      quasiChar_apply_eq_of_isUnramified hu ord_unif_eq
    set A : ℂ := ((μ (unifUnit F) : ℂˣ) : ℂ) with hA
    have hA0 : A ≠ 0 := Units.ne_zero _
    refine ⟨-(A * (residueCard F : ℂ) * a), -((n + 1 : ℤ) * Real.log (residueCard F)), fun s => ?_⟩
    have hX : (residueCard F : ℂ) ^ (-s) ≠ 0 := by
      rw [Complex.cpow_def_of_ne_zero hq0]
      exact Complex.exp_ne_zero _
    have e1 : (residueCard F : ℂ) ^ (1 - s) = (residueCard F : ℂ) * (residueCard F : ℂ) ^ (-s) := by
      rw [sub_eq_add_neg, Complex.cpow_add _ _ hq0, Complex.cpow_one]
    have e2 : (residueCard F : ℂ) ^ (-(1 - s)) = ((residueCard F : ℂ) * (residueCard F : ℂ) ^ (-s))⁻¹ := by
      rw [Complex.cpow_neg, e1]
    have e3 : ((μ⁻¹ (unifUnit F) : ℂˣ) : ℂ) = A⁻¹ := by
      rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val]
    have e4 : lin μ = 1 - C A * X := by
      rw [lin, if_pos h, hval]
    rw [Ad3.gam, fac, hε s, localLFactor_of_isUnramified hu, localLFactor_of_isUnramified hu', e2, e3,
      Complex.ofReal_natCast, e4, alg _ _ _ _ _ hA0 hq0 hX, zpow_qpow _ hq1]
    simp only [eval_sub, eval_one, eval_mul, eval_C, eval_X, e1]
  · have hu : ¬ IsUnramifiedChar μ := fun h2 => h ((unram_iff μ).2 h2)
    have hu' : ¬ IsUnramifiedChar μ⁻¹ := fun h2 => hu (isUnramifiedChar_iff.2 fun u hu2 => by
      have := isUnramifiedChar_iff.1 h2 u hu2
      rwa [MonoidHom.inv_apply, inv_eq_one] at this)
    refine ⟨a, -(n * Real.log (residueCard F)), fun s => ?_⟩
    have e4 : lin μ = 1 := by rw [lin, if_neg h]
    rw [Ad3.gam, fac, hε s, localLFactor_of_not_isUnramified hu, localLFactor_of_not_isUnramified hu', e4,
      zpow_qpow _ hq1]
    simp
