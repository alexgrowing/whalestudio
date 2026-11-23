import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.PsiEDef
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.ExistsDenOfLeOne

noncomputable section

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum ValuativeRel Polynomial

namespace Formalism.L2.SG.Pf.LocalDenominators

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {sig : E →ₐ[F] E} {p : HeightOneSpectrum (𝓞 F)} (A : Formalism.MainNotions.S.Loc.LocAt F E sig p)

theorem val_iF_le (a b : F) :
    valuation A.Fp (A.ιF a) ≤ valuation A.Fp (A.ιF b) ↔ p.valuation F a ≤ p.valuation F b := by
  first
  | exact ((Valuation.Compatible.vle_iff_le (v := valuation A.Fp) _ _).symm).trans (A.val a b)
  | exact ((Valuation.Compatible.vle_iff_le _ _).symm).trans (A.val a b)

theorem iF_mem_iff (a : F) : A.ιF a ∈ 𝒪[A.Fp] ↔ p.valuation F a ≤ 1 := by
  have h := val_iF_le A a 1
  rw [map_one, map_one, map_one] at h
  rw [Valuation.mem_integer_iff]
  first
  | exact h
  | simpa using h

theorem val_int_le (t : 𝓞 F) : p.valuation F (t : F) ≤ 1 := p.valuation_le_one t

theorem val_unit {t : 𝓞 F} (ht : t ∉ p.asIdeal) : p.valuation F (t : F) = 1 := by
  refine le_antisymm (val_int_le t) (not_lt.mp fun h => ht ?_)
  first
  | exact (p.valuation_lt_one_iff_mem t).mp h
  | exact (HeightOneSpectrum.valuation_lt_one_iff_mem (K := F) p t).mp h

theorem iF_unit {t : 𝓞 F} (ht : t ∉ p.asIdeal) : valuation A.Fp (A.ιF (t : F)) = 1 := by
  have h1 := (val_iF_le A (t : F) 1).mpr (by rw [map_one, val_unit ht])
  have h2 := (val_iF_le A 1 (t : F)).mpr (by rw [map_one, val_unit ht])
  rw [map_one, map_one] at h1 h2
  exact le_antisymm h1 h2

theorem exists_den {a : F} (ha : p.valuation F a ≤ 1) :
    ∃ t : 𝓞 F, t ∉ p.asIdeal ∧ ∃ y : 𝓞 F, (y : F) = (t : F) * a := by
  obtain ⟨r, s, hs, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 F) a
  have hs0 : s ≠ 0 := nonZeroDivisors.ne_zero hs
  have hs0' : ((s : 𝓞 F) : F) ≠ 0 := by exact_mod_cast hs0
  rw [map_div₀, valuation_of_algebraMap, valuation_of_algebraMap] at ha
  have hpos : 0 < p.intValuation s := by
    rw [zero_lt_iff]
    exact (intValuation_ne_zero p s hs0)
  have hrs : p.intValuation r ≤ p.intValuation s := by
    rwa [div_le_one₀ hpos] at ha
  have hr : r ∈ p.asIdeal ^ Formalism.HermitianLattices.Ext.L3.vF p.asIdeal s := by
    rw [← intValuation_le_pow_iff_mem]
    exact hrs.trans ((intValuation_le_pow_iff_mem p s _).2
      (Formalism.HermitianLattices.Ext.L3.localValuationFiltration.mem_pow_vF p.isMaximal hs0))
  obtain ⟨t, ht, hmul⟩ := Formalism.L2.SG.Pf.G2.exists_mul_mem_span p.isMaximal hs0
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 (hmul r hr)
  refine ⟨t, ht, y, ?_⟩
  have h := congrArg (algebraMap (𝓞 F) F) hy
  simp only [map_mul] at h
  field_simp
  rw [mul_comm] at h
  simpa [mul_comm] using h

theorem iE_int {y : E} (hy : IsIntegral ℤ y) : A.ιE y ∈ A.O := by
  refine (A.O_def _).mpr ?_
  first
  | exact (map_isIntegral_int A.ιE hy).tower_top
  | exact IsIntegral.tower_top (map_isIntegral_int A.ιE hy)

theorem iE_alg (a : F) : A.ιE (algebraMap F E a) = algebraMap A.Fp A.Ep (A.ιF a) := A.compat a

theorem alg_mem_O {z : A.Fp} (hz : z ∈ 𝒪[A.Fp]) : algebraMap A.Fp A.Ep z ∈ A.O := by
  refine (A.O_def _).mpr ?_
  exact isIntegral_algebraMap (x := (⟨z, hz⟩ : 𝒪[A.Fp]))

instance : Nontrivial A.Ep := Module.nontrivial_of_finrank_pos (R := A.Fp) (by rw [A.rank]; norm_num)

theorem mem_of_alg_mem_O {z : A.Fp} (hz : algebraMap A.Fp A.Ep z ∈ A.O) : z ∈ 𝒪[A.Fp] := by
  have h1 := (A.O_def _).mp hz
  have h2 : IsIntegral 𝒪[A.Fp] z :=
    (isIntegral_algHom_iff (IsScalarTower.toAlgHom 𝒪[A.Fp] A.Fp A.Ep)
      (algebraMap A.Fp A.Ep).injective).mp h1
  first
  | exact (Valuation.integer.integers _).mem_of_integral h2
  | simpa using (Valuation.integer.integers _).mem_of_integral h2

variable (hσ : ∀ e, sig (sig e) = e) (hfix : ∀ y : E, sig y = y → y ∈ (algebraMap F E).range)
include hσ hfix

theorem iE_sig_mem {x : E} (hx : A.ιE x ∈ A.O) : A.ιE (sig x) ∈ A.O := by
  rw [← A.cj_ιE]
  exact (A.O_def _).mpr
    (((A.O_def _).mp hx).map ((A.cj : A.Ep →ₐ[A.Fp] A.Ep).restrictScalars 𝒪[A.Fp]))

theorem iE_mem_O_iff (x : E) :
    A.ιE x ∈ A.O ↔ ∃ s : 𝓞 F, s ∉ p.asIdeal ∧ IsIntegral ℤ (algebraMap F E (s : F) * x) := by
  constructor
  · intro hx

    obtain ⟨t, ht⟩ := hfix (x + sig x) (by rw [map_add, hσ, add_comm])
    obtain ⟨n, hn⟩ := hfix (x * sig x) (by rw [map_mul, hσ, mul_comm])
    have hxs := iE_sig_mem A hσ hfix hx
    have htO : A.ιF t ∈ 𝒪[A.Fp] := by
      apply mem_of_alg_mem_O A
      rw [← iE_alg, ht, map_add]; exact A.O.add_mem hx hxs
    have hnO : A.ιF n ∈ 𝒪[A.Fp] := by
      apply mem_of_alg_mem_O A
      rw [← iE_alg, hn, map_mul]; exact A.O.mul_mem hx hxs
    obtain ⟨s₁, hs₁, y₁, hy₁⟩ := exists_den ((iF_mem_iff A t).1 htO)
    obtain ⟨s₂, hs₂, y₂, hy₂⟩ := exists_den ((iF_mem_iff A n).1 hnO)
    refine ⟨s₁ * s₂, fun h => (p.isPrime.mem_or_mem h).elim hs₁ hs₂, ?_⟩
    set c : E := algebraMap F E ((s₁ * s₂ : 𝓞 F) : F) with hc
    have hkey : (c * x) ^ 2 - algebraMap F E ((s₂ * y₁ : 𝓞 F) : F) * (c * x) +
        algebraMap F E ((s₁ * s₁ * s₂ * y₂ : 𝓞 F) : F) = 0 := by
      have hy₁' : algebraMap (𝓞 F) F y₁ = algebraMap (𝓞 F) F s₁ * t := hy₁
      have hy₂' : algebraMap (𝓞 F) F y₂ = algebraMap (𝓞 F) F s₂ * n := hy₂
      have e1 : algebraMap F E ((s₂ * y₁ : 𝓞 F) : F) = c * (x + sig x) := by
        rw [hc, ← ht, ← map_mul]; congr 1
        show algebraMap (𝓞 F) F (s₂ * y₁) = algebraMap (𝓞 F) F (s₁ * s₂) * t
        rw [map_mul, map_mul, hy₁']; ring
      have e2 : algebraMap F E ((s₁ * s₁ * s₂ * y₂ : 𝓞 F) : F) = c * c * (x * sig x) := by
        rw [hc, ← hn, ← map_mul, ← map_mul]; congr 1
        show algebraMap (𝓞 F) F (s₁ * s₁ * s₂ * y₂) = algebraMap (𝓞 F) F (s₁ * s₂) * algebraMap (𝓞 F) F (s₁ * s₂) * n
        rw [map_mul, map_mul, map_mul, map_mul, hy₂']; ring
      rw [e1, e2]; ring
    have hint : IsIntegral (𝓞 F) (c * x) := by
      refine ⟨X ^ 2 - C (s₂ * y₁) * X + C (s₁ * s₁ * s₂ * y₂), ?_, ?_⟩
      · monicity!
      · rw [← hkey]
        simp [eval₂_sub, eval₂_add, eval₂_mul, eval₂_X, eval₂_C, eval₂_pow]
        rfl
    exact isIntegral_trans (R := ℤ) _ hint
  · rintro ⟨s, hs, hint⟩
    have h1 := iE_int A hint
    rw [map_mul, iE_alg] at h1
    have hinv : (A.ιF (s : F))⁻¹ ∈ 𝒪[A.Fp] := by
      rw [Valuation.mem_integer_iff, map_inv₀, iF_unit A hs, inv_one]
    have hne : A.ιF (s : F) ≠ 0 := by
      intro h0; have := iF_unit A hs; rw [h0, map_zero] at this; exact zero_ne_one this
    have e : A.ιE x = algebraMap A.Fp A.Ep (A.ιF (s : F))⁻¹ * (algebraMap A.Fp A.Ep (A.ιF (s : F)) * A.ιE x) := by
      rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hne, map_one, one_mul]
    rw [e]
    exact A.O.mul_mem (alg_mem_O A hinv) h1

end Formalism.L2.SG.Pf.LocalDenominators
