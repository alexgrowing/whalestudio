import Mathlib
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AlgebraicValuesFinite.AlgValsFinMain
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AlgebraicValuesFinite.EvFLocalIdeleSelf
open NumberField IsDedekindDomain Formalism.L2.Host

noncomputable section

open Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR

namespace GlobalTheory.HeckeLocDec

theorem localIdele_unitPart_mem (L : Type) [Field L] [NumberField L] (w : HeightOneSpectrum (𝓞 L))
    (x : (w.adicCompletion L)ˣ) (a : ℤ) (ha : Valued.v (x : w.adicCompletion L) = WithZero.exp (-a)) :
    localIdele L w (x * (atFin w (unif w)) ^ (-a)) ∈ PI.AlgValsFin.W.UFin L := by
  refine ⟨?_, fun w' => ?_⟩
  · funext v
    exact (localIdele_isSupportedAt L w _).1 v
  · by_cases h : w' = w
    · subst h
      rw [← PI.AlgValsFin.W.evF_val, PI.AlgValsFin.W.evF_localIdele_self]
      have h1 : Valued.v ((atFin w' (unif w') : (w'.adicCompletion L)ˣ) : w'.adicCompletion L) =
          WithZero.exp (-1) := unif_spec w'
      rw [Units.val_mul, Units.val_zpow_eq_zpow_val, map_mul, map_zpow₀, h1, ha,
        ← WithZero.exp_zsmul, ← WithZero.exp_add]
      simp
    · rw [← PI.AlgValsFin.W.evF_val, PI.AlgValsFin.W.evF_localIdele_ne w' w h]
      simp

theorem loc_div_val_pow (L : Type) [Field L] [NumberField L] (χ : HChar L) :
    ∃ N : ℕ, 0 < N ∧ ∀ (w : HeightOneSpectrum (𝓞 L)) (x : (w.adicCompletion L)ˣ),
      ∃ a : ℤ, ((χ.loc w x / χ.val w ^ a : ℂˣ) : ℂ) ^ N = 1 := by
  obtain ⟨N, hN, hT⟩ := PI.AlgValsFin.W.torsUnits L χ
  refine ⟨N, hN, fun w x => ?_⟩
  have hx0 : Valued.v (x : w.adicCompletion L) ≠ 0 := by simp
  obtain ⟨a, ha⟩ : ∃ a : ℤ, Valued.v (x : w.adicCompletion L) = WithZero.exp (-a) :=
    ⟨-WithZero.log (Valued.v (x : w.adicCompletion L)), by rw [neg_neg, WithZero.exp_log hx0]⟩
  refine ⟨a, ?_⟩
  have hmem := localIdele_unitPart_mem L w x a ha
  have h := hT _ hmem
  have e : χ.loc w x / χ.val w ^ a = χ.1 (localIdele L w (x * (atFin w (unif w)) ^ (-a))) := by
    show χ.loc w x / χ.loc w (atFin w (unif w)) ^ a = χ.loc w (x * (atFin w (unif w)) ^ (-a))
    rw [map_mul, map_zpow, zpow_neg, div_eq_mul_inv]
  rw [e, ← Units.val_pow_eq_pow_val, h, Units.val_one]

end GlobalTheory.HeckeLocDec
