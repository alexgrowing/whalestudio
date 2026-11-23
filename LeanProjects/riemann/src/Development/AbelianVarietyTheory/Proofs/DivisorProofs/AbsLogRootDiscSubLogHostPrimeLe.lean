import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuadraticSubfieldRootDiscriminant
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
import Formalism.MeanHeightDescent.DivisionInequalityWithCovolume
open NumberField IsDedekindDomain Formalism.BasicNotions GlobalTheory.AllWt GlobalTheory.FlatLine

namespace GlobalTheory

theorem rootDiscr_le_of_intermediateField {E : Type} [Field E] [NumberField E]
    (K : IntermediateField ℚ E) : rootDiscr K ≤ rootDiscr E := by
  have hdisc := natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow K (𝓞 K) E (𝓞 E)
  have hN : Ideal.absNorm (differentIdeal (𝓞 K) (𝓞 E)) ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact differentIdeal_ne_bot
  have htow := Module.finrank_mul_finrank ℚ K E
  set k := Module.finrank ℚ K
  set m := Module.finrank K E
  have hk : 0 < k := Module.finrank_pos
  have hm : 0 < m := Module.finrank_pos
  have ha : 0 < (discr K).natAbs := Int.natAbs_pos.mpr (discr_ne_zero K)
  have hle : (discr K).natAbs ^ m ≤ (discr E).natAbs := by
    rw [hdisc]
    exact Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero hN)
  have hleR : ((discr K).natAbs : ℝ) ^ m ≤ ((discr E).natAbs : ℝ) := by exact_mod_cast hle
  rw [rootDiscr_def, rootDiscr_def, ← htow]
  have e1 : (((|discr K| : ℤ)) : ℝ) = ((discr K).natAbs : ℝ) := by
    rw [Nat.cast_natAbs]
  have e2 : (((|discr E| : ℤ)) : ℝ) = ((discr E).natAbs : ℝ) := by
    rw [Nat.cast_natAbs]
  rw [e1, e2]
  change _ ^ ((k : ℝ))⁻¹ ≤ _
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  calc ((discr K).natAbs : ℝ) ^ (k : ℝ)⁻¹
      = (((discr K).natAbs : ℝ) ^ m) ^ (((k * m : ℕ) : ℝ))⁻¹ := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
        congr 1
        push_cast
        field_simp
    _ ≤ ((discr E).natAbs : ℝ) ^ (((k * m : ℕ) : ℝ))⁻¹ :=
        Real.rpow_le_rpow (by positivity) hleR (by positivity)

end GlobalTheory

namespace GlobalTheory

theorem abs_lrd_sub_log_d_le_lrd :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E),
      |GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects.lrd E - Real.log H.d| ≤ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects.lrd E := by
  intro E _ _ _ H
  have hK := (rootDiscr_and_different_quadField E H).1
  have hle := rootDiscr_le_of_intermediateField (GlobalTheory.IndefiniteRowSideFullHecke.AdelicDegreeTameRamification.quadField H)
  rw [hK] at hle
  have hd1 : (1 : ℝ) ≤ H.d := by exact_mod_cast H.d_prime.one_lt.le
  have hs : 0 < √(H.d : ℝ) := Real.sqrt_pos.mpr (by linarith)
  have hlog0 : 0 ≤ Real.log H.d := Real.log_nonneg hd1
  have hlogs : Real.log √(H.d : ℝ) = Real.log H.d / 2 := by
    rw [Real.log_sqrt (by linarith)]
  have h2 : Real.log H.d / 2 ≤ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects.lrd E := by
    rw [← hlogs, GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects.lrd]
    exact Real.log_le_log hs hle
  rw [abs_le]
  constructor <;> linarith

end GlobalTheory
