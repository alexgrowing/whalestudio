import Mathlib
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.DepthCond
import Formalism.LocalRingCardinality.HostCls

open Module NumberField IsDedekindDomain

namespace Formalism.L2.Indef.Tree.DepthCond

open Formalism.L2.DIV Formalism.BasicNotions

theorem rounding_condition_holds : RoundCore := by
  intro e₁ e₂ x E h1 h2 hE
  have he1 : (0 : ℝ) < e₁ := by exact_mod_cast h1
  have he2 : (0 : ℝ) < e₂ := by exact_mod_cast h2
  have hc : (⌈(e₂ : ℝ) * x⌉ : ℝ) < (e₂ : ℝ) * x + 1 := Int.ceil_lt_add_one _
  have hE' : (E : ℝ) ≤ (e₁ : ℝ) * (⌈(e₂ : ℝ) * x⌉ : ℝ) := by exact_mod_cast hE
  have hlt : (E : ℝ) < (e₁ : ℝ) * ((e₂ : ℝ) * x + 1) :=
    lt_of_le_of_lt hE' (mul_lt_mul_of_pos_left hc he1)
  rw [div_lt_iff₀ (mul_pos he1 he2)]
  have heq : (x + 1 / (e₂ : ℝ)) * ((e₁ : ℝ) * (e₂ : ℝ)) = (e₁ : ℝ) * ((e₂ : ℝ) * x + 1) := by
    field_simp
  rw [heq]
  exact hlt

theorem nu_level_condition_holds : NuLevelCore := by
  intro g T ν D D' hg hT hν hTD hD'
  have hg1 : 0 < g - 1 := by linarith
  have h1 : T * ν ≤ T * (D / (g - 1)) := mul_le_mul_of_nonneg_left hν hT
  have h2 : T * (D / (g - 1)) = T * D / (g - 1) := by ring
  have h3 : T * D / (g - 1) ≤ D' / (g - 1) := div_le_div_of_nonneg_right hTD hg1.le
  have h4 : D' / (g - 1) < 1 / 2 := by
    rw [div_lt_iff₀ hg1]
    linarith
  linarith

theorem level_condition_holds : LevelCore := by
  intro e T ν s n X he hT hTν hs hX
  have he' : 1 / e ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) he
  have hexp : T * (ν + 1) = T * ν + T := by ring
  linarith

theorem ramification_condition_holds : RamCore := by
  intro l T ν s s' D D' C k B X hl hT hν hs' hTD hD' hCk hB hX
  have hl1 : 0 < l - 1 := by linarith
  have h1 : T * ν ≤ T * (D / (l - 1)) := mul_le_mul_of_nonneg_left hν hT
  have h2 : T * (D / (l - 1)) = T * D / (l - 1) := by ring
  have h3 : T * D / (l - 1) ≤ D' / (l - 1) := div_le_div_of_nonneg_right hTD hl1.le
  have h4 : C * k * B ≤ (l - 1) * B := mul_le_mul_of_nonneg_right hCk hB
  have h5 : D' / (l - 1) ≤ B := by
    rw [div_le_iff₀ hl1]
    linarith
  have hexp : T * (ν + s + 1) = T * ν + T * s + T := by ring
  linarith

theorem content_prime_condition_holds : FjPCore := by
  intro Nd j p
  refine ⟨fun h => ?_, fun h0 h1 h => ?_, fun h0 h1 h2 hq hd => ?_⟩
  · unfold NumDatum.FjP
    rw [if_pos h]
  · have hc : Nd.cls p = PrimeClass.ram2 ∨ Nd.cls p = PrimeClass.ramQ := by
      unfold NumDatum.cls primeClass
      by_cases hs : p ∈ Nd.H.small
      · left
        rw [if_pos hs]
      · right
        rw [if_neg hs, if_pos (h.resolve_left hs)]
    unfold NumDatum.FjP
    rw [if_neg (by rintro (h' | h') <;> contradiction)]
    rcases hc with hc | hc <;> simp [hc]
  · have hs : p ∉ Nd.H.small := by
      intro hmem
      have hdv : p ∣ Nd.H.QS := Nat.dvd_of_mem_primeFactors hmem
      have hpr : p.Prime := Nat.prime_of_mem_primeFactors hmem
      have hQd : Nat.Coprime Nd.H.QS Nd.H.d := Nat.Coprime.coprime_dvd_right (dvd_mul_left _ _) Nd.H.QS_coprime
      rw [hd] at hdv hpr
      exact Nat.not_prime_one (Nat.Coprime.eq_one_of_dvd hQd.symm hdv ▸ hpr)
    have hc : Nd.cls p = PrimeClass.ramD := by
      unfold NumDatum.cls primeClass
      rw [if_neg hs, if_neg hq, if_pos hd]
    unfold NumDatum.FjP
    rw [if_neg (by rintro (h' | h') <;> contradiction), if_pos hc]

theorem ramified_discriminant_condition_holds : FRamDCore := by
  intro Nd j b hk hw
  have hk1 : (0 : ℝ) ≤ ((Nd.R.k : ℝ) - 1) / 2 := by
    have : (1 : ℝ) ≤ Nd.R.k := by exact_mod_cast hk
    linarith
  have hsum0 : 0 ≤ ∑ t : Nd.R.A, min (Nd.w j (false, t)) (Nd.w j (true, t)) :=
    Finset.sum_nonneg fun t _ => le_min (hw t).1 (hw t).2.1
  have hsumle : ∑ t : Nd.R.A, min (Nd.w j (false, t)) (Nd.w j (true, t)) ≤ ∑ _t : Nd.R.A, 2 * b :=
    Finset.sum_le_sum fun t _ => (hw t).2.2
  have hcard : ∑ _t : Nd.R.A, 2 * b = (Nd.R.n : ℝ) * (2 * b) := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    congr 2
    simp only [Formalism.BasicNotions.Ranks.n, Formalism.HC.Frame.A]
    first
    | exact Fintype.card_fin _
    | simp [Formalism.HC.Idx]
    | exact ZMod.card _
  have h1 := mul_le_mul_of_nonneg_left (hsumle.trans hcard.le) hk1
  have h2 := mul_nonneg hk1 hsum0
  unfold NumDatum.FRamD
  constructor <;> nlinarith

section Record

variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {Bs : DefBase K} {Df : DefSide Bs} {S : IndefData Df} {P : Type} [Group P] [Finite P] {c : OnConst}

open Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.Indef Formalism.L2.Indef.Tree

end Record

end Formalism.L2.Indef.Tree.DepthCond
