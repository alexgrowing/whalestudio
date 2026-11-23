import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.DataParams₂
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleClassGroupCardPos
import Formalism.LocalRingCardinality.SpanPowerMembership.SizeData₂
import Formalism.LocalRingCardinality.SpanPowerMembership.DivXExample

noncomputable section

namespace Formalism.BasicNotions.Examples₂

open NumberField IsDedekindDomain

instance instFactExamplePrime : Fact T0.Prime := ⟨examplePrime_prime⟩

theorem exampleHost_type_primes_split : ∀ k, (placesOver H0.E (H0.g k)).ncard = Module.finrank ℚ H0.E := by
  refine g_split_of H0 (fun k => ?_)
  fin_cases k
  · show 413718278401 % (2 ^ (2 + 2) * 571 * 599) = 1; norm_num
  · show 603339156001 % (2 ^ (2 + 2) * 571 * 599) = 1; norm_num

theorem exampleHost_typeHypothesis : THyp H0 where
  cond := fun k => by
    fin_cases k
    · show 413718278401 % (2 ^ (2 + 2) * 571 * 599) = 1; norm_num
    · show 603339156001 % (2 ^ (2 + 2) * 571 * 599) = 1; norm_num
  bb := BB_disj0
  jac := fun k => by
    fin_cases k
    · exact ⟨by show (413718278401 : ℕ) ≠ 2; norm_num, by show jacobiSym (-599) 413718278401 = 1; norm_num⟩
    · exact ⟨by show (603339156001 : ℕ) ≠ 2; norm_num, by show jacobiSym (-599) 603339156001 = 1; norm_num⟩

theorem examplePrime_ne_split_primes : T0 ≠ H0.pde ∧ T0 ≠ H0.pde' :=
  ⟨by show T0 ≠ 751; norm_num [T0], by show T0 ≠ 991; norm_num [T0]⟩

theorem exampleHost_split_prime_split : (placesOver H0.E H0.pde).ncard = Module.finrank ℚ H0.E ∧
    (placesOver H0.E H0.pde').ncard = Module.finrank ℚ H0.E :=
  ⟨placesOver_ncard_of_split_inj H0 exampleRanks_h_injective 751 (hp := ⟨by norm_num⟩)
      (by show ¬ (751 : ℕ) ∣ 2 ^ (2 + 2) * 571 * 599; norm_num) (by show jacobiSym (-571) 751 = 1; norm_num)
      (by show jacobiSym (-599) 751 = 1; norm_num)
      (Or.inr (by show ((751 : ℕ) : ZMod 16) = -1; decide +kernel)),
    placesOver_ncard_of_split_inj H0 exampleRanks_h_injective 991 (hp := ⟨by norm_num⟩)
      (by show ¬ (991 : ℕ) ∣ 2 ^ (2 + 2) * 571 * 599; norm_num) (by show jacobiSym (-571) 991 = 1; norm_num)
      (by show jacobiSym (-599) 991 = 1; norm_num)
      (Or.inr (by show ((991 : ℕ) : ZMod 16) = -1; decide +kernel))⟩

def exampleRecord (G : LocalGap H0) : D7 :=
  exampleRecordOfData H0 T0 exampleHost_type_primes_split exampleHost_typeHypothesis examplePrime_mem_levelPrimes examplePrime_ne_split_primes π0O π0_mem_K π0_norm π0_cong G

theorem nonempty_D7_of_localGap (G : LocalGap H0) : Nonempty D7 := ⟨exampleRecord G⟩

theorem record_nonempty_of_localGap : Nonempty (LocalGap H0) → Nonempty D7 := fun ⟨G⟩ => nonempty_D7_of_localGap G

theorem record_nonempty_iff_localGap : Nonempty D7 ↔ Nonempty (LocalGap H0) :=
  ⟨fun ⟨D⟩ => ⟨LocalGap.localGapOfRecord D H0⟩, record_nonempty_of_localGap⟩

def exampleSizeData (G : LocalGap H0) : SizeData₂ (exampleRecord G) :=
  sizeDataAt0 (exampleRecord G) rfl rfl (fun _ _ _ _ => rfl) (fun _ => examplePrime_ge) (le_refl 2) (le_refl 16) (le_refl 50) rfl (fun _ _ => rfl) rfl
    (fun _ i => by
      show hc0.v i = _
      have : ∀ i : Fin (R0.k - 1), hc0.v i = 24 - 4 * ((i : ℕ) : ℚ) := by
        intro i; fin_cases i <;> simp [hc0, hcV] <;> norm_num
      exact this i)
    (fun _ _ => by show hc0.u ⟨0, by decide⟩ = _; simp [hc0, hcU])
    (fun _ _ i h1 h2 => by
      have : ∀ i : Fin R0.k, 1 ≤ i.1 → i.1 + 1 < R0.k → hc0.u i = 55 / 2 - 4 * ((i : ℕ) : ℚ) := by
        intro i h1 h2
        fin_cases i <;> simp_all [hc0, hcU] <;> norm_num
      exact this i h1 h2)
    (fun _ j => by
      have : ∀ j : Fin R0.m, hc0.b j = 91 + 18 * ((j : ℕ) : ℚ) := by
        intro j; fin_cases j <;> simp [hc0, hcB] <;> norm_num
      exact this j)
    (fun _ j => by
      have : ∀ j : Fin R0.m, hc0.e j = 100 + 18 * ((j : ℕ) : ℚ) := by
        intro j; fin_cases j <;> simp [hc0, hcE] <;> norm_num
      exact this j)

theorem exists_sizeData_sc_eq_sc0 (G : LocalGap H0) : ∃ D : D7, ∃ L : SizeData₂ D, L.sc = sc0 :=
  ⟨exampleRecord G, exampleSizeData G, rfl⟩

theorem divX_nonempty (G : LocalGap H0) : Nonempty (DivX (exampleRecord G)) :=
  ⟨divXExample (exampleRecord G) rfl (fun _ => inferInstanceAs (Subsingleton Z0))⟩

end Formalism.BasicNotions.Examples₂
