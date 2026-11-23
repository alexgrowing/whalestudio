import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.RatBasisLinearIndependentInt
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.DividedPowerAlgebras.DpOfPre
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.DividedPowerAlgebras.ChooseFac

set_option autoImplicit false

noncomputable section

open DividedPowers GlobalTheory.Cris GlobalTheory.PDA

namespace FubiniStudyChowHeightFormula₂.Adr

open PowerSeries

theorem uniformBell_comp_coeff (m : ℕ) {n N : ℕ} (hn : n ≠ 0) (hN : N ≠ 0) :
    n.uniformBell N ^ m * m.uniformBell (n * N) = m.uniformBell n * (m * n).uniformBell N := by
  have h1 := Nat.uniformBell_mul_eq n hN
  have h2 := Nat.uniformBell_mul_eq m (Nat.mul_ne_zero hn hN)
  have h3 := Nat.uniformBell_mul_eq m hn
  have h4 := Nat.uniformBell_mul_eq (m * n) hN
  have hpos : 0 < N.factorial ^ (m * n) * n.factorial ^ m * m.factorial := by positivity
  apply Nat.eq_of_mul_eq_mul_right hpos
  have e1 : n.uniformBell N ^ m * m.uniformBell (n * N)
      * (N.factorial ^ (m * n) * n.factorial ^ m * m.factorial) = (m * (n * N)).factorial := by
    rw [← h2, ← h1]
    ring
  have e2 : m.uniformBell n * (m * n).uniformBell N
      * (N.factorial ^ (m * n) * n.factorial ^ m * m.factorial) = (m * n * N).factorial := by
    rw [← h4, ← h3]
    ring
  rw [e1, e2, mul_assoc]

theorem exists_dividedPowers_aug : ∀ (B : Type) [CommRing B] (Q : PDPoly B),
    ∃ η : DividedPowers Q.aug, ∀ n : ℕ, η.dpow n (Q.e 1) = Q.e n := by
  intro B _ Q
  obtain ⟨η, hpre, hη⟩ := pre_aug B Q
  obtain ⟨δ, hδ⟩ := dp_of_pre Q.P Q.aug η (Set.range fun n : ℕ => Q.e (n + 1)) hpre rfl (by
    rintro x ⟨k, rfl⟩ m n hn
    show η m (η n (Q.e (k + 1))) = _ * η (m * n) (Q.e (k + 1))
    obtain ⟨j, hj⟩ : ∃ j, n * (k + 1) = j + 1 :=
      ⟨n * (k + 1) - 1, by
        have : 0 < n * (k + 1) := Nat.mul_pos (Nat.pos_of_ne_zero hn) k.succ_pos
        omega⟩
    have hc := congrArg (Nat.cast : ℕ → Q.P) (uniformBell_comp_coeff m hn (N := k + 1) (by omega))
    push_cast at hc
    rw [hη n k, hj, hpre.mul m _ _ (Q.e_succ_mem_aug j), hη m j, hη (m * n) k, ← hj,
      show m * (n * (k + 1)) = m * n * (k + 1) by ring, ← mul_assoc, ← mul_assoc, hc])
  refine ⟨δ, fun n => ?_⟩
  rw [hδ]
  simpa [Nat.uniformBell_one_right] using hη n 0

private theorem dpowSeries_add_base_eq_mul {R A : Type} [CommRing R] [CommRing A] [Algebra R A] {I : Ideal R}
    (κ : DividedPowers I) {r : R} (hr : r ∈ I) (a b : A) :
    (PowerSeries.mk fun n => (a + b) ^ n * algebraMap R A (κ.dpow n r)) =
      (PowerSeries.mk fun n => a ^ n * algebraMap R A (κ.dpow n r)) *
        PowerSeries.mk fun n => b ^ n * algebraMap R A (κ.dpow n r) := by
  ext n
  simp only [PowerSeries.coeff_mk, PowerSeries.coeff_mul]
  rw [(Commute.all a b).add_pow', Finset.sum_mul]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hk
  have h := κ.mul_dpow (m := k.1) (n := k.2) hr
  rw [hk] at h
  rw [show a ^ k.1 * algebraMap R A (κ.dpow k.1 r) * (b ^ k.2 * algebraMap R A (κ.dpow k.2 r))
      = a ^ k.1 * b ^ k.2 * algebraMap R A (κ.dpow k.1 r * κ.dpow k.2 r) by rw [map_mul]; ring,
    h, map_mul, map_natCast, nsmul_eq_mul]
  ring

private theorem dpowSeries_algebraMap_mul_base_eq_smul_arg {R A : Type} [CommRing R] [CommRing A] [Algebra R A] {I : Ideal R}
    (κ : DividedPowers I) {r : R} (hr : r ∈ I) (s : R) (y : A) :
    (PowerSeries.mk fun n => (algebraMap R A s * y) ^ n * algebraMap R A (κ.dpow n r)) =
      PowerSeries.mk fun n => y ^ n * algebraMap R A (κ.dpow n (s * r)) := by
  ext n
  simp only [PowerSeries.coeff_mk]
  rw [κ.dpow_mul hr, map_mul, map_pow]
  ring

private theorem dpowSeries_add_arg_eq_mul {R A : Type} [CommRing R] [CommRing A] [Algebra R A] {I : Ideal R}
    (κ : DividedPowers I) {r r' : R} (hr : r ∈ I) (hr' : r' ∈ I) (y : A) :
    (PowerSeries.mk fun n => y ^ n * algebraMap R A (κ.dpow n (r + r'))) =
      (PowerSeries.mk fun n => y ^ n * algebraMap R A (κ.dpow n r)) *
        PowerSeries.mk fun n => y ^ n * algebraMap R A (κ.dpow n r') := by
  ext n
  simp only [PowerSeries.coeff_mk, PowerSeries.coeff_mul]
  rw [κ.dpow_add hr hr', map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hk
  rw [← hk, pow_add, map_mul]
  ring

private theorem dpowSeries_zero_arg_eq_one {R A : Type} [CommRing R] [CommRing A] [Algebra R A] {I : Ideal R}
    (κ : DividedPowers I) (y : A) :
    (PowerSeries.mk fun n => y ^ n * algebraMap R A (κ.dpow n 0)) = 1 := by
  ext n
  rcases n with _ | n
  · simp [κ.dpow_zero I.zero_mem]
  · simp [κ.dpow_eval_zero (Nat.succ_ne_zero n)]

private theorem dpowSeries_zero_base_eq_one {R A : Type} [CommRing R] [CommRing A] [Algebra R A] {I : Ideal R}
    (κ : DividedPowers I) {r : R} (hr : r ∈ I) :
    (PowerSeries.mk fun n => (0 : A) ^ n * algebraMap R A (κ.dpow n r)) = 1 := by
  ext n
  rcases n with _ | n
  · simp [κ.dpow_zero hr]
  · simp

private theorem dpowSeries_sum_base_eq_prod {R A : Type} [CommRing R] [CommRing A] [Algebra R A] {I : Ideal R}
    (κ : DividedPowers I) {r : R} (hr : r ∈ I) {ι : Type} (s : Finset ι) (v : ι → A) :
    (PowerSeries.mk fun n => (∑ j ∈ s, v j) ^ n * algebraMap R A (κ.dpow n r)) =
      ∏ j ∈ s, PowerSeries.mk fun n => v j ^ n * algebraMap R A (κ.dpow n r) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using dpowSeries_zero_base_eq_one κ hr
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.prod_insert hj, dpowSeries_add_base_eq_mul κ hr, ih]

private theorem dpowSeries_sum_arg_eq_prod {R A : Type} [CommRing R] [CommRing A] [Algebra R A] {I : Ideal R}
    (κ : DividedPowers I) (y : A) {ι : Type} (s : Finset ι) (v : ι → R) (hv : ∀ i, v i ∈ I) :
    (PowerSeries.mk fun n => y ^ n * algebraMap R A (κ.dpow n (∑ i ∈ s, v i))) =
      ∏ i ∈ s, PowerSeries.mk fun n => y ^ n * algebraMap R A (κ.dpow n (v i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using dpowSeries_zero_arg_eq_one κ y
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.prod_insert hj,
      dpowSeries_add_arg_eq_mul κ (hv j) (I.sum_mem fun i _ => hv i), ih]

theorem flatExt (R A : Type) [CommRing R] [CommRing A] [Algebra R A] [Module.Flat R A] (I : Ideal R)
    (κ : DividedPowers I) : ∃ δ : DividedPowers (I.map (algebraMap R A)), IsDPMorphism κ δ (algebraMap R A) := by
  classical
  obtain ⟨γ, hpre, hγ⟩ := pre_of_gens A I (fun i : I => algebraMap R A i)
    (fun i n => algebraMap R A (κ.dpow n i))
    (fun i => by simp [κ.dpow_zero i.2])
    (fun i => by simp [κ.dpow_one i.2])
    (fun i n hn => Ideal.subset_span ⟨⟨κ.dpow n i, κ.dpow_mem hn i.2⟩, rfl⟩)
    (fun i m n => by rw [← map_mul, κ.mul_dpow i.2, map_mul, map_natCast])
    (by
      intro c hc
      have hrel : ∑ i : c.support, ((i : I) : R) • c i = 0 := by
        rw [Finset.sum_coe_sort c.support (fun i => ((i : I) : R) • c i)]
        simpa [Finsupp.sum, Algebra.smul_def, mul_comm] using hc
      obtain ⟨k, a, y, hca, hsum⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero
        (R := R) (M := A) (f := fun i : c.support => ((i : I) : R)) (x := fun i => c i) hrel
      rw [Finsupp.prod, ← Finset.prod_coe_sort]
      calc (∏ i : c.support, PowerSeries.mk fun n =>
              c i ^ n * algebraMap R A (κ.dpow n ((i : I) : R)))
          = ∏ i : c.support, ∏ j, PowerSeries.mk fun n =>
              y j ^ n * algebraMap R A (κ.dpow n (a i j * ((i : I) : R))) := by
            refine Finset.prod_congr rfl fun i _ => ?_
            rw [show (c i : A) = ∑ j, a i j • y j from hca i, dpowSeries_sum_base_eq_prod κ (i : I).2]
            refine Finset.prod_congr rfl fun j _ => ?_
            rw [Algebra.smul_def, dpowSeries_algebraMap_mul_base_eq_smul_arg κ (i : I).2]
        _ = ∏ j, ∏ i : c.support, PowerSeries.mk fun n =>
              y j ^ n * algebraMap R A (κ.dpow n (a i j * ((i : I) : R))) := Finset.prod_comm
        _ = ∏ j, PowerSeries.mk fun n =>
              y j ^ n * algebraMap R A (κ.dpow n (∑ i : c.support, a i j * ((i : I) : R))) := by
            refine Finset.prod_congr rfl fun j _ => ?_
            exact (dpowSeries_sum_arg_eq_prod κ (y j) Finset.univ (fun i : c.support => a i j * ((i : I) : R))
              fun i => I.mul_mem_left _ (i : I).2).symm
        _ = 1 := by
            refine Finset.prod_eq_one fun j _ => ?_
            have h0 : ∑ i : c.support, a i j * ((i : I) : R) = 0 := by
              rw [← hsum j]
              exact Finset.sum_congr rfl fun i _ => mul_comm _ _
            rw [h0, dpowSeries_zero_arg_eq_one κ (y j)])
  have hspan : I.map (algebraMap R A) = Ideal.span (Set.range fun i : I => algebraMap R A i) := by
    rw [Ideal.map, Set.image_eq_range]
    rfl
  obtain ⟨δ, hδ⟩ := dp_of_pre A (I.map (algebraMap R A)) γ (Set.range fun i : I => algebraMap R A i)
    (hspan ▸ hpre) hspan (by
      rintro _ ⟨i, rfl⟩ m n hn
      show γ m (γ n (algebraMap R A i)) = _ * γ (m * n) (algebraMap R A i)
      rw [hγ i n, hγ ⟨κ.dpow n i, κ.dpow_mem hn i.2⟩ m, hγ i (m * n)]
      show algebraMap R A (κ.dpow m (κ.dpow n i)) = _
      rw [κ.dpow_comp hn i.2, map_mul, map_natCast])
  refine ⟨δ, ⟨le_rfl, fun {n} a ha => ?_⟩⟩
  rw [hδ]
  exact hγ ⟨a, ha⟩ n

theorem exists_std (B : Type) [CommRing B] (J : Ideal B) (δ : DividedPowers J) (Q : PDPoly B) :
    ∃ η : DividedPowers (Q.ext J), Q.IsStd δ η := by
  obtain ⟨η, hη⟩ := exists_dividedPowers_aug B Q
  obtain ⟨-, ε, hε⟩ := exists_lift_and_aug B Q
  obtain ⟨θ, hθ, hθη⟩ := dp_split B J δ Q.P ε Q.aug η hε
  refine ⟨θ, ⟨hθ, fun n => ?_⟩⟩
  rw [hθη n _ (Q.e_succ_mem_aug 0)]
  exact hη n

end FubiniStudyChowHeightFormula₂.Adr
