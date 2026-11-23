import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousOfMemSmoothSpan
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DifferentiableIntegralMulCpow

noncomputable section

open NumberField Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.ThetaPoisson GroundTheory.Global
  GroundTheory.Global.IdeleGroup
open scoped ComplexConjugate nonZeroDivisors ContDiff

namespace GlobalTheory.RSTheta

theorem summable_tsum_norm_le_of_le_shortest (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ)
    (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (N : ℕ) (hN : Module.finrank ℝ (Fin a → Cinf E) ≤ N) :
    ∃ (M : ℕ) (C : ℝ), ∀ (h : GA E a) (A : ℝ) (c : (Fin a → E) → ℂ), 0 ≤ A →
      (∀ ξ : Fin a → E, (fun i => pFin E (((fun j => algebraMap E (Ad E) (ξ j)) ᵥ* h.val) i)) ∉ latt a J →
        c ξ = 0) →
      (∀ ξ ξ' : Fin a → E, ξ' ≠ 0 →
        (fun i => pFin E (((fun j => algebraMap E (Ad E) (ξ' j)) ᵥ* h.val) i)) ∈ latt a J →
        ‖c ξ‖ * (1 + ‖fun i => pInf E (((fun j => algebraMap E (Ad E) (ξ j)) ᵥ* h.val) i)‖) ^ M ≤
          A * ‖fun i => pInf E (((fun j => algebraMap E (Ad E) (ξ' j)) ᵥ* h.val) i)‖ ^ N) →
      Summable (fun ξ : {ξ : Fin a → E // ξ ≠ 0} => ‖c ξ‖) ∧
        ∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, ‖c ξ‖ ≤ C * A := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · haveI : IsEmpty {ξ : Fin 0 → E // ξ ≠ 0} := ⟨fun ξ => ξ.2 (Subsingleton.elim _ _)⟩
    exact ⟨0, 0, fun _ _ _ _ _ _ => ⟨summable_empty, by simp⟩⟩
  set D := Module.finrank ℝ (Fin a → Cinf E) with hD
  have hD1 : 1 ≤ D := by rw [hD, finrank_pi_Cinf]; exact Nat.mul_pos ha Module.finrank_pos
  have hND : (D : ℝ) ≤ N := by exact_mod_cast hN
  obtain ⟨K, hK, hlat⟩ := GlobalTheory.LatticeCount.tsum_one_add_norm_rpow_neg_le_regimes (V := Fin a → Cinf E)
    hD1 (M := ((N + D + 1 : ℕ) : ℝ)) (by push_cast; linarith)
  rw [← hD] at hlat
  refine ⟨N + D + 1, 2 ^ N * K, fun g A c hA hsupp hdec => ?_⟩
  let T : (Fin a → E) →+ (Fin a → Ad E) :=
    { toFun := fun ξ => (fun j => algebraMap E (Ad E) (ξ j)) ᵥ* g.val
      map_zero' := by simp only [Pi.zero_apply, map_zero]; exact zero_vecMul _
      map_add' := fun x y => by simp only [Pi.add_apply, map_add]; exact add_vecMul _ _ _ }
  let TI : (Fin a → E) →+ (Fin a → Cinf E) := ((pInf E).toAddMonoidHom.compLeft (Fin a)).comp T
  let TF : (Fin a → E) →+ (Fin a → Af E) := ((pFin E).toAddMonoidHom.compLeft (Fin a)).comp T
  let P : AddSubgroup (Fin a → E) := (AddSubgroup.pi Set.univ fun _ => idealFiniteAdeles J).comap TF
  have hP : ∀ ξ, ξ ∈ P ↔ TF ξ ∈ latt a J := fun ξ => ⟨fun h i => h i trivial, fun h i _ => h i⟩
  obtain ⟨δ, hδ, hδle⟩ := exists_le_norm g (isCompact_latt J)
  replace hδle : ∀ ξ ∈ P, ξ ≠ 0 → δ ≤ ‖TI ξ‖ := fun ξ h h0 => hδle ξ h0 ((hP ξ).1 h)
  have hsP : ∀ ξ, c ξ ≠ 0 → ξ ∈ P := fun ξ h => (hP ξ).2 (by_contra fun h' => h (hsupp ξ h'))
  set S : Set ℝ := (fun ξ => ‖TI ξ‖) '' {ξ | ξ ∈ P ∧ ξ ≠ 0} with hS
  rcases S.eq_empty_or_nonempty with hS0 | hS0
  · have : ∀ ξ : {ξ : Fin a → E // ξ ≠ 0}, ‖c ξ‖ = 0 := fun ξ => by
      by_contra h
      exact Set.eq_empty_iff_forall_notMem.1 hS0 _ ⟨ξ.1, ⟨hsP _ (norm_ne_zero_iff.1 h), ξ.2⟩, rfl⟩
    simp only [this, tsum_zero]
    exact ⟨summable_zero, by positivity⟩
  have hr : 0 < sInf S := hδ.trans_le (le_csInf hS0 (by rintro _ ⟨ξ, hξ, rfl⟩; exact hδle ξ hξ.1 hξ.2))
  have hrle : ∀ ξ ∈ P, ξ ≠ 0 → sInf S ≤ ‖TI ξ‖ := fun ξ h h0 =>
    csInf_le ⟨0, by rintro _ ⟨ξ, -, rfl⟩; exact norm_nonneg _⟩ ⟨ξ, ⟨h, h0⟩, rfl⟩
  obtain ⟨_, ⟨ξ₀, hξ₀, rfl⟩, hlt⟩ := exists_lt_of_csInf_lt hS0 (show sInf S < 2 * sInf S by linarith)
  generalize sInf S = r at hr hrle hlt
  obtain ⟨hsum, hlo, hhi⟩ := hlat (P.map TI) r hr (by
    rintro _ ⟨ξ, hξ, rfl⟩ h0
    exact hrle ξ hξ fun e => h0 (by rw [e, map_zero]))
  set B : ℝ := A * (2 * r) ^ N with hB
  have hB0 : 0 ≤ B := by positivity
  have hterm : ∀ ξ, ‖c ξ‖ ≤ B * (1 + ‖TI ξ‖) ^ (-(((N + D + 1 : ℕ)) : ℝ)) := fun ξ => by
    have h1 := hdec ξ ξ₀ hξ₀.2 ((hP _).1 hξ₀.1)
    have hpos : 0 < (1 + ‖TI ξ‖) ^ (N + D + 1) := by positivity
    rw [Real.rpow_neg (by positivity), Real.rpow_natCast, ← div_eq_mul_inv, le_div_iff₀ hpos]
    refine h1.trans (mul_le_mul_of_nonneg_left ?_ hA)
    exact pow_le_pow_left₀ (norm_nonneg _) hlt.le _
  let j : {ξ // ξ ∈ P ∧ ξ ≠ 0} → {ξ : Fin a → E // ξ ≠ 0} := fun ξ => ⟨ξ.1, ξ.2.2⟩
  have hj : Function.Injective j := fun x y h => Subtype.ext (congrArg (fun z : {ξ : Fin a → E // ξ ≠ 0} => z.1) h)
  have hjs : ∀ ξ ∉ Set.range j, ‖c ξ‖ = 0 := fun ξ h => by
    by_contra h'
    exact h ⟨⟨ξ.1, hsP _ (norm_ne_zero_iff.1 h'), ξ.2⟩, rfl⟩
  let ι : {ξ // ξ ∈ P ∧ ξ ≠ 0} → ((P.map TI : Set (Fin a → Cinf E)) \ {0} : Set (Fin a → Cinf E)) := fun ξ =>
    ⟨TI ξ.1, ⟨ξ.1, ξ.2.1, rfl⟩, norm_pos_iff.1 (hr.trans_le (hrle _ ξ.2.1 ξ.2.2))⟩
  have hι : Function.Injective ι := fun x y h => Subtype.ext (by
    by_contra hne
    have h1 := hrle _ (P.sub_mem x.2.1 y.2.1) (sub_ne_zero.2 hne)
    rw [map_sub, show TI x.1 = TI y.1 from congrArg Subtype.val h, sub_self, norm_zero] at h1
    exact h1.not_gt hr)
  have hs1 := (hsum.mul_left B).comp_injective hι
  have hs2 : Summable ((fun ξ : {ξ : Fin a → E // ξ ≠ 0} => ‖c ξ‖) ∘ j) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun ξ => hterm ξ.1) hs1
  refine ⟨(hj.summable_iff hjs).1 hs2, ?_⟩
  rw [← hj.tsum_eq (f := fun ξ : {ξ : Fin a → E // ξ ≠ 0} => ‖c ξ‖) fun ξ h => by_contra fun h' => h (hjs ξ h')]
  refine (Summable.tsum_le_tsum_of_inj ι hι (fun _ _ => by positivity) (fun ξ => hterm ξ.1) hs2
    (hsum.mul_left B)).trans ?_
  rw [tsum_mul_left]
  have key : ∀ e : ℝ, r ^ ((N : ℝ) + e) ≤ 1 → B * (K * r ^ e) ≤ 2 ^ N * K * A := by
    intro e he
    calc B * (K * r ^ e) = 2 ^ N * K * A * r ^ ((N : ℝ) + e) := by
          rw [hB, Real.rpow_add hr, Real.rpow_natCast, mul_pow]; ring
      _ ≤ _ := mul_le_of_le_one_right (by positivity) he
  rcases le_total r 1 with h1 | h1
  · exact (mul_le_mul_of_nonneg_left (hlo h1) hB0).trans (key _ (Real.rpow_le_one hr.le h1 (by linarith)))
  · exact (mul_le_mul_of_nonneg_left (hhi h1) hB0).trans
      (key _ (Real.rpow_le_one_of_one_le_of_nonpos h1 (by push_cast; linarith)))

end GlobalTheory.RSTheta
