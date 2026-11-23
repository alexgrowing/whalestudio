import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConstMemBddAut
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NoExcludedParameterOfLiftParameters
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TendstoOneOfSummable
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.GLZetaBound

theorem norm_mul_sub_one_le {a b : ℂ} {c : ℝ} (hc : 0 ≤ c) {m k : ℕ}
    (ha : ‖a - 1‖ ≤ (1 + c) ^ m - 1) (hb : ‖b - 1‖ ≤ (1 + c) ^ k - 1) :
    ‖a * b - 1‖ ≤ (1 + c) ^ (m + k) - 1 := by
  have e : a * b - 1 = (a - 1) * (b - 1) + (a - 1) + (b - 1) := by ring
  rw [e, pow_add]
  have h1 : ‖(a - 1) * (b - 1)‖ ≤ ((1 + c) ^ m - 1) * ((1 + c) ^ k - 1) := by
    rw [norm_mul]; exact mul_le_mul ha hb (norm_nonneg _) ((norm_nonneg _).trans ha)
  calc ‖(a - 1) * (b - 1) + (a - 1) + (b - 1)‖
      ≤ ‖(a - 1) * (b - 1)‖ + ‖a - 1‖ + ‖b - 1‖ := norm_add₃_le
    _ ≤ ((1 + c) ^ m - 1) * ((1 + c) ^ k - 1) + ((1 + c) ^ m - 1) + ((1 + c) ^ k - 1) := by
        gcongr
    _ = (1 + c) ^ m * (1 + c) ^ k - 1 := by ring

theorem norm_inv_one_sub_sub_one_le {y : ℂ} (hy : ‖y‖ ≤ 1 / 2) :
    ‖(1 - y)⁻¹ - 1‖ ≤ 2 * ‖y‖ := by
  have h1 : 1 - ‖y‖ ≤ ‖1 - y‖ := by
    have := norm_sub_norm_le (1 : ℂ) y
    rwa [norm_one] at this
  have h2 : (1 : ℂ) - y ≠ 0 := by
    intro h; rw [h, norm_zero] at h1; linarith
  have e : (1 - y)⁻¹ - 1 = y / (1 - y) := by field_simp; ring
  rw [e, norm_div, div_le_iff₀ (norm_pos_iff.2 h2)]
  nlinarith [norm_nonneg y]

theorem norm_eulerFac_sub_one_le {B : Multiset ℂˣ} {x : ℂ} {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 2)
    (h : ∀ b ∈ B, ‖(b : ℂ) * x‖ ≤ δ) : ‖GlobalTheory.LFun.eulerFac B x - 1‖ ≤ (1 + 2 * δ) ^ B.card - 1 := by
  rw [GlobalTheory.LFun.eulerFac_eq_prod]
  induction B using Multiset.induction_on with
  | empty => simp
  | cons b B ih =>
    have h1 := ih fun c hc => h c (Multiset.mem_cons_of_mem hc)
    have h2 := h b (Multiset.mem_cons_self _ _)
    rw [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, add_comm B.card 1]
    refine norm_mul_sub_one_le (by linarith) ?_ h1
    rw [pow_one]
    have := norm_inv_one_sub_sub_one_le (h2.trans hδ)
    linarith

theorem norm_prod_one_sub_sub_one_le {ι : Type*} (s : Finset ι) (z : ι → ℂ) {δ : ℝ} (hδ0 : 0 ≤ δ)
    (h : ∀ i ∈ s, ‖z i‖ ≤ δ) : ‖∏ i ∈ s, (1 - z i) - 1‖ ≤ (1 + 2 * δ) ^ s.card - 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have h1 := ih fun c hc => h c (Finset.mem_insert_of_mem hc)
    have h2 := h a (Finset.mem_insert_self _ _)
    rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha, add_comm s.card 1]
    refine norm_mul_sub_one_le (by linarith) ?_ h1
    rw [pow_one]
    have e : (1 - z a) - 1 = -z a := by ring
    rw [e, norm_neg]
    linarith

theorem one_add_two_mul_pow_sub_one_le {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 4) (m : ℕ) :
    (1 + 2 * δ) ^ m - 1 ≤ 3 ^ m * δ := by
  have key : (1 + 2 * δ) ^ m - 1 ≤ (3 ^ m - 1) * δ := by
    induction m with
    | zero => simp
    | succ m ih =>
      have h3 : (1 : ℝ) ≤ 3 ^ m := one_le_pow₀ (by norm_num)
      have hf : 0 ≤ (1 + 2 * δ) ^ m - 1 := by
        have : (1 : ℝ) ≤ (1 + 2 * δ) ^ m := one_le_pow₀ (by linarith)
        linarith
      have e : (1 + 2 * δ) ^ (m + 1) - 1 = (1 + 2 * δ) * ((1 + 2 * δ) ^ m - 1) + 2 * δ := by ring
      rw [e, pow_succ]
      have : (1 + 2 * δ) * ((1 + 2 * δ) ^ m - 1) ≤ (3 / 2) * ((3 ^ m - 1) * δ) := by
        have : 1 + 2 * δ ≤ 3 / 2 := by linarith
        exact mul_le_mul this ih hf (by norm_num)
      nlinarith
  have : (3 ^ m - 1) * δ ≤ 3 ^ m * δ := by nlinarith
  linarith

theorem norm_trivial_sub_one_le : ∀ (q : ℕ), 2 ≤ q → ∀ (r t : ℕ), r + 5 ≤ t → ∀ (B : Multiset ℂˣ), B.card = r → (∀ β ∈ B, ‖(β : ℂ)‖ ≤ (q : ℝ) ^ (((r : ℝ) - 1) / 2) ∧ ‖((β⁻¹ : ℂˣ) : ℂ)‖ ≤ (q : ℝ) ^ (((r : ℝ) - 1) / 2)) → ∀ X : ℂ, ‖X‖ = (q : ℝ) ^ (-((1 + (t : ℝ)) / 2)) → ‖eulerFac B X * eulerFac (B.map fun β => β⁻¹) X * ∏ i ∈ Finset.Ioc t (r + t), (1 - ((q : ℂ) ^ i)⁻¹) - 1‖ ≤ 27 ^ r * ((q : ℝ) ^ 2)⁻¹ := by
  intro q hq r t hrt B hB hβ X hX
  set δ : ℝ := ((q : ℝ) ^ 2)⁻¹ with hδdef
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hq0 : (0 : ℝ) < q := by linarith
  have hq1 : (1 : ℝ) ≤ q := by linarith
  have hδ0 : 0 ≤ δ := by positivity
  have hδ : δ ≤ 1 / 4 := by
    rw [hδdef]
    have : (4 : ℝ) ≤ (q : ℝ) ^ 2 := by nlinarith
    rw [inv_le_comm₀ (by positivity) (by norm_num)]
    linarith
  have hrt' : (r : ℝ) + 5 ≤ t := by exact_mod_cast hrt
  have hbx : (q : ℝ) ^ (((r : ℝ) - 1) / 2) * ‖X‖ ≤ δ := by
    rw [hX, ← Real.rpow_add hq0]
    have e : δ = (q : ℝ) ^ (-(2 : ℝ)) := by
      rw [hδdef, Real.rpow_neg hq0.le, Real.rpow_two]
    rw [e]
    apply Real.rpow_le_rpow_of_exponent_le hq1
    linarith
  have hB1 : ∀ b ∈ B, ‖(b : ℂ) * X‖ ≤ δ := by
    intro b hb
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_right (hβ b hb).1 (norm_nonneg _)).trans hbx
  have hB2 : ∀ b ∈ B.map (fun β : ℂˣ => β⁻¹), ‖(b : ℂ) * X‖ ≤ δ := by
    intro b hb
    obtain ⟨β, hβB, rfl⟩ := Multiset.mem_map.1 hb
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_right (hβ β hβB).2 (norm_nonneg _)).trans hbx
  have h1 := norm_eulerFac_sub_one_le hδ0 (by linarith) hB1
  have h2 := norm_eulerFac_sub_one_le hδ0 (by linarith) hB2
  have h3 := norm_prod_one_sub_sub_one_le (Finset.Ioc t (r + t)) (fun i => ((q : ℂ) ^ i)⁻¹) hδ0
    (by
      intro i hi
      have hi2 : 2 ≤ i := by
        have := (Finset.mem_Ioc.1 hi).1; omega
      rw [norm_inv, norm_pow, Complex.norm_natCast, hδdef]
      apply inv_anti₀ (by positivity)
      exact pow_le_pow_right₀ hq1 hi2)
  rw [Multiset.card_map] at h2
  rw [Nat.card_Ioc, show r + t - t = r by omega] at h3
  rw [hB] at h1 h2
  have h12 := norm_mul_sub_one_le (by linarith) h1 h2
  have h123 := norm_mul_sub_one_le (by linarith) h12 h3
  have h4 := one_add_two_mul_pow_sub_one_le hδ0 hδ (r + r + r)
  have e27 : (3 : ℝ) ^ (r + r + r) = 27 ^ r := by
    rw [show r + r + r = 3 * r by ring, pow_mul]; norm_num
  rw [e27] at h4
  exact h123.trans h4

end GlobalTheory.GLZetaBound
