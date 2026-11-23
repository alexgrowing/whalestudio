import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSpanStepHomog
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSpanStepLocal
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace SpanStepHomog

variable {K : Type} [Fintype K] {ι : K → Type} {Ω : Type} [Field Ω]

theorem mul_mem {y : (Σ k, ι k) → Ω} {a : K → ℤ} {n j : ℕ} {s t : Ω} (hs : s ∈ chartLat y a n)
    (ht : t ∈ chartLat y a j) : s * t ∈ chartLat y a (n + j) := by
  intro c hc
  have h : ∏ k, y ⟨k, c k⟩ ^ (-(((n + j : ℕ) : ℤ) * a k)) =
      (∏ k, y ⟨k, c k⟩ ^ (-((n : ℤ) * a k))) * ∏ k, y ⟨k, c k⟩ ^ (-((j : ℤ) * a k)) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [← zpow_add₀ (hc k)]
    congr 1
    push_cast
    ring
  rw [h, show s * t * ((∏ k, y ⟨k, c k⟩ ^ (-((n : ℤ) * a k))) * ∏ k, y ⟨k, c k⟩ ^ (-((j : ℤ) * a k))) =
      (s * ∏ k, y ⟨k, c k⟩ ^ (-((n : ℤ) * a k))) * (t * ∏ k, y ⟨k, c k⟩ ^ (-((j : ℤ) * a k))) by ring]
  exact MulMemClass.mul_mem (hs c hc) (ht c hc)

theorem pow_mem {y : (Σ k, ι k) → Ω} {a : K → ℤ} {v : Ω} (hv : v ∈ chartLat y a 1) (e : ℕ) :
    v ^ e ∈ chartLat y a e := by
  induction e with
  | zero => intro c _; simp
  | succ e ih => rw [pow_succ]; exact mul_mem ih hv

abbrev forms {q : ℕ} (w : Fin q → Ω) (e : ℕ) : AddSubgroup Ω :=
  gradedSpan w (fun _ : Fin 1 => 0) (fun _ => 1) e

theorem mul_forms_mem {q r : ℕ} {w : Fin q → Ω} {d : Fin r → ℕ} {t : Fin r → Ω} {N e : ℕ} {x f : Ω}
    (hx : x ∈ gradedSpan w d t N) (hf : f ∈ forms w e) : x * f ∈ gradedSpan w d t (N + e) := by
  have hmono : ∀ μ : Fin q → ℕ, x * ∏ i, w i ^ μ i ∈ gradedSpan w d t (N + ∑ i, μ i) := by
    intro μ
    induction hx using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨l, ν, hν, rfl⟩ := hz
      have h := gradedSpan_gen_mem w d t l (ν + μ)
      have hdeg : d l + ∑ i, (ν + μ) i = N + ∑ i, μ i := by
        rw [← hν]; simp [Finset.sum_add_distrib, add_assoc]
      have hval : t l * ∏ i, w i ^ (ν + μ) i = t l * (∏ i, w i ^ ν i) * ∏ i, w i ^ μ i := by
        simp only [Pi.add_apply, pow_add, Finset.prod_mul_distrib]; ring
      rwa [hdeg, hval] at h
    | zero => rw [zero_mul]; exact zero_mem _
    | add z z' _ _ hz hz' => rw [add_mul]; exact add_mem hz hz'
    | neg z _ hz => rw [neg_mul]; exact neg_mem hz
  induction hf using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨l, μ, hμ, rfl⟩ := hz
    have h := hmono μ
    rwa [one_mul, ← hμ, zero_add]
  | zero => rw [mul_zero]; exact zero_mem _
  | add z z' _ _ hz hz' => rw [mul_add]; exact add_mem hz hz'
  | neg z _ hz => rw [mul_neg]; exact neg_mem hz

theorem one_mem_forms {q : ℕ} (w : Fin q → Ω) : (1 : Ω) ∈ forms w 0 := by
  have h := gradedSpan_gen_mem w (fun _ : Fin 1 => 0) (fun _ => (1 : Ω)) 0 (fun _ => 0)
  simpa using h

theorem mem_forms_one {q : ℕ} (w : Fin q → Ω) (i : Fin q) : w i ∈ forms w 1 := by
  have h := gradedSpan_gen_mem w (fun _ : Fin 1 => 0) (fun _ => (1 : Ω)) 0 (Pi.single i 1)
  simpa [Pi.single_apply, pow_ite, Finset.prod_ite_eq'] using h

theorem pow_mem_forms {q : ℕ} (w : Fin q → Ω) (i : Fin q) (e : ℕ) : w i ^ e ∈ forms w e := by
  induction e with
  | zero => simpa using one_mem_forms w
  | succ e ih => rw [pow_succ]; exact mul_forms_mem ih (mem_forms_one w i)

theorem exists_mul_pow_mem_forms {q : ℕ} {w : Fin q → Ω} {j : Fin q} (hj : w j ≠ 0) {c : Ω}
    (hc : c ∈ Algebra.adjoin ℤ (Set.range fun i => w i / w j)) : ∃ E : ℕ, c * w j ^ E ∈ forms w E := by
  induction hc using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    refine ⟨1, ?_⟩
    rw [pow_one, div_mul_cancel₀ _ hj]
    exact mem_forms_one w i
  | algebraMap r =>
    refine ⟨0, ?_⟩
    rw [pow_zero, mul_one, algebraMap_int_eq, eq_intCast, ← zsmul_one]
    exact zsmul_mem (one_mem_forms w) r
  | add x x' _ _ hx hx' =>
    obtain ⟨E, hE⟩ := hx
    obtain ⟨E', hE'⟩ := hx'
    refine ⟨E + E', ?_⟩
    have h1 := mul_forms_mem hE (pow_mem_forms w j E')
    have h2 := mul_forms_mem hE' (pow_mem_forms w j E)
    rw [add_comm E' E] at h2
    rw [show (x + x') * w j ^ (E + E') = x * w j ^ E * w j ^ E' + x' * w j ^ E' * w j ^ E by ring]
    exact add_mem h1 h2
  | mul x x' _ _ hx hx' =>
    obtain ⟨E, hE⟩ := hx
    obtain ⟨E', hE'⟩ := hx'
    refine ⟨E + E', ?_⟩
    rw [show x * x' * w j ^ (E + E') = x * w j ^ E * (x' * w j ^ E') by ring]
    exact mul_forms_mem hE hE'

theorem mul_pow_mem_forms_of_le {q : ℕ} {w : Fin q → Ω} {j : Fin q} {c : Ω} {E E' : ℕ}
    (h : c * w j ^ E ∈ forms w E) (hle : E ≤ E') : c * w j ^ E' ∈ forms w E' := by
  have h' := mul_forms_mem h (pow_mem_forms w j (E' - E))
  rwa [mul_assoc, ← pow_add, Nat.add_sub_cancel' hle] at h'

end SpanStepHomog

open SpanStepHomog in

theorem SpanStepHomog.proof (hL : SpanStepLocal.Statement) : SpanStepHomog.Statement := by
  intro K _ ι _ Ω _ y a q w hy hw hgen
  have H : ∀ j, ∃ (r : ℕ) (b : Fin r → Ω), (∀ l, ∃ n : ℕ, b l * w j ^ n ∈ chartLat y a n) ∧
      (w j ≠ 0 → ∀ (g : Ω) (n : ℕ), g * w j ^ n ∈ chartLat y a n →
        ∃ c : Fin r → Ω, (∀ l, c l ∈ Algebra.adjoin ℤ (Set.range fun i => w i / w j)) ∧
          g = ∑ l, c l * b l) := by
    intro j
    by_cases hj : w j = 0
    · exact ⟨0, Fin.elim0, fun l => l.elim0, fun h => (h hj).elim⟩
    · obtain ⟨r, b, h1, h2⟩ := hL K ι Ω y a q w hy hw hgen j hj
      exact ⟨r, b, h1, fun _ => h2⟩
  choose r b hb hspan using H
  choose nb hnb using hb
  set m := ∑ j, ∑ l, nb j l with hm
  have hle : ∀ j l, nb j l ≤ m := fun j l =>
    (Finset.single_le_sum (f := nb j) (fun _ _ => Nat.zero_le _) (Finset.mem_univ l)).trans
      (Finset.single_le_sum (f := fun j => ∑ l, nb j l) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j))
  let e := Fintype.equivFin (Σ j, Fin (r j))
  let T : (Σ j, Fin (r j)) → Ω := fun p => b p.1 p.2 * w p.1 ^ m
  let t : Fin (Fintype.card (Σ j, Fin (r j))) → Ω := fun i => T (e.symm i)
  have htv : ∀ j l, t (e ⟨j, l⟩) = b j l * w j ^ m := fun j l => by
    show T (e.symm (e ⟨j, l⟩)) = _
    rw [Equiv.symm_apply_apply]
  refine ⟨m, _, t, fun i => ?_, fun n s hs j hj => ?_⟩
  · have h := mul_mem (hnb (e.symm i).1 (e.symm i).2) (pow_mem (hw (e.symm i).1) (m - nb (e.symm i).1 (e.symm i).2))
    rwa [mul_assoc, ← pow_add, Nat.add_sub_cancel' (hle _ _)] at h
  have hwn : w j ^ n ≠ 0 := pow_ne_zero n hj
  obtain ⟨c, hc, hg⟩ := hspan j hj (s / w j ^ n) n (by rwa [div_mul_cancel₀ _ hwn])
  choose E hE using fun l => exists_mul_pow_mem_forms hj (hc l)
  refine ⟨m + ∑ l, E l, ?_⟩
  have hs' : s * w j ^ (m + ∑ l, E l) =
      ∑ l, t (e ⟨j, l⟩) * (c l * w j ^ (∑ l, E l)) * w j ^ n := by
    rw [show s = s / w j ^ n * w j ^ n by rw [div_mul_cancel₀ _ hwn], hg, Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [htv, pow_add]; ring
  rw [hs', show n + (m + ∑ l, E l) = m + ∑ l, E l + n by ring]
  refine sum_mem fun l _ => mul_forms_mem (mul_forms_mem ?_ (mul_pow_mem_forms_of_le (hE l)
    (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ l)))) (pow_mem_forms w j n)
  have h := gradedSpan_gen_mem w (fun _ => m) t (e ⟨j, l⟩) (fun _ => 0)
  simpa using h

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
