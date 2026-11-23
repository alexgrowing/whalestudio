import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EvalMod
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical

namespace GlobalTheory.CompanionTheory.LTPer.Nonv

theorem ltIter_succ_eq {B : Type} [CommRing B] (ϖ : B) (q n : ℕ) (x : B) :
    ltIter ϖ q (n + 1) x = ϖ * ltIter ϖ q n x + ltIter ϖ q n x ^ q := by
  simp only [ltIter, Function.iterate_succ_apply']

theorem norm_step_eq {C : Type} [NormedField C] [IsUltrametricDist C] (a c : C) (q : ℕ) (hq : 2 ≤ q)
    (h : ‖c‖ ^ (q - 1) < ‖a‖) : ‖a * c + c ^ q‖ = ‖a‖ * ‖c‖ := by
  by_cases hc : c = 0
  · subst hc
    have : q ≠ 0 := by omega
    simp [this]
  · have hcpos : 0 < ‖c‖ := norm_pos_iff.mpr hc
    have hlt : ‖c ^ q‖ < ‖a * c‖ := by
      obtain ⟨r, rfl⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
      rw [norm_pow, norm_mul, pow_succ]
      simp only [Nat.add_sub_cancel] at h
      exact mul_lt_mul_of_pos_right h hcpos
    rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (ne_of_gt hlt), max_eq_left hlt.le, norm_mul]

theorem norm_step_le {C : Type} [NormedField C] [IsUltrametricDist C] (a c : C) (q : ℕ) (hq : 2 ≤ q) :
    ‖a * c + c ^ q‖ ≤ max ‖a‖ (‖c‖ ^ (q - 1)) * ‖c‖ := by
  refine (IsUltrametricDist.norm_add_le_max _ _).trans ?_
  obtain ⟨r, rfl⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  rw [norm_mul, norm_pow, pow_succ, max_mul_of_nonneg _ _ (norm_nonneg c)]

theorem exists_norm_geometric {C : Type} [NormedField C] [IsUltrametricDist C] (a : C) (q : ℕ) (hq : 2 ≤ q)
    (ha0 : a ≠ 0) (ha : ‖a‖ < 1) (c : ℕ → C) (hc : ∀ n, c (n + 1) = a * c n + c n ^ q)
    (h0 : ‖c 0‖ < 1) : ∃ n, ∀ j, ‖c (n + j)‖ = ‖a‖ ^ j * ‖c n‖ := by
  have hapos : 0 < ‖a‖ := norm_pos_iff.mpr ha0
  set ρ := max ‖a‖ (‖c 0‖ ^ (q - 1)) with hρ
  have hρ1 : ρ < 1 := max_lt ha (pow_lt_one₀ (norm_nonneg _) h0 (by omega))
  have hρ0 : 0 ≤ ρ := hapos.le.trans (le_max_left _ _)
  have hdec : ∀ n, ‖c n‖ ≤ ρ ^ n * ‖c 0‖ := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hle : ‖c n‖ ≤ ‖c 0‖ :=
        ih.trans (mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ hρ0 hρ1.le))
      have hm : max ‖a‖ (‖c n‖ ^ (q - 1)) ≤ ρ :=
        max_le_max le_rfl (pow_le_pow_left₀ (norm_nonneg _) hle _)
      rw [hc n]
      calc ‖a * c n + c n ^ q‖ ≤ max ‖a‖ (‖c n‖ ^ (q - 1)) * ‖c n‖ := norm_step_le a _ q hq
        _ ≤ ρ * (ρ ^ n * ‖c 0‖) := mul_le_mul hm ih (norm_nonneg _) hρ0
        _ = ρ ^ (n + 1) * ‖c 0‖ := by ring
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hapos hρ1
  have hcn : ‖c n‖ < ‖a‖ :=
    ((hdec n).trans (mul_le_of_le_one_right (pow_nonneg hρ0 n) h0.le)).trans_lt hn
  have hsmall : ∀ x : C, ‖x‖ ≤ ‖c n‖ → ‖x‖ ^ (q - 1) < ‖a‖ := by
    intro x hx
    have hx1 : ‖x‖ ≤ 1 := hx.trans (hcn.trans ha).le
    exact ((pow_le_of_le_one (norm_nonneg _) hx1 (by omega)).trans hx).trans_lt hcn
  refine ⟨n, fun j => ?_⟩
  induction j with
  | zero => simp
  | succ j ih =>
    have hle : ‖c (n + j)‖ ≤ ‖c n‖ := by
      rw [ih]
      exact mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ hapos.le ha.le)
    rw [← add_assoc, hc (n + j), norm_step_eq a _ q hq (hsmall _ hle), ih]
    ring

variable {B : Type} [CommRing B] {S : Subring B} {F : ℕ → Ideal B} {ϖ : B}

theorem ltIter_mem (hE : PerEnv S F ϖ) (q : ℕ) {Q : B} (hQ : Q ∈ S) (n : ℕ) : ltIter ϖ q n Q ∈ S := by
  induction n with
  | zero => simpa [ltIter] using hQ
  | succ n ih =>
    rw [ltIter_succ_eq]
    exact S.add_mem (S.mul_mem hE.mem ih) (S.pow_mem ih q)

theorem ltIter_mem_succ (hE : PerEnv S F ϖ) (ϖ' : B) (hϖ : ϖ * ϖ' = 1) (q : ℕ) (hq : 2 ≤ q) {Q : B} (hQ : Q ∈ S)
    (hT : Tends S F ϖ (fun n => ϖ' ^ n * ltIter ϖ q n Q) 0) (n m : ℕ) (hm : 1 ≤ m)
    (hy : ltIter ϖ q n Q ∈ F m) : ltIter ϖ q n Q ∈ F (m + 1) := by
  have hanti : Antitone F := antitone_nat_of_succ_le hE.anti
  have hD : ∀ j, ltIter ϖ q (n + j) Q - ϖ ^ j * ltIter ϖ q n Q ∈ F (m + 1) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have hym : ltIter ϖ q (n + j) Q ∈ F m := by
        have h1 := (F m).add_mem (hE.anti m ih) ((F m).mul_mem_left (ϖ ^ j) hy)
        simpa using h1
      have hsq : ltIter ϖ q (n + j) Q * ltIter ϖ q (n + j) Q ∈ F (m + 1) :=
        hanti (by omega : m + 1 ≤ m + m) (hE.mul_le m m (Ideal.mul_mem_mul hym hym))
      obtain ⟨r, rfl⟩ : ∃ r, q = r + 2 := ⟨q - 2, by omega⟩
      have he : ltIter ϖ (r + 2) (n + (j + 1)) Q - ϖ ^ (j + 1) * ltIter ϖ (r + 2) n Q =
          ϖ * (ltIter ϖ (r + 2) (n + j) Q - ϖ ^ j * ltIter ϖ (r + 2) n Q) +
            ltIter ϖ (r + 2) (n + j) Q ^ r * (ltIter ϖ (r + 2) (n + j) Q * ltIter ϖ (r + 2) (n + j) Q) := by
        rw [← add_assoc, ltIter_succ_eq]
        ring
      rw [he]
      exact (F (m + 1)).add_mem ((F (m + 1)).mul_mem_left _ ih) ((F (m + 1)).mul_mem_left _ hsq)
  obtain ⟨c, hc⟩ := hT (m + 1)
  refine hE.closed (m + 1) _ (ltIter_mem hE q hQ n) fun M => ?_
  obtain ⟨N, hN⟩ := hc (M + c)
  obtain ⟨s, hs, hd⟩ := hN (n + N) (by omega)
  refine ⟨ϖ ^ n * s, S.mul_mem (S.pow_mem hE.mem n) hs, ?_⟩
  have h1 : ϖ ^ c * ϖ' ^ c = 1 := by rw [← mul_pow, hϖ, one_pow]
  have h2 : ϖ ^ n * ϖ' ^ n = 1 := by rw [← mul_pow, hϖ, one_pow]
  have h3 : ϖ ^ N * ϖ' ^ N = 1 := by rw [← mul_pow, hϖ, one_pow]
  have he : ltIter ϖ q n Q - ϖ ^ M * (ϖ ^ n * s) =
      ϖ ^ n * ϖ' ^ c * (ϖ ^ c * (ϖ' ^ (n + N) * ltIter ϖ q (n + N) Q - 0) - ϖ ^ (M + c) * s) -
        ϖ' ^ N * (ltIter ϖ q (n + N) Q - ϖ ^ N * ltIter ϖ q n Q) := by
    linear_combination (-ltIter ϖ q n Q) * h3 +
      (ϖ ^ M * ϖ ^ n * s - ϖ' ^ N * ltIter ϖ q (n + N) Q * (ϖ ^ n * ϖ' ^ n)) * h1 -
      ϖ' ^ N * ltIter ϖ q (n + N) Q * h2
  rw [he]
  exact (F (m + 1)).sub_mem ((F (m + 1)).mul_mem_left _ hd) ((F (m + 1)).mul_mem_left _ (hD N))

variable {C : Type} [NormedField C] [IsUltrametricDist C]

theorem exists_ltIter_mem_one (ϖ' : B) (hϖ : ϖ * ϖ' = 1) (θ : B →+* C) (hθ : ∀ x, θ x = 0 ↔ x ∈ F 1)
    (hS : ∀ s ∈ S, ‖θ s‖ ≤ 1) (ha : ‖θ ϖ‖ < 1) (q : ℕ) (hq : 2 ≤ q) (Q : B) (hQ : Q ∈ S)
    (hQM : ∃ M : ℕ, 0 < M ∧ Near S ϖ (F 1) 1 (Q ^ M))
    (hT : Tends S F ϖ (fun n => ϖ' ^ n * ltIter ϖ q n Q) 0) : ∃ n, ltIter ϖ q n Q ∈ F 1 := by
  have haa : θ ϖ * θ ϖ' = 1 := by rw [← map_mul, hϖ, map_one]
  have ha0 : θ ϖ ≠ 0 := left_ne_zero_of_mul_eq_one haa
  have hapos : 0 < ‖θ ϖ‖ := norm_pos_iff.mpr ha0
  have hnn : ‖θ ϖ‖ * ‖θ ϖ'‖ = 1 := by rw [← norm_mul, haa, norm_one]
  have hpos' : 0 < ‖θ ϖ'‖ := by
    have := right_ne_zero_of_mul_eq_one haa
    exact norm_pos_iff.mpr this
  have h0 : ‖θ (ltIter ϖ q 0 Q)‖ < 1 := by
    obtain ⟨M, hM, s, hs, hd⟩ := hQM
    have e : θ Q ^ M = θ ϖ * θ s := by
      have := (hθ _).mpr hd
      simp only [map_sub, map_mul, map_pow, pow_one] at this
      exact sub_eq_zero.mp this
    by_contra hcon
    have h1 : (1 : ℝ) ≤ ‖θ Q‖ := by simpa [ltIter] using hcon
    have h2 : (1 : ℝ) ≤ ‖θ Q‖ ^ M := one_le_pow₀ h1
    have h3 : ‖θ Q‖ ^ M = ‖θ ϖ‖ * ‖θ s‖ := by rw [← norm_pow, e, norm_mul]
    have h4 : ‖θ ϖ‖ * ‖θ s‖ < 1 :=
      (mul_le_of_le_one_right hapos.le (hS s hs)).trans_lt ha
    linarith
  obtain ⟨n, hn⟩ := exists_norm_geometric (θ ϖ) q hq ha0 ha (fun n => θ (ltIter ϖ q n Q))
    (fun n => by simp only [ltIter_succ_eq, map_add, map_mul, map_pow]) h0
  refine ⟨n, (hθ _).mp ?_⟩
  by_contra hne
  have hcpos : 0 < ‖θ (ltIter ϖ q n Q)‖ := norm_pos_iff.mpr hne
  obtain ⟨c, hc⟩ := hT 1
  have hK : 0 < ‖θ ϖ‖ ^ c * ‖θ ϖ'‖ ^ n * ‖θ (ltIter ϖ q n Q)‖ := by positivity
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one hK ha
  obtain ⟨N, hN⟩ := hc m
  obtain ⟨s, hs, hd⟩ := hN (n + N) (by omega)
  have e := (hθ _).mpr hd
  simp only [map_sub, map_mul, map_pow, map_zero, sub_zero] at e
  have e2 : ‖θ ϖ‖ ^ c * (‖θ ϖ'‖ ^ (n + N) * ‖θ (ltIter ϖ q (n + N) Q)‖) = ‖θ ϖ‖ ^ m * ‖θ s‖ := by
    have := congrArg norm (sub_eq_zero.mp e)
    simpa only [norm_mul, norm_pow] using this
  have hNN : ‖θ ϖ‖ ^ N * ‖θ ϖ'‖ ^ N = 1 := by rw [← mul_pow, hnn, one_pow]
  have e3 : ‖θ ϖ‖ ^ c * ‖θ ϖ'‖ ^ n * ‖θ (ltIter ϖ q n Q)‖ = ‖θ ϖ‖ ^ m * ‖θ s‖ := by
    rw [← e2, hn N, pow_add]
    linear_combination (-(‖θ ϖ‖ ^ c * ‖θ ϖ'‖ ^ n * ‖θ (ltIter ϖ q n Q)‖)) * hNN
  have h5 : ‖θ ϖ‖ ^ m * ‖θ s‖ ≤ ‖θ ϖ‖ ^ m :=
    mul_le_of_le_one_right (pow_nonneg hapos.le m) (hS s hs)
  linarith

end GlobalTheory.CompanionTheory.LTPer.Nonv

namespace GlobalTheory.CompanionTheory.LTPer

open GlobalTheory.CompanionTheory.LTPer.Nonv in

theorem exists_ltIter_eq_zero_of_tends : ∀ {B : Type} [CommRing B] {S : Subring B} {F : ℕ → Ideal B} {ϖ : B} {C : Type} [NormedField C] [IsUltrametricDist C], PerEnv S F ϖ → ∀ (ϖ' : B), ϖ * ϖ' = 1 →
    ∀ (θ : B →+* C), (∀ x, θ x = 0 ↔ x ∈ F 1) → (∀ s ∈ S, ‖θ s‖ ≤ 1) → ‖θ ϖ‖ < 1 → ∀ (q : ℕ), 2 ≤ q →
    ∀ Q ∈ S, (∃ M : ℕ, 0 < M ∧ Near S ϖ (F 1) 1 (Q ^ M)) →
      Tends S F ϖ (fun n => ϖ' ^ n * ltIter ϖ q n Q) 0 → ∃ n, ltIter ϖ q n Q = 0 := by
  intro B _ S F ϖ C _ _ hE ϖ' hϖ θ hθ hS ha q hq Q hQ hQM hT
  obtain ⟨n, hn⟩ := exists_ltIter_mem_one ϖ' hϖ θ hθ hS ha q hq Q hQ hQM hT
  refine ⟨n, hE.sep _ fun k => ?_⟩
  have hall : ∀ m, 1 ≤ m → ltIter ϖ q n Q ∈ F m := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base => exact hn
    | succ m hm ih => exact ltIter_mem_succ hE ϖ' hϖ q hq hQ hT n m hm ih
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [hE.top]; exact Submodule.mem_top
  · exact hall k hk

end GlobalTheory.CompanionTheory.LTPer
