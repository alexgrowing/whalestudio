import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.FactorialMulChooseEqProdRange

noncomputable section

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Finset Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas

def sumBin (r K n : ℕ) : ℝ := ((Nat.choose (n + (r + K) - 1) (r + K - 1) : ℕ) : ℝ)

theorem sum_one_le_bin (r K n : ℕ) : 1 ≤ sumBin r K n := by
  unfold sumBin
  exact_mod_cast Nat.succ_le_of_lt (Nat.choose_pos (by omega))

theorem sum_one_le_prod {ι : Type*} (s : Finset ι) (f : ι → ℝ) (h1 : ∀ i ∈ s, 1 ≤ f i) : 1 ≤ ∏ i ∈ s, f i := by
  calc (1 : ℝ) = ∏ _i ∈ s, (1 : ℝ) := by simp
    _ ≤ _ := Finset.prod_le_prod (fun _ _ => zero_le_one) h1

theorem sum_single_le_prod {ι : Type*} (s : Finset ι) (f : ι → ℝ) (h1 : ∀ i ∈ s, 1 ≤ f i) {a : ι} (ha : a ∈ s) :
    f a ≤ ∏ i ∈ s, f i := by
  classical
  rw [← Finset.mul_prod_erase s f ha]
  have h2 : (1 : ℝ) ≤ ∏ i ∈ s.erase a, f i := sum_one_le_prod _ _ fun i hi => h1 i (Finset.mem_of_mem_erase hi)
  have h3 : 0 ≤ f a := le_trans zero_le_one (h1 a ha)
  nlinarith

namespace Dat

variable {n' r : ℕ} [NeZero n'] (X : Dat n' r) (p K : ℕ)

def sumTset (la : Fin n' → Fin (r + K) → ℕ) (j : ℤ) : Finset (Fin r → ℕ) :=
  Fintype.piFinset fun i : Fin r =>
    (Finset.range (r * X.Qc p K j)).filter fun e => e % X.Qc p K j = X.nz p K la j (X.F.fr j i.val) % X.Qc p K j

def sumhT (t : Fin n') (v : Fin (r + K) → ℕ) : ℝ :=
  ∏ j : Fin X.F.J, ∏ x ∈ X.F.LLset (j.val : ℤ),
    if posOf n' x = t then sumBin r K ((X.a' p K t - ∑ c, v c) / X.Pz p K (j.val : ℤ) x) else 1

def sumSt (t : Fin n') : ℝ := ∑ v ∈ X.laSet p K t, X.sumhT p K t v

omit [NeZero n'] in

def firstSumFactor : ℝ := 1 - 1 / X.a ^ (X.Ns ^ 2)

def sumWf (j : ℤ) : ℝ := ∏ i : Fin r, sumBin r K ((X.Bw p K j (X.F.fr (j - 1) i.val) - (X.m0 K : ℤ)).toNat)

def sumTf (j : ℤ) : ℝ := (((X.Qc p K j : ℕ) : ℝ) ^ (r - 1) * max 0 (1 - (r : ℝ) / (2 * X.Y))) ^ r

theorem sum_segBound_eq (j : ℤ) (b : ℤ → ℕ) :
    X.segBound p K j b = (X.firstSumFactor * X.sumWf p K j * X.sumTf p K j) * ∏ x ∈ X.F.LLset j, sumBin r K (b x) := by
  unfold segBound firstSumFactor sumWf sumTf sumBin
  ring

end Dat

structure SumFacts {n' r : ℕ} [NeZero n'] (X : Dat n' r) (p K : ℕ) : Prop where
  tiling : ∀ φ : Fin n' → ℝ,
    ∏ t ∈ X.F.TT, φ t = ∏ j ∈ Finset.range X.F.J, ∏ x ∈ X.toLate (j : ℤ), φ (posOf n' x)
  split : ∀ (j : ℤ) (ψ : ℤ → ℝ),
    ∏ x ∈ X.toLate j, ψ x = (∏ x ∈ X.F.LLset j, ψ x) * ∏ i : Fin r, ψ (X.F.fr j i.val)
  LLsub : ∀ j x, x ∈ X.F.LLset j → x ∈ X.toLate j ∧ x < X.F.fr j 0
  frlate : ∀ j (i : Fin r), X.F.fr j i.val ∈ X.toLate j
  uniqP : ∀ j j' x x', x ∈ X.toLate j → x' ∈ X.toLate j' → posOf n' x = posOf n' x' →
    X.Pz p K j x = X.Pz p K j' x'
  kP : ∀ j x, x ∈ X.toLate j → (r + K) * X.Pz p K j x ≤ X.a' p K (posOf n' x)
  compA : ∀ t ∈ X.F.TT, sumBin r K (X.deg t) * (1 - 5 / X.Y) ≤ sumBin r K (X.a' p K t)
  compW : ∀ j (i : Fin r), sumBin r K (X.a' p K (posOf n' (X.F.fr j i.val))) * (1 - 1 / X.Y) ≤
    (((X.Pz p K j (X.F.fr j i.val) * X.Qc p K j : ℕ) : ℝ)) ^ (r + K - 1) *
      sumBin r K ((X.Bw p K (j + 1) (X.F.fr j i.val) - (X.m0 K : ℤ)).toNat)
  prodQ : ∏ j ∈ Finset.range X.F.J, X.Qc p K (j : ℤ) = p ^ n'
  perW : ∀ j (i : Fin r),
    X.Bw p K (j + X.F.J) (X.F.fr (j + X.F.J - 1) i.val) = X.Bw p K j (X.F.fr (j - 1) i.val)
  JN : X.F.J ≤ X.F.TT.card
  a32 : 32 * X.Y ≤ X.a

section Steps

variable {n' r : ℕ} [NeZero n'] {X : Dat n' r} {p K : ℕ}

omit [NeZero n'] in
theorem sum_eZ_val (e : Fin X.F.J → Fin r → ℕ) (j : Fin X.F.J) : X.eZ e (j.val : ℤ) = e j := by
  have hJ : 0 < X.F.J := lt_of_le_of_lt (Nat.zero_le _) j.isLt
  unfold Dat.eZ
  rw [dif_pos hJ]
  congr 1
  apply Fin.ext
  have h1 : ((j.val : ℤ) % (X.F.J : ℤ)) = j.val := Int.emod_eq_of_lt (by omega) (by exact_mod_cast j.isLt)
  simp only [h1, Int.toNat_natCast]
  exact Nat.mod_eq_of_lt j.isLt

theorem sum_late_mem {j x : ℤ} (hx : x ∈ X.toLate j) :
    x ∈ X.F.letters j ∧ ¬ X.F.IsW j x ∧ x ≤ X.F.fr j (r - 1) ∧ posOf n' x ∈ X.F.TT := by
  classical
  have hx' := Finset.mem_filter.mp hx
  have h2 := Finset.mem_filter.mp hx'.1
  exact ⟨hx'.1, hx'.2, (Finset.mem_Icc.mp h2.1).2, h2.2⟩

theorem sum_bfam_late (la : Fin n' → Fin (r + K) → ℕ) (e : Fin X.F.J → Fin r → ℕ) (j : Fin X.F.J) (x : ℤ)
    (hx : x ∈ X.toLate (j.val : ℤ)) :
    X.bfam p K la e (j.val : ℤ) x = X.setTau (j.val : ℤ) (X.nz p K la (j.val : ℤ)) (e j) x := by
  obtain ⟨h1, h2, h3, -⟩ := sum_late_mem hx
  unfold Dat.bfam Dat.setTau
  rw [if_pos h1, if_neg h2, sum_eZ_val]
  by_cases h : X.F.fr (j.val : ℤ) 0 ≤ x
  · rw [if_pos h, if_pos ⟨h, h3⟩]
  · rw [if_neg h, if_neg (fun hh => h hh.1)]

theorem family_degrees_admissible (hr : 0 < r) (hp : 0 < p) (hLL : ∀ j x, x ∈ X.F.LLset j → x ∈ X.toLate j)
    (la : Fin n' → Fin (r + K) → ℕ) (hla : la ∈ X.LA p K) (j : ℤ) :
    X.AdmLL p K j (X.nz p K la j) := by
  classical
  intro x hx
  have hv : la (posOf n' x) ∈ X.laSet p K (posOf n' x) := (Fintype.mem_piFinset.mp hla) _
  obtain ⟨-, hle, hall⟩ := Finset.mem_filter.mp hv
  obtain ⟨hlt, hmod⟩ := hall j x (hLL j x hx) rfl
  set P := X.Pz p K j x with hPdef
  set n := X.a' p K (posOf n' x) with hn
  set s := ∑ c, la (posOf n' x) c with hs
  have hP : 0 < P := by rw [hPdef]; unfold Dat.Pz; exact pow_pos hp _
  have hdvd : P ∣ n - s := (Nat.modEq_iff_dvd' hle).mp hmod
  have hnz : X.nz p K la j x = (n - s) / P := rfl
  have hPr : (0 : ℝ) < (P : ℝ) := by exact_mod_cast hP
  have hcast : ((X.nz p K la j x : ℕ) : ℝ) = ((n : ℝ) - s) / P := by
    rw [hnz, Nat.cast_div hdvd hPr.ne', Nat.cast_sub hle]
  have hslt : s < (r + K) * P := by
    calc s < ∑ _c : Fin (r + K), P := by
            rw [hs]
            exact Finset.sum_lt_sum_of_nonempty ⟨⟨0, by omega⟩, Finset.mem_univ _⟩ fun c _ => hlt c
      _ = (r + K) * P := by simp
  have hslt' : (s : ℝ) < Dat.k (r := r) K * P := by
    unfold Dat.k
    exact_mod_cast hslt
  rw [hcast]
  constructor
  · rw [sub_div, sub_lt_sub_iff_left, div_lt_iff₀ hPr]
    exact hslt'
  · exact div_le_div_of_nonneg_right (by have : (0 : ℝ) ≤ s := Nat.cast_nonneg _; linarith) hPr.le

theorem first_sum_factor_bounds (hY : 1 ≤ X.Y) (ha : 32 * X.Y ≤ X.a) (hNs : 1 ≤ X.Ns) :
    1 - 1 / (32 * X.Y) ≤ X.firstSumFactor ∧ 0 ≤ X.firstSumFactor := by
  have ha1 : 1 ≤ X.a := by linarith
  have h1 : X.a ≤ X.a ^ (X.Ns ^ 2) := by
    calc X.a = X.a ^ 1 := (pow_one _).symm
      _ ≤ X.a ^ (X.Ns ^ 2) := pow_le_pow_right₀ ha1 (Nat.one_le_pow _ _ hNs)
  have h2 : 1 / X.a ^ (X.Ns ^ 2) ≤ 1 / (32 * X.Y) :=
    one_div_le_one_div_of_le (by linarith) (ha.trans h1)
  have h3 : 1 / (32 * X.Y) ≤ 1 := by
    rw [div_le_one (by linarith)]; linarith
  unfold Dat.firstSumFactor
  constructor <;> linarith

end Steps

end Formalism.MainNotions.SelectionLemmas.Pf
