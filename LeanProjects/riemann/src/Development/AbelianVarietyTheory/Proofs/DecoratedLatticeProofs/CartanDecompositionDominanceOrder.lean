import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCoType
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PosIffLtCard
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke

noncomputable section

namespace GlobalTheory.ZonalInduct

def psum {N : ℕ} (ν : Fin N → ℤ) (j : ℕ) : ℤ :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin N => (i : ℕ) < j), ν i

def pot {N : ℕ} (ν : Fin N → ℤ) : ℤ := ∑ j ∈ Finset.range (N + 1), psum ν j

theorem psum_succ {N : ℕ} (ν : Fin N → ℤ) (i : Fin N) : psum ν (i + 1) = psum ν i + ν i := by
  unfold psum
  have : Finset.univ.filter (fun j : Fin N => (j : ℕ) < i + 1) =
      insert i (Finset.univ.filter (fun j : Fin N => (j : ℕ) < i)) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
    omega
  rw [this, Finset.sum_insert (by simp), add_comm]

theorem pot_lt {N : ℕ} {μ ν : Fin N → ℤ} (h : ∀ j, psum μ j ≤ psum ν j) (hne : μ ≠ ν) : pot μ < pot ν := by
  obtain ⟨i, hi⟩ : ∃ i, μ i ≠ ν i := by
    by_contra h'; push_neg at h'; exact hne (funext h')
  have hiN := i.isLt
  have : ∃ j ∈ Finset.range (N + 1), psum μ j < psum ν j := by
    by_contra h'; push_neg at h'
    have e1 : psum μ i = psum ν i := le_antisymm (h _) (h' _ (Finset.mem_range.2 (by omega)))
    have e2 : psum μ (i + 1) = psum ν (i + 1) := le_antisymm (h _) (h' _ (Finset.mem_range.2 (by omega)))
    rw [psum_succ, psum_succ, e1] at e2
    exact hi (by linarith)
  obtain ⟨j, hj, hlt⟩ := this
  exact Finset.sum_lt_sum (fun j _ => h j) ⟨j, hj, hlt⟩

theorem pot_nonneg {N : ℕ} {ν : Fin N → ℤ} (h : ∀ i, 0 ≤ ν i) : 0 ≤ pot ν :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun i _ => h i

theorem pos_iff_lt {N : ℕ} {e : Fin N → ℤ} (ha : Antitone e) (i : Fin N) :
    0 < e i ↔ (i : ℕ) < (Finset.univ.filter fun j => 0 < e j).card := by
  first
  | exact @_root_.GlobalTheory.PositiveIffLtCard.pos_iff_lt_card
  | exact _root_.GlobalTheory.PositiveIffLtCard.pos_iff_lt_card
  | (apply _root_.GlobalTheory.PositiveIffLtCard.pos_iff_lt_card <;> assumption)
  | (intros; apply _root_.GlobalTheory.PositiveIffLtCard.pos_iff_lt_card <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PositiveIffLtCard.pos_iff_lt_card <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PositiveIffLtCard.pos_iff_lt_card ..)

theorem nonneg_of_dom {N : ℕ} {ν e : Fin N → ℤ} (hν : Antitone ν) (he : ∀ i, 0 ≤ e i)
    (hle : ∀ j, psum ν j ≤ psum e j) (hsum : ∑ i, ν i = ∑ i, e i) (i : Fin N) : 0 ≤ ν i := by
  by_contra hneg
  push_neg at hneg
  have sν := Finset.sum_filter_add_sum_filter_not Finset.univ (fun j : Fin N => (j : ℕ) < i) ν
  have se := Finset.sum_filter_add_sum_filter_not Finset.univ (fun j : Fin N => (j : ℕ) < i) e
  have tν : ∑ j ∈ Finset.univ.filter (fun j : Fin N => ¬ (j : ℕ) < i), ν j < 0 := by
    refine Finset.sum_neg (fun j hj => ?_) ⟨i, by simp⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hj
    exact lt_of_le_of_lt (hν (Fin.le_def.2 hj)) hneg
  have te : 0 ≤ ∑ j ∈ Finset.univ.filter (fun j : Fin N => ¬ (j : ℕ) < i), e j :=
    Finset.sum_nonneg fun j _ => he j
  have := hle i
  unfold psum at this
  linarith

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem torusElt_add' {N : ℕ} (ϖ : kˣ) (a b : Fin N → ℤ) :
    torusElt k (Fin N) ϖ (a + b) = torusElt k (Fin N) ϖ a * torusElt k (Fin N) ϖ b := by
  apply Units.ext
  rw [Units.val_mul, val_torusElt, val_torusElt, val_torusElt, diagonal_mul_diagonal]
  congr 1; funext i; simp [zpow_add₀ (Units.ne_zero ϖ)]

theorem torusElt_zero' {N : ℕ} (ϖ : kˣ) : torusElt k (Fin N) ϖ (fun _ => 0) = 1 := by
  apply Units.ext
  rw [val_torusElt]; simp

theorem torusElt_one_comm {N : ℕ} (ϖ : kˣ) (g : GL (Fin N) k) :
    g * torusElt k (Fin N) ϖ (fun _ => 1) = torusElt k (Fin N) ϖ (fun _ => 1) * g := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, val_torusElt]
  ext i j; simp [Matrix.diagonal_mul, Matrix.mul_diagonal, mul_comm]

theorem vanish_of_shift {N : ℕ} {ϖ : kˣ} {c : ℕ → ℂ} (hc : c N ≠ 0) {h : GL (Fin N) k → ℂ}
    (hK : ∀ κ ∈ KO k (Fin N), ∀ m, h (κ * m) = h m ∧ h (m * κ) = h m)
    (hT : ∀ (s : Finset (Fin N)) R, IsRepsK (torusElt k (Fin N) ϖ (indic s)) R →
      ∀ m, ∑ g ∈ R, h (m * g) = c s.card * h m)
    (hex : ∀ g : GL (Fin N) k, ∃ R, IsRepsK g R) (j : ℕ) (m : GL (Fin N) k)
    (hm : h (m * torusElt k (Fin N) ϖ (fun _ => (j : ℤ))) = 0) : h m = 0 := by
  induction j generalizing m with
  | zero => simpa [torusElt_zero'] using hm
  | succ j ih =>
    apply ih
    have hz : indic (Finset.univ : Finset (Fin N)) = fun _ => 1 := funext fun i => by simp [indic]
    obtain ⟨R, hR⟩ := hex (torusElt k (Fin N) ϖ (indic Finset.univ))
    set z := torusElt k (Fin N) ϖ (fun _ => 1) with hzdef
    set m' := m * torusElt k (Fin N) ϖ (fun _ => (j : ℤ))
    have hsplit : torusElt k (Fin N) ϖ (fun _ => ((j + 1 : ℕ) : ℤ)) = torusElt k (Fin N) ϖ (fun _ => (j : ℤ)) * z := by
      rw [hzdef, ← torusElt_add']; congr 1
    have hm' : h (m' * z) = 0 := by rw [← hm, hsplit, mul_assoc]
    have key := hT Finset.univ R hR m'
    have hterm : ∀ g ∈ R, h (m' * g) = 0 := by
      intro g hg
      obtain ⟨κ, hκ, κ', hκ', rfl⟩ := hR.1 g hg
      rw [hz] at *
      have e : m' * (κ * z * κ') = (m' * z) * (κ * κ') := by
        rw [torusElt_one_comm]; simp only [mul_assoc]; rfl
      rw [e, (hK _ (mul_mem hκ hκ') _).2, hm']
    rw [Finset.sum_eq_zero hterm, Finset.card_univ, Fintype.card_fin] at key
    exact (mul_eq_zero.1 key.symm).resolve_left hc

theorem vanish_dominant {N : ℕ} {ϖ : kˣ} {c : ℕ → ℂ} {h : GL (Fin N) k → ℂ}
    (hcart : ∀ x : GL (Fin N) k, ∃ ν : Fin N → ℤ, Antitone ν ∧ ∃ κ ∈ KO k (Fin N), ∃ κ' ∈ KO k (Fin N),
      x = κ * torusElt k (Fin N) ϖ ν * κ')
    (hdom : ∀ (μ ν : Fin N → ℤ), Antitone μ → Antitone ν → ∀ n : ℕ, n ≤ N → ∀ g : GL (Fin N) k,
      (∃ κ ∈ KO k (Fin N), ∃ κ' ∈ KO k (Fin N),
        g = κ * torusElt k (Fin N) ϖ (indic (Finset.univ.filter fun i : Fin N => (i : ℕ) < n)) * κ') →
      (∃ κ ∈ KO k (Fin N), ∃ κ' ∈ KO k (Fin N), torusElt k (Fin N) ϖ μ * g = κ * torusElt k (Fin N) ϖ ν * κ') →
      ∑ i, ν i = ∑ i, μ i + n ∧ ∀ j : ℕ, ∑ i ∈ Finset.univ.filter (fun i : Fin N => (i : ℕ) < j), ν i ≤
        ∑ i ∈ Finset.univ.filter (fun i : Fin N => (i : ℕ) < j),
          (μ i + indic (Finset.univ.filter fun i : Fin N => (i : ℕ) < n) i))
    (hex : ∀ g : GL (Fin N) k, ∃ R, IsRepsK g R)
    (hK : ∀ κ ∈ KO k (Fin N), ∀ m, h (κ * m) = h m ∧ h (m * κ) = h m)
    (hT : ∀ (s : Finset (Fin N)) R, IsRepsK (torusElt k (Fin N) ϖ (indic s)) R →
      ∀ m, ∑ g ∈ R, h (m * g) = c s.card * h m)
    (h1 : h 1 = 0) :
    ∀ n : ℕ, ∀ e : Fin N → ℤ, Antitone e → (∀ i, 0 ≤ e i) → pot e ≤ n → h (torusElt k (Fin N) ϖ e) = 0 := by
  intro n
  refine Nat.strong_induction_on n ?_
  intro n ih e ha he hpot
  have IH : ∀ ν : Fin N → ℤ, Antitone ν → (∀ i, 0 ≤ ν i) → pot ν < pot e →
      h (torusElt k (Fin N) ϖ ν) = 0 := by
    intro ν hν hν0 hlt
    have h0 := pot_nonneg hν0
    exact ih (pot ν).toNat (by omega) ν hν hν0 (by omega)
  by_cases hzero : ∀ i, e i = 0
  · have : e = fun _ => 0 := funext hzero
    rw [this, torusElt_zero', h1]
  push_neg at hzero
  obtain ⟨i₀, hi₀⟩ := hzero
  have hi₀pos : 0 < e i₀ := lt_of_le_of_ne (he i₀) (Ne.symm hi₀)
  obtain ⟨n₀, hn₀⟩ : ∃ n₀, n₀ = (Finset.univ.filter fun j => 0 < e j).card := ⟨_, rfl⟩
  have key : ∀ i, 0 < e i ↔ (i : ℕ) < n₀ := fun i => hn₀ ▸ pos_iff_lt ha i
  have hn₀N : n₀ ≤ N := by rw [hn₀]; exact (Finset.card_le_univ _).trans (by simp)
  obtain ⟨s, hs⟩ : ∃ s : Finset (Fin N), s = Finset.univ.filter fun i : Fin N => (i : ℕ) < n₀ := ⟨_, rfl⟩
  have hind : ∀ i, indic s i = if 0 < e i then 1 else 0 := by
    intro i; simp only [indic, hs, Finset.mem_filter, Finset.mem_univ, true_and, ← key]
  have hscard : s.card = n₀ := by
    rw [hn₀]; congr 1; rw [hs]; ext i; simp [key]
  set μ : Fin N → ℤ := fun i => e i - indic s i with hμdef
  have hμe : ∀ i, μ i + indic s i = e i := fun i => by simp [hμdef]
  have hμa : Antitone μ := by
    intro i j hij
    have := ha hij; have hi := he i; have hj := he j
    simp only [hμdef, hind]
    split_ifs <;> omega
  have hμ0 : ∀ i, 0 ≤ μ i := by
    intro i; have := he i; simp only [hμdef, hind]; split_ifs <;> omega
  have hμlt : pot μ < pot e := by
    apply pot_lt
    · intro j; unfold psum
      exact Finset.sum_le_sum fun i _ => by simp only [hμdef, hind]; split_ifs <;> omega
    · intro hh; have := congrFun hh i₀; simp only [hμdef, hind, if_pos hi₀pos] at this; omega
  have hμv := IH μ hμa hμ0 hμlt
  have hTe : torusElt k (Fin N) ϖ e = torusElt k (Fin N) ϖ μ * torusElt k (Fin N) ϖ (indic s) := by
    rw [← torusElt_add']; congr 1; funext i; exact (hμe i).symm
  have hsumind : ∑ i, indic s i = (n₀ : ℤ) := by
    rw [← hscard]; simp [indic]
  obtain ⟨R, hR⟩ := hex (torusElt k (Fin N) ϖ (indic s))
  have hsum := hT s R hR (torusElt k (Fin N) ϖ μ)
  rw [hμv, mul_zero] at hsum
  have hterm : ∀ g ∈ R, h (torusElt k (Fin N) ϖ μ * g) = 0 ∨
      h (torusElt k (Fin N) ϖ μ * g) = h (torusElt k (Fin N) ϖ e) := by
    intro g hg
    obtain ⟨ν, hν, κ1, hκ1, κ2, hκ2, hx⟩ := hcart (torusElt k (Fin N) ϖ μ * g)
    have hval : h (torusElt k (Fin N) ϖ μ * g) = h (torusElt k (Fin N) ϖ ν) := by
      rw [hx, mul_assoc, (hK κ1 hκ1 _).1, (hK κ2 hκ2 _).2]
    obtain ⟨κ, hκ, κ', hκ', hgeq⟩ := hR.1 g hg
    have hd := hdom μ ν hμa hν n₀ hn₀N g ⟨κ, hκ, κ', hκ', by rw [← hs]; exact hgeq⟩ ⟨κ1, hκ1, κ2, hκ2, hx⟩
    simp only [← hs] at hd
    obtain ⟨hd1, hd2⟩ := hd
    have hle : ∀ j, psum ν j ≤ psum e j := by
      intro j; have := hd2 j; simp only [hμe] at this; exact this
    have hsumeq : ∑ i, ν i = ∑ i, e i := by
      rw [hd1, ← hsumind, ← Finset.sum_add_distrib]; simp only [hμe]
    have hν0 := nonneg_of_dom hν he hle hsumeq
    by_cases hνe : ν = e
    · right; rw [hval, hνe]
    · left; rw [hval]; exact IH ν hν hν0 (pot_lt hle hνe)
  obtain ⟨g₁, ⟨hg₁R, hg₁K⟩, -⟩ := hR.2 1 (one_mem _)
  have hg₁ : h (torusElt k (Fin N) ϖ μ * g₁) = h (torusElt k (Fin N) ϖ e) := by
    have e1 : torusElt k (Fin N) ϖ μ * g₁ =
        torusElt k (Fin N) ϖ e * (g₁⁻¹ * (1 * torusElt k (Fin N) ϖ (indic s)))⁻¹ := by
      rw [hTe]; group
    rw [e1, (hK _ (inv_mem hg₁K) _).2]
  by_contra hx
  have hite : ∀ g ∈ R, h (torusElt k (Fin N) ϖ μ * g) =
      if h (torusElt k (Fin N) ϖ μ * g) = h (torusElt k (Fin N) ϖ e) then h (torusElt k (Fin N) ϖ e) else 0 := by
    intro g hg
    rcases hterm g hg with h0 | h0
    · rw [h0, if_neg (Ne.symm hx)]
    · rw [if_pos h0]; exact h0
  rw [Finset.sum_congr rfl hite, Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const,
    nsmul_eq_mul] at hsum
  have hcard : (R.filter fun g => h (torusElt k (Fin N) ϖ μ * g) = h (torusElt k (Fin N) ϖ e)).card ≠ 0 :=
    Finset.card_ne_zero.2 ⟨g₁, Finset.mem_filter.2 ⟨hg₁R, hg₁⟩⟩
  rcases mul_eq_zero.1 hsum with hc0 | hc0
  · exact hcard (by exact_mod_cast hc0)
  · exact hx hc0

theorem zonal_vanish : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) (ϖ : kˣ) (c : ℕ → ℂ), c N ≠ 0 → (∀ x : GL (Fin N) k, ∃ ν : Fin N → ℤ, Antitone ν ∧ ∃ κ ∈ KO k (Fin N), ∃ κ' ∈ KO k (Fin N), x = κ * torusElt k (Fin N) ϖ ν * κ') → (∀ (μ ν : Fin N → ℤ), Antitone μ → Antitone ν → ∀ n : ℕ, n ≤ N → ∀ g : GL (Fin N) k, (∃ κ ∈ KO k (Fin N), ∃ κ' ∈ KO k (Fin N), g = κ * torusElt k (Fin N) ϖ (indic (Finset.univ.filter fun i : Fin N => (i : ℕ) < n)) * κ') → (∃ κ ∈ KO k (Fin N), ∃ κ' ∈ KO k (Fin N), torusElt k (Fin N) ϖ μ * g = κ * torusElt k (Fin N) ϖ ν * κ') → ∑ i, ν i = ∑ i, μ i + n ∧ ∀ j : ℕ, ∑ i ∈ Finset.univ.filter (fun i : Fin N => (i : ℕ) < j), ν i ≤ ∑ i ∈ Finset.univ.filter (fun i : Fin N => (i : ℕ) < j), (μ i + indic (Finset.univ.filter fun i : Fin N => (i : ℕ) < n) i)) → (∀ g : GL (Fin N) k, ∃ R, IsRepsK g R) → ∀ h : GL (Fin N) k → ℂ, (∀ κ ∈ KO k (Fin N), ∀ m, h (κ * m) = h m ∧ h (m * κ) = h m) → (∀ (s : Finset (Fin N)) R, IsRepsK (torusElt k (Fin N) ϖ (indic s)) R → ∀ m, ∑ g ∈ R, h (m * g) = c s.card * h m) → h 1 = 0 → ∀ m, h m = 0 := by
  intro k _ _ _ _ N ϖ c hc hcart hdom hex h hK hT h1 m
  obtain ⟨ν, hν, κ, hκ, κ', hκ', rfl⟩ := hcart m
  rw [mul_assoc, (hK κ hκ _).1, (hK κ' hκ' _).2]
  set j : ℕ := (∑ i, |ν i|).toNat with hj
  apply vanish_of_shift hc hK hT hex j
  rw [← torusElt_add']
  refine vanish_dominant hcart hdom hex hK hT h1 (pot (ν + fun _ => (j : ℤ))).toNat (ν + fun _ => (j : ℤ))
    ?_ ?_ (Int.self_le_toNat _)
  · intro a b hab; simp only [Pi.add_apply]; linarith [hν hab]
  · intro i; simp only [Pi.add_apply]
    have h1' : |ν i| ≤ ∑ i, |ν i| :=
      Finset.single_le_sum (f := fun i => |ν i|) (fun i _ => abs_nonneg _) (Finset.mem_univ i)
    have h2 := neg_abs_le (ν i)
    have h3 := Int.self_le_toNat (∑ i, |ν i|)
    omega

end GlobalTheory.ZonalInduct
