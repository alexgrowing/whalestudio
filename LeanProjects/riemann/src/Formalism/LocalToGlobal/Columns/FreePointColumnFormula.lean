import Formalism.LocalToGlobal.Columns.ReductionExistsInLatticeStabilizerHolds
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnfoldingEquivalence.CompSymmComp

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section Reps

open Classical

variable {E : Type} [Field E] [NumberField E] {P : HeightOneSpectrum (𝓞 E)} {q : ℕ}

theorem clS_rep_int (hq : ((q : ℕ) : 𝓞 E) ∈ P.asIdeal) (hu : ((q : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) (hp : q.Prime)
    (hcard : Nat.card (𝓞 E ⧸ P.asIdeal) = q) :
    ∀ (D : ℕ) (y : E), IntAt P y → ∃ i : ℕ, i < q ^ D ∧ IntAt P ((y - i) / (q : E) ^ D)
  | 0, y, hy => ⟨0, by simp, by simpa using hy⟩
  | D + 1, y, hy => by
    have hq0 : (q : E) ≠ 0 := ciQ_ne_zero hu
    obtain ⟨i, hi, hz⟩ := clS_rep_int hq hu hp hcard D y hy
    obtain ⟨d, hd, hdr⟩ := ocbS_natCast_surj hq hp hcard (redP P ((y - i) / (q : E) ^ D))
    have hzd : IntAt P (((y - i) / (q : E) ^ D - d) / q) := by
      refine ciIntAt_div hq hu (ciIntAt_sub hz (ocbS_intAt_natCast d)) ?_
      rw [redP_sub hz (ocbS_intAt_natCast d), redP_natCast₂, hdr, sub_self]
    refine ⟨i + q ^ D * d, ?_, ?_⟩
    · have h1 : q ^ D * d ≤ q ^ D * (q - 1) := Nat.mul_le_mul_left _ (by omega)
      have h2 : q ^ D * (q - 1) + q ^ D = q ^ (D + 1) := by
        rw [pow_succ, Nat.mul_sub_one, Nat.sub_add_cancel (Nat.le_mul_of_pos_right _ hp.pos)]
      omega
    · have e : (y - ((i + q ^ D * d : ℕ) : E)) / (q : E) ^ (D + 1) = ((y - i) / (q : E) ^ D - d) / q := by
        push_cast
        field_simp
        ring
      rw [e]
      exact hzd

theorem clS_rep (hq : ((q : ℕ) : 𝓞 E) ∈ P.asIdeal) (hu : ((q : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) (hp : q.Prime)
    (hcard : Nat.card (𝓞 E ⧸ P.asIdeal) = q) (A B : ℕ) (x : E) (hx : IntAt P ((q : E) ^ A * x)) :
    ∃ v ∈ LocE.valsQ E q A B, IntAt P ((x - v) / (q : E) ^ B) := by
  have hq0 : (q : E) ≠ 0 := ciQ_ne_zero hu
  obtain ⟨i, hi, hz⟩ := clS_rep_int hq hu hp hcard (A + B) _ hx
  refine ⟨(i : E) / (q : E) ^ A, Finset.mem_image.2 ⟨i, Finset.mem_range.2 hi, rfl⟩, ?_⟩
  have e : (x - (i : E) / (q : E) ^ A) / (q : E) ^ B = ((q : E) ^ A * x - i) / (q : E) ^ (A + B) := by
    rw [pow_add]
    field_simp
  rw [e]
  exact hz

theorem clS_rep_unique (hq : ((q : ℕ) : 𝓞 E) ∈ P.asIdeal) (hu : ((q : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) (hp : q.Prime)
    {A B : ℕ} {v v' : E} (hv : v ∈ LocE.valsQ E q A B) (hv' : v' ∈ LocE.valsQ E q A B) (h : IntAt P ((v - v') / (q : E) ^ B)) :
    v = v' := by
  have hq0 : (q : E) ≠ 0 := ciQ_ne_zero hu
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hv
  obtain ⟨i', hi', rfl⟩ := Finset.mem_image.1 hv'
  rw [Finset.mem_range] at hi hi'
  have key : ∀ j j' : ℕ, j < q ^ (A + B) → j' < q ^ (A + B) → j' ≤ j →
      IntAt P (((j : E) / (q : E) ^ A - (j' : E) / (q : E) ^ A) / (q : E) ^ B) → j = j' := by
    intro j j' hj hj' hle hI
    have e : ((j : E) / (q : E) ^ A - (j' : E) / (q : E) ^ A) / (q : E) ^ B = ((j - j' : ℕ) : E) / (q : E) ^ (A + B) := by
      rw [Nat.cast_sub hle, pow_add]
      field_simp
    rw [e, ocbS_intAt_div_pow hq hu hp] at hI
    have := Nat.eq_zero_of_dvd_of_lt hI (by omega)
    omega
  rcases le_total i' i with hle | hle
  · rw [key i i' hi hi' hle h]
  · have h' : IntAt P (((i' : E) / (q : E) ^ A - (i : E) / (q : E) ^ A) / (q : E) ^ B) := by
      have e : ((i' : E) / (q : E) ^ A - (i : E) / (q : E) ^ A) / (q : E) ^ B =
          -(((i : E) / (q : E) ^ A - (i' : E) / (q : E) ^ A) / (q : E) ^ B) := by ring
      rw [e]
      exact ciIntAt_neg h
    rw [key i' i hi' hi hle h']

end Reps

section Perm

theorem clS_sum_perm {α M : Type} [DecidableEq α] [AddCommMonoid M] (V W : Finset α) (hWV : W ⊆ V) (T σ : α → α) (F : α → M)
    (h1 : ∀ t ∈ V, F (T t) ≠ 0 → t ∈ W) (h2 : ∀ u ∈ V, F u ≠ 0 → u ∈ W) (h3 : ∀ t ∈ W, σ t ∈ W) (h4 : Set.InjOn σ W)
    (h5 : ∀ t ∈ W, F (σ t) = F (T t)) : ∑ t ∈ V, F (T t) = ∑ u ∈ V, F u := by
  classical
  rw [← Finset.sum_subset hWV (fun t ht htW => by by_contra h; exact htW (h1 t ht h)),
    ← Finset.sum_subset hWV (fun u hu huW => by by_contra h; exact huW (h2 u hu h))]
  rw [← Finset.sum_congr rfl h5]
  have himg : W.image σ = W := by
    refine Finset.eq_of_subset_of_card_le (fun x hx => ?_) ?_
    · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hx
      exact h3 t ht
    · rw [Finset.card_image_of_injOn h4]
  conv_rhs => rw [← himg]
  rw [Finset.sum_image (fun x hx y hy hxy => h4 hx hy hxy)]

end Perm

section Alg

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n' n c : ℕ}

theorem clS_apply_sum {N M : ℕ} (f : Sp E N →ₗ[E] Sp E M) (v : Sp E N) (l : Fin M) : f v l = ∑ s, v s * f (Pi.single s 1) l := by
  rw [LinearMap.pi_apply_eq_sum_univ f v, Finset.sum_apply]
  refine Finset.sum_congr rfl fun s _ => ?_
  have : (fun j => if s = j then (1 : E) else 0) = Pi.single s 1 := by
    funext j
    rw [Pi.single_apply]
    by_cases hj : j = s
    · subst hj; simp
    · rw [if_neg (Ne.symm hj), if_neg hj]
  rw [this]
  rfl

theorem clS_ext {N M : ℕ} {f f' : Sp E N →ₗ[E] Sp E M} (h : ∀ s l, f (Pi.single s 1) l = f' (Pi.single s 1) l) : f = f' := by
  refine LinearMap.ext fun v => funext fun l => ?_
  rw [clS_apply_sum f, clS_apply_sum f']
  exact Finset.sum_congr rfl fun s _ => by rw [h]

theorem clS_single_eN {N : ℕ} (s : Fin N) : (Pi.single s 1 : Sp E N) = Loc.eN E N s.1 := by
  funext l
  unfold Loc.eN
  rw [Pi.single_apply]
  by_cases h : l = s
  · rw [if_pos h, if_pos (congrArg Fin.val h)]
  · rw [if_neg h, if_neg (fun h' => h (Fin.ext h'))]

theorem free_point_column_formula (y : HomE E n' n) (t : Loc.FC n' (c + 1) n c → E) (l : Fin (n + c)) (s : Fin (n' + (c + 1))) :
    Loc.xx1 y t (Pi.single s 1) l =
      if hf : Loc.IsFree n' n c l.1 s.1 then t ⟨(l, s), hf⟩ else PI.UnfoldEquiv.UnitaryGroupMassFormula.base y l s :=
  PI.UnfoldEquiv.UnitaryGroupMassFormula.fillMatrix_single y t l s

theorem clS_rho_hi {r : Sp E (n' + (c + 1)) ≃ₗ[E] Sp E (n' + (c + 1))} (hr : Loc.R1cond E n' (c + 1) r) (s s' : Fin (n' + (c + 1)))
    (hs : n' ≤ s.1) (h : s.1 ≤ s'.1) : r (Pi.single s 1) s' = if s' = s then 1 else 0 := by
  obtain ⟨σ, hσ⟩ : ∃ σ, s.1 = n' + σ := ⟨s.1 - n', by omega⟩
  have h1 := hr.2.2 σ s' (show ¬ (s'.1 < n' + σ) by omega)
  rw [Pi.sub_apply, sub_eq_zero] at h1
  rw [clS_single_eN, hσ, h1]
  unfold Loc.eN
  by_cases h2 : s' = s
  · rw [if_pos h2, if_pos (by rw [h2, hσ])]
  · rw [if_neg h2, if_neg (fun h3 => h2 (Fin.ext (by rw [h3, hσ])))]

theorem clS_entry (x : HomE E (n' + (c + 1)) (n + c)) {r : Sp E (n' + (c + 1)) ≃ₗ[E] Sp E (n' + (c + 1))}
    (hr : Loc.R1cond E n' (c + 1) r) (s : Fin (n' + (c + 1))) (hs : n' ≤ s.1) (l : Fin (n + c)) :
    (x ∘ₗ r.toLinearMap) (Pi.single s 1) l =
      x (Pi.single s 1) l + ∑ s' : Fin (n' + (c + 1)), if s'.1 < s.1 then r (Pi.single s 1) s' * x (Pi.single s' 1) l else 0 := by
  show x (r (Pi.single s 1)) l = _
  rw [clS_apply_sum x]
  have e : ∀ s' : Fin (n' + (c + 1)), r (Pi.single s 1) s' * x (Pi.single s' 1) l =
      (if s' = s then x (Pi.single s 1) l else 0) + if s'.1 < s.1 then r (Pi.single s 1) s' * x (Pi.single s' 1) l else 0 := by
    intro s'
    by_cases h : s'.1 < s.1
    · rw [if_pos h, if_neg (fun h' => by rw [h'] at h; exact lt_irrefl _ h), zero_add]
    · rw [if_neg h, add_zero, clS_rho_hi hr s s' hs (by omega)]
      by_cases h2 : s' = s
      · rw [if_pos h2, if_pos h2, one_mul, h2]
      · rw [if_neg h2, if_neg h2, zero_mul]
  rw [Finset.sum_congr rfl fun s' _ => e s', Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ s, if_pos (Finset.mem_univ _)]

theorem free_point_embedding (y : HomE E n' n) (t : Loc.FC n' (c + 1) n c → E) (v : Sp E n') :
    Loc.xx1 y t (Loc.inX E n' (c + 1) v) = Loc.inX E n c (y v) :=
  (PI.UnfoldEquiv.UnitaryGroupMassFormula.isFillOf_fillMatrix y t).1 v

theorem free_point_later_column (y : HomE E n' n) (t : Loc.FC n' (c + 1) n c → E) (l : Fin (n + c)) (s' : Fin (n' + (c + 1))) (hl : n ≤ l.1)
    (hs : s'.1 ≤ n' + (l.1 - n)) : Loc.xx1 y t (Pi.single s' 1) l = if s'.1 = n' + (l.1 - n) then 1 else 0 := by
  have hlc := l.2
  have hf : ¬ Loc.IsFree n' n c l.1 s'.1 := by
    unfold Loc.IsFree
    omega
  rw [free_point_column_formula, dif_neg hf]
  unfold PI.UnfoldEquiv.UnitaryGroupMassFormula.base
  by_cases h1 : s'.1 < n'
  · rw [dif_pos h1, dif_neg (by omega), if_neg (by omega)]
  · rw [dif_neg h1]
    by_cases h2 : s'.1 = n' + (l.1 - n)
    · rw [if_pos h2, if_pos (by omega)]
    · rw [if_neg h2, if_neg (by omega)]

def freeCoordinatesTransform (y : HomE E n' n) (r : Sp E (n' + (c + 1)) ≃ₗ[E] Sp E (n' + (c + 1))) (t : Loc.FC n' (c + 1) n c → E) :
    Loc.FC n' (c + 1) n c → E :=
  fun p => (Loc.xx1 y t ∘ₗ r.toLinearMap) (Pi.single p.1.2 1) p.1.1

theorem clS_comp {r : Sp E (n' + (c + 1)) ≃ₗ[E] Sp E (n' + (c + 1))} {g : Sp E n' ≃ₗ[E] Sp E n'} (hr : Loc.R1cond E n' (c + 1) r)
    (hg : ∀ x, r (Loc.inX E n' (c + 1) x) = Loc.inX E n' (c + 1) (g x)) (y : HomE E n' n) (t : Loc.FC n' (c + 1) n c → E) :
    Loc.xx1 y t ∘ₗ r.toLinearMap = Loc.xx1 (y ∘ₗ g.toLinearMap) (freeCoordinatesTransform y r t) := by
  refine clS_ext fun s l => ?_
  by_cases hs : s.1 < n'
  · show Loc.xx1 y t (r (Pi.single s 1)) l = _
    rw [clS_single_eN, ciEN hs, hg, free_point_embedding, free_point_embedding]
    rfl
  · rw [free_point_column_formula (y ∘ₗ g.toLinearMap)]
    split_ifs with hf
    · rfl
    · have hsl := s.2
      rw [clS_entry _ hr s (by omega) l, free_point_column_formula, dif_neg hf]
      have hb : PI.UnfoldEquiv.UnitaryGroupMassFormula.base y l s = PI.UnfoldEquiv.UnitaryGroupMassFormula.base (y ∘ₗ g.toLinearMap) l s := by
        unfold PI.UnfoldEquiv.UnitaryGroupMassFormula.base
        rw [dif_neg hs, dif_neg hs]
      rw [hb, add_eq_left]
      refine Finset.sum_eq_zero fun s' _ => ?_
      split_ifs with h1
      · by_cases h0 : s.1 = n'
        · have e : r (Pi.single s 1) = Pi.single s 1 := by
            rw [clS_single_eN, h0]
            exact hr.2.1
          rw [e, Pi.single_apply, if_neg (fun h' => by rw [h'] at h1; exact lt_irrefl _ h1), zero_mul]
        · have hfl : n ≤ l.1 ∧ s.1 - n' ≤ l.1 - n := by
            unfold Loc.IsFree at hf
            omega
          rw [free_point_later_column y t l s' hfl.1 (by omega), if_neg (by omega), mul_zero]
      · rfl

theorem clS_chArg {r : Sp E (n' + (c + 1)) ≃ₗ[E] Sp E (n' + (c + 1))} (hr : Loc.R1cond E n' (c + 1) r) (y : HomE E n' n)
    (t : Loc.FC n' (c + 1) n c → E) :
    Loc.chArg (n' := n') (c' := c + 1) (n := n) (c := c) (Loc.xx1 y t ∘ₗ r.toLinearMap) =
      Loc.chArg (n' := n') (c' := c + 1) (n := n) (c := c) (Loc.xx1 y t) + Loc.n1Arg r := by
  unfold Loc.chArg Loc.n1Arg
  rw [Nat.add_sub_cancel, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i < c := Finset.mem_range.1 hi
  have hs : n' + i + 1 < n' + (c + 1) := by omega
  have hs0 : n' + i < n' + (c + 1) := by omega
  have hl : n + i < n + c := by omega
  have e1 : Loc.eN E (n' + (c + 1)) (n' + i + 1) = Pi.single (⟨n' + i + 1, hs⟩ : Fin (n' + (c + 1))) 1 :=
    (clS_single_eN (E := E) (⟨n' + i + 1, hs⟩ : Fin (n' + (c + 1)))).symm
  unfold Loc.atN
  rw [dif_pos hl, dif_pos hl, dif_pos hs0, e1, clS_entry _ hr ⟨n' + i + 1, hs⟩ (by show n' ≤ n' + i + 1; omega) ⟨n + i, hl⟩]
  congr 1
  have e2 : ∀ s' : Fin (n' + (c + 1)), (if s'.1 < (⟨n' + i + 1, hs⟩ : Fin (n' + (c + 1))).1 then
      r (Pi.single ⟨n' + i + 1, hs⟩ 1) s' * Loc.xx1 y t (Pi.single s' 1) ⟨n + i, hl⟩ else 0) =
      if s' = ⟨n' + i, hs0⟩ then r (Pi.single ⟨n' + i + 1, hs⟩ 1) ⟨n' + i, hs0⟩ else 0 := by
    intro s'
    by_cases h1 : s'.1 < n' + i + 1
    · rw [if_pos h1, free_point_later_column y t ⟨n + i, hl⟩ s' (by show n ≤ n + i; omega) (by show s'.1 ≤ n' + (n + i - n); omega)]
      by_cases h2 : s' = ⟨n' + i, hs0⟩
      · rw [if_pos h2, if_pos (by rw [h2]; show n' + i = n' + (n + i - n); omega), mul_one, h2]
      · rw [if_neg h2, if_neg (fun h3 => h2 (Fin.ext (by show s'.1 = n' + i; have : s'.1 = n' + (n + i - n) := h3; omega))), mul_zero]
    · rw [if_neg h1, if_neg (fun h2 => h1 (by rw [h2]; show n' + i < n' + i + 1; omega))]
  rw [Finset.sum_congr rfl fun s' _ => e2 s', Finset.sum_ite_eq' Finset.univ, if_pos (Finset.mem_univ _)]

end Alg

section An

open Classical

variable {E : Type} [Field E] [NumberField E] [StarRing E] {P : HeightOneSpectrum (𝓞 E)} {q : ℕ} {n' n c : ℕ}

theorem clS_bd_mono {m m' : ℕ} {x : E} (hx : IntAt P ((q : E) ^ m * x)) (h : m ≤ m') : IntAt P ((q : E) ^ m' * x) := by
  have e : (q : E) ^ m' * x = (q : E) ^ (m' - m) * ((q : E) ^ m * x) := by
    rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel h]
  rw [e]
  have hp : IntAt P ((q : E) ^ (m' - m)) := by
    have h := IntAt.coe P (((q : ℕ) : 𝓞 E) ^ (m' - m))
    rwa [map_pow, map_natCast] at h
  exact hp.mul hx

theorem clS_bd_int (m : ℕ) {x : E} (hx : IntAt P x) : IntAt P ((q : E) ^ m * x) :=
  clS_bd_mono (m := 0) (by rwa [pow_zero, one_mul]) (Nat.zero_le m)

theorem clS_bd_add {m : ℕ} {x y : E} (hx : IntAt P ((q : E) ^ m * x)) (hy : IntAt P ((q : E) ^ m * y)) :
    IntAt P ((q : E) ^ m * (x + y)) := by
  rw [mul_add]
  exact hx.add hy

theorem clS_bd_neg {m : ℕ} {x : E} (hx : IntAt P ((q : E) ^ m * x)) : IntAt P ((q : E) ^ m * -x) := by
  rw [mul_neg]
  exact ciIntAt_neg hx

theorem clS_bd_sub {m : ℕ} {x y : E} (hx : IntAt P ((q : E) ^ m * x)) (hy : IntAt P ((q : E) ^ m * y)) :
    IntAt P ((q : E) ^ m * (x - y)) := by
  rw [mul_sub]
  exact ciIntAt_sub hx hy

theorem clS_bd_mul {m m' : ℕ} {x y : E} (hx : IntAt P ((q : E) ^ m * x)) (hy : IntAt P ((q : E) ^ m' * y)) :
    IntAt P ((q : E) ^ (m + m') * (x * y)) := by
  have e : (q : E) ^ (m + m') * (x * y) = ((q : E) ^ m * x) * ((q : E) ^ m' * y) := by
    rw [pow_add]
    ring
  rw [e]
  exact hx.mul hy

theorem clS_bd_sum {ι : Type} {m : ℕ} (s : Finset ι) (f : ι → E) (h : ∀ i ∈ s, IntAt P ((q : E) ^ m * f i)) :
    IntAt P ((q : E) ^ m * ∑ i ∈ s, f i) := by
  rw [Finset.mul_sum]
  exact ciIntAt_sum _ _ h

def clS_phi (y : HomE E n' n) (r : Sp E (n' + (c + 1)) ≃ₗ[E] Sp E (n' + (c + 1))) (t : Loc.FC n' (c + 1) n c → E)
    (p : Loc.FC n' (c + 1) n c) : E :=
  ∑ s' : Fin (n' + (c + 1)), if s'.1 < p.1.2.1 then r (Pi.single p.1.2 1) s' * Loc.xx1 y t (Pi.single s' 1) p.1.1 else 0

theorem clS_T_eq {r : Sp E (n' + (c + 1)) ≃ₗ[E] Sp E (n' + (c + 1))} (hr : Loc.R1cond E n' (c + 1) r) (y : HomE E n' n)
    (t : Loc.FC n' (c + 1) n c → E) (p : Loc.FC n' (c + 1) n c) : freeCoordinatesTransform y r t p = t p + clS_phi y r t p := by
  unfold freeCoordinatesTransform clS_phi
  rw [clS_entry _ hr p.1.2 p.2.1 p.1.1, free_point_column_formula, dif_pos p.2]

theorem clS_M_bd {a e : ℕ} {y : HomE E n' n} (hy : ∀ s l, IntAt P ((q : E) ^ a * y (Pi.single s 1) l)) {t : Loc.FC n' (c + 1) n c → E}
    {σ : ℕ} (ht : ∀ p : Loc.FC n' (c + 1) n c, p.1.2.1 - n' < σ → IntAt P ((q : E) ^ (a + (p.1.2.1 - n' + 1) * e) * t p))
    (s' : Fin (n' + (c + 1))) (hs' : s'.1 < n' + σ) (l : Fin (n + c)) :
    IntAt P ((q : E) ^ (a + σ * e) * Loc.xx1 y t (Pi.single s' 1) l) := by
  rw [free_point_column_formula]
  split_ifs with hf
  · have h0 : n' ≤ s'.1 := hf.1
    have h1 : s'.1 - n' < σ := by omega
    exact clS_bd_mono (ht ⟨(l, s'), hf⟩ h1) (Nat.add_le_add_left (Nat.mul_le_mul_right e (by show s'.1 - n' + 1 ≤ σ; omega)) a)
  · unfold PI.UnfoldEquiv.UnitaryGroupMassFormula.base
    split_ifs with h1 h2 h3
    · rw [LinearMap.toMatrix'_apply]
      exact clS_bd_mono (hy ⟨s'.1, h1⟩ ⟨l.1, h2⟩) (Nat.le_add_right _ _)
    · exact clS_bd_int _ ciIntAt_zero
    · exact clS_bd_int _ ciIntAt_one
    · exact clS_bd_int _ ciIntAt_zero

theorem clS_phi_bd {a e : ℕ} {y : HomE E n' n} (hy : ∀ s l, IntAt P ((q : E) ^ a * y (Pi.single s 1) l))
    {r : Sp E (n' + (c + 1)) ≃ₗ[E] Sp E (n' + (c + 1))} (hre : ∀ s s', IntAt P ((q : E) ^ e * r (Pi.single s 1) s'))
    {t : Loc.FC n' (c + 1) n c → E} (p : Loc.FC n' (c + 1) n c)
    (ht : ∀ p' : Loc.FC n' (c + 1) n c, p'.1.2.1 - n' < p.1.2.1 - n' → IntAt P ((q : E) ^ (a + (p'.1.2.1 - n' + 1) * e) * t p')) :
    IntAt P ((q : E) ^ (a + (p.1.2.1 - n' + 1) * e) * clS_phi y r t p) := by
  unfold clS_phi
  refine clS_bd_sum _ _ fun s' _ => ?_
  split_ifs with h
  · have h0 : n' ≤ p.1.2.1 := p.2.1
    have h1 := clS_bd_mul (hre p.1.2 s') (clS_M_bd hy ht s' (by omega) p.1.1)
    have e1 : e + (a + (p.1.2.1 - n') * e) = a + (p.1.2.1 - n' + 1) * e := by ring
    rwa [e1] at h1
  · exact clS_bd_int _ ciIntAt_zero

theorem clS_phi_congr (y : HomE E n' n) (r : Sp E (n' + (c + 1)) ≃ₗ[E] Sp E (n' + (c + 1))) {t t' : Loc.FC n' (c + 1) n c → E}
    (p : Loc.FC n' (c + 1) n c) (h : ∀ p' : Loc.FC n' (c + 1) n c, p'.1.2.1 - n' < p.1.2.1 - n' → t p' = t' p') :
    clS_phi y r t p = clS_phi y r t' p := by
  unfold clS_phi
  refine Finset.sum_congr rfl fun s' _ => ?_
  split_ifs with h1
  · rw [free_point_column_formula, free_point_column_formula]
    split_ifs with hf
    · have h0 : n' ≤ s'.1 := hf.1
      rw [h ⟨(p.1.1, s'), hf⟩ (by show s'.1 - n' < p.1.2.1 - n'; omega)]
    · rfl
  · rfl

end An

section Main

open Classical

variable {E : Type} [Field E] [NumberField E] [StarRing E] {P : HeightOneSpectrum (𝓞 E)} {q : ℕ} {K : Type} [Field K] {n' n c : ℕ}

theorem clS_chArg_add (x z : HomE E (n' + (c + 1)) (n + c)) :
    Loc.chArg (n' := n') (c' := c + 1) (n := n) (c := c) (x + z) =
      Loc.chArg (n' := n') (c' := c + 1) (n := n) (c := c) x + Loc.chArg (n' := n') (c' := c + 1) (n := n) (c := c) z := by
  unfold Loc.chArg
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  unfold Loc.atN
  split_ifs
  · rfl
  · rw [add_zero]

theorem clS_chArg_bd {m : ℕ} {x : HomE E (n' + (c + 1)) (n + c)} (hx : ∀ s l, IntAt P ((q : E) ^ m * x (Pi.single s 1) l)) :
    IntAt P ((q : E) ^ m * Loc.chArg (n' := n') (c' := c + 1) (n := n) (c := c) x) := by
  unfold Loc.chArg
  refine clS_bd_sum _ _ fun i hi => ?_
  have hi' := Finset.mem_range.1 hi
  have hs : n' + i + 1 < n' + (c + 1) := by omega
  rw [show Loc.eN E (n' + (c + 1)) (n' + i + 1) = Pi.single (⟨n' + i + 1, hs⟩ : Fin (n' + (c + 1))) 1 from
    (clS_single_eN (E := E) (⟨n' + i + 1, hs⟩ : Fin (n' + (c + 1)))).symm]
  unfold Loc.atN
  split_ifs
  · exact hx _ _
  · exact clS_bd_int _ ciIntAt_zero

theorem free_argument_integral {m : ℕ} {r : Sp E (n' + (c + 1)) ≃ₗ[E] Sp E (n' + (c + 1))} (hre : ∀ s s', IntAt P ((q : E) ^ m * r (Pi.single s 1) s')) :
    IntAt P ((q : E) ^ m * Loc.n1Arg r) := by
  unfold Loc.n1Arg
  refine clS_bd_sum _ _ fun i hi => ?_
  have hi' := Finset.mem_range.1 hi
  have hs : n' + i + 1 < n' + (c + 1) := by omega
  rw [show Loc.eN E (n' + (c + 1)) (n' + i + 1) = Pi.single (⟨n' + i + 1, hs⟩ : Fin (n' + (c + 1))) 1 from
    (clS_single_eN (E := E) (⟨n' + i + 1, hs⟩ : Fin (n' + (c + 1)))).symm]
  unfold Loc.atN
  split_ifs
  · exact hre _ _
  · exact clS_bd_int _ ciIntAt_zero

def clS_G (psi : E → K) (Ψ : Loc.SF E K (n' + (c + 1)) (n + c)) (yj : HomE E n' n) (u : Loc.FC n' (c + 1) n c → E) : K :=
  Ψ (Loc.xx1 yj u) * psi (-Loc.chArg (n' := n') (c' := c + 1) (n := n) (c := c) (Loc.xx1 yj u))

theorem clS_int_of_div (hq0 : (q : E) ≠ 0) {B : ℕ} {d : E} (h : IntAt P (d / (q : E) ^ B)) : IntAt P d := by
  have e : d = (q : E) ^ B * (d / (q : E) ^ B) := by
    field_simp
  rw [e]
  exact clS_bd_int _ h

theorem clS_G_congr (hq0 : (q : E) ≠ 0) (psi : E → K) {D a b B : ℕ}
    (hadd : ∀ x y : E, IntAt P ((q : E) ^ D * x) → IntAt P ((q : E) ^ D * y) → psi (x + y) = psi x * psi y)
    (hint : ∀ x : E, IntAt P x → psi x = 1) (Ψ : Loc.SF E K (n' + (c + 1)) (n + c))
    (hsupp : ∀ x, Ψ x ≠ 0 → ∀ s l, IntAt P ((q : E) ^ a * x (Pi.single s 1) l)) (haD : a ≤ D)
    (hinv : ∀ x z, (∀ s l, IntAt P (((q : E) ^ b)⁻¹ * z (Pi.single s 1) l)) → Ψ (x + z) = Ψ x) (hB : b ≤ B) (yj : HomE E n' n)
    (u v : Loc.FC n' (c + 1) n c → E) (huv : ∀ p, IntAt P ((v p - u p) / (q : E) ^ B)) : clS_G psi Ψ yj v = clS_G psi Ψ yj u := by
  have hZ : ∀ s l, (Loc.xx1 yj v - Loc.xx1 yj u) (Pi.single s 1) l =
      if hf : Loc.IsFree n' n c l.1 s.1 then v ⟨(l, s), hf⟩ - u ⟨(l, s), hf⟩ else 0 := by
    intro s l
    rw [LinearMap.sub_apply, Pi.sub_apply, free_point_column_formula, free_point_column_formula]
    split_ifs
    · rfl
    · rw [sub_self]
  have hZi : ∀ s l, IntAt P ((Loc.xx1 yj v - Loc.xx1 yj u) (Pi.single s 1) l) := by
    intro s l
    rw [hZ]
    split_ifs with hf
    · exact clS_int_of_div hq0 (huv _)
    · exact ciIntAt_zero
  have hZb : ∀ s l, IntAt P (((q : E) ^ b)⁻¹ * (Loc.xx1 yj v - Loc.xx1 yj u) (Pi.single s 1) l) := by
    intro s l
    rw [hZ]
    split_ifs with hf
    · have e : ((q : E) ^ b)⁻¹ * (v ⟨(l, s), hf⟩ - u ⟨(l, s), hf⟩) = (q : E) ^ (B - b) * ((v ⟨(l, s), hf⟩ - u ⟨(l, s), hf⟩) / (q : E) ^ B) := by
        have e2 : (q : E) ^ B = (q : E) ^ (B - b) * (q : E) ^ b := by rw [← pow_add, Nat.sub_add_cancel hB]
        rw [e2]
        field_simp
      rw [e]
      exact clS_bd_int _ (huv _)
    · rw [mul_zero]
      exact ciIntAt_zero
  have hv : Loc.xx1 yj v = Loc.xx1 yj u + (Loc.xx1 yj v - Loc.xx1 yj u) := by abel
  have hΨ : Ψ (Loc.xx1 yj v) = Ψ (Loc.xx1 yj u) := by
    rw [hv]
    exact hinv _ _ hZb
  unfold clS_G
  rw [hΨ]
  by_cases h0 : Ψ (Loc.xx1 yj u) = 0
  · rw [h0, zero_mul, zero_mul]
  · congr 1
    have hζ : IntAt P (Loc.chArg (n' := n') (c' := c + 1) (n := n) (c := c) (Loc.xx1 yj v - Loc.xx1 yj u)) := by
      have h1 : IntAt P ((q : E) ^ 0 * Loc.chArg (n' := n') (c' := c + 1) (n := n) (c := c) (Loc.xx1 yj v - Loc.xx1 yj u)) :=
        clS_chArg_bd fun s l => by
          rw [pow_zero, one_mul]
          exact hZi s l
      rwa [pow_zero, one_mul] at h1
    rw [hv, clS_chArg_add, neg_add, hadd _ _ (clS_bd_neg (clS_bd_mono (clS_chArg_bd (hsupp _ h0)) haD)) (clS_bd_neg (clS_bd_int _ hζ)),
      hint _ (ciIntAt_neg hζ), mul_one]

def clS_rp (P : HeightOneSpectrum (𝓞 E)) (q A B : ℕ) (v : E) : E :=
  if h : ∃ u ∈ LocE.valsQ E q A B, IntAt P ((v - u) / (q : E) ^ B) then h.choose else 0

theorem clS_rp_spec (hq : ((q : ℕ) : 𝓞 E) ∈ P.asIdeal) (hu : ((q : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) (hp : q.Prime)
    (hcard : Nat.card (𝓞 E ⧸ P.asIdeal) = q) {A B : ℕ} {v : E} (hv : IntAt P ((q : E) ^ A * v)) :
    clS_rp P q A B v ∈ LocE.valsQ E q A B ∧ IntAt P ((v - clS_rp P q A B v) / (q : E) ^ B) := by
  have h := clS_rep hq hu hp hcard A B v hv
  unfold clS_rp
  rw [dif_pos h]
  exact h.choose_spec

theorem clS_bd_of_congr (hq0 : (q : E) ≠ 0) {m B : ℕ} {v u : E} (hv : IntAt P ((q : E) ^ m * v)) (h : IntAt P ((v - u) / (q : E) ^ B)) :
    IntAt P ((q : E) ^ m * u) := by
  have e : u = v - (v - u) := by ring
  rw [e]
  exact clS_bd_sub hv (clS_bd_int _ (clS_int_of_div hq0 h))

theorem free_point_block_entry (yj : HomE E n' n) (u : Loc.FC n' (c + 1) n c → E) (s : Fin n') (l : Fin n) :
    Loc.xx1 yj u (Pi.single (Fin.castAdd (c + 1) s) 1) (Fin.castAdd c l) = yj (Pi.single s 1) l := by
  rw [clS_single_eN, show (Fin.castAdd (c + 1) s).1 = s.1 from rfl, ciEN s.2, free_point_embedding, ciInX_castAdd]

theorem clS_cov (hq : ((q : ℕ) : 𝓞 E) ∈ P.asIdeal) (hu : ((q : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) (hp : q.Prime)
    (hcard : Nat.card (𝓞 E ⧸ P.asIdeal) = q) (psi : E → K) (D a b e : ℕ)
    (hadd : ∀ x y : E, IntAt P ((q : E) ^ D * x) → IntAt P ((q : E) ^ D * y) → psi (x + y) = psi x * psi y)
    (hint : ∀ x : E, IntAt P x → psi x = 1) (Ψ : Loc.SF E K (n' + (c + 1)) (n + c))
    (hsupp : ∀ x, Ψ x ≠ 0 → ∀ s l, IntAt P ((q : E) ^ a * x (Pi.single s 1) l)) (haD : a ≤ D)
    (hinv : ∀ x z, (∀ s l, IntAt P (((q : E) ^ b)⁻¹ * z (Pi.single s 1) l)) → Ψ (x + z) = Ψ x)
    {r : Sp E (n' + (c + 1)) ≃ₗ[E] Sp E (n' + (c + 1))} (hr : r ∈ Loc.R1 E n' (c + 1)) {g : Sp E n' ≃ₗ[E] Sp E n'} (hgG : g ∈ GLint E n' P)
    (hg : ∀ x, r (Loc.inX E n' (c + 1) x) = Loc.inX E n' (c + 1) (g x)) (hre : ∀ s s', IntAt P ((q : E) ^ e * r (Pi.single s 1) s'))
    (heD : e ≤ D) (A B : ℕ) (hA : a + (c + 1) * e ≤ A) (hB : b ≤ B) (wt : K) (y : HomE E n' n) :
    Loc.E1 (n' := n') (c' := c + 1) (n := n) (c := c) psi (LocE.valsQ E q A B) wt (fun x => Ψ (x ∘ₗ r.toLinearMap)) y =
      psi (Loc.n1Arg r) * Loc.E1 (n' := n') (c' := c + 1) (n := n) (c := c) psi (LocE.valsQ E q A B) wt Ψ (y ∘ₗ g.toLinearMap) := by
  have hq0 : (q : E) ≠ 0 := ciQ_ne_zero hu
  have hr1 : Loc.R1cond E n' (c + 1) r := hr.1

  have hterm : ∀ t : Loc.FC n' (c + 1) n c → E,
      Ψ (Loc.xx1 y t ∘ₗ r.toLinearMap) * psi (-Loc.chArg (n' := n') (c' := c + 1) (n := n) (c := c) (Loc.xx1 y t)) =
        psi (Loc.n1Arg r) * clS_G psi Ψ (y ∘ₗ g.toLinearMap) (freeCoordinatesTransform y r t) := by
    intro t
    have e1 := clS_comp hr1 hg y t
    have e2 := clS_chArg hr1 y t
    rw [e1] at e2
    unfold clS_G
    rw [e1]
    by_cases h0 : Ψ (Loc.xx1 (y ∘ₗ g.toLinearMap) (freeCoordinatesTransform y r t)) = 0
    · rw [h0, zero_mul, zero_mul, mul_zero]
    · have hx : -Loc.chArg (n' := n') (c' := c + 1) (n := n) (c := c) (Loc.xx1 y t) =
          Loc.n1Arg r + -Loc.chArg (n' := n') (c' := c + 1) (n := n) (c := c) (Loc.xx1 (y ∘ₗ g.toLinearMap) (freeCoordinatesTransform y r t)) := by
        rw [e2]
        ring
      rw [hx, hadd _ _ (clS_bd_mono (free_argument_integral hre) heD) (clS_bd_neg (clS_bd_mono (clS_chArg_bd (hsupp _ h0)) haD))]
      ring

  have hsum : ∑ t ∈ Fintype.piFinset (fun _ : Loc.FC n' (c + 1) n c => LocE.valsQ E q A B), clS_G psi Ψ (y ∘ₗ g.toLinearMap) (freeCoordinatesTransform y r t) =
      ∑ u ∈ Fintype.piFinset (fun _ : Loc.FC n' (c + 1) n c => LocE.valsQ E q A B), clS_G psi Ψ (y ∘ₗ g.toLinearMap) u := by
    by_cases hyg : ∀ s l, IntAt P ((q : E) ^ a * (y ∘ₗ g.toLinearMap) (Pi.single s 1) l)
    ·
      have hgi : g.symm ∈ GLint E n' P := (GLint E n' P).inv_mem hgG
      have hy : ∀ s l, IntAt P ((q : E) ^ a * y (Pi.single s 1) l) := by
        intro s l
        have e0 : y (Pi.single s 1) l = (y ∘ₗ g.toLinearMap) (g.symm (Pi.single s 1)) l := by
          show _ = y (g (g.symm _)) l
          rw [LinearEquiv.apply_symm_apply]
        rw [e0, clS_apply_sum]
        refine clS_bd_sum _ _ fun j _ => ?_
        have h1 : IntAt P (g.symm (Pi.single s 1) j) := (ciMem_stdAt P _).1 ((hgi _).2 (ciSingle_mem s)) j
        have e3 : (q : E) ^ a * (g.symm (Pi.single s 1) j * (y ∘ₗ g.toLinearMap) (Pi.single j 1) l) =
            g.symm (Pi.single s 1) j * ((q : E) ^ a * (y ∘ₗ g.toLinearMap) (Pi.single j 1) l) := by ring
        rw [e3]
        exact h1.mul (hyg j l)
      have hlev : ∀ p : Loc.FC n' (c + 1) n c, a + (p.1.2.1 - n' + 1) * e ≤ A := by
        intro p
        have h1 := p.1.2.2
        exact le_trans (Nat.add_le_add_left (Nat.mul_le_mul_right e (by omega)) a) hA

      have hTW : ∀ t : Loc.FC n' (c + 1) n c → E, (∀ p, IntAt P ((q : E) ^ (a + (p.1.2.1 - n' + 1) * e) * t p)) →
          ∀ p, IntAt P ((q : E) ^ (a + (p.1.2.1 - n' + 1) * e) * freeCoordinatesTransform y r t p) := by
        intro t ht p
        rw [clS_T_eq hr1]
        exact clS_bd_add (ht p) (clS_phi_bd hy hre p fun p' _ => ht p')
      refine clS_sum_perm _ ((Fintype.piFinset fun _ : Loc.FC n' (c + 1) n c => LocE.valsQ E q A B).filter fun t =>
        ∀ p, IntAt P ((q : E) ^ (a + (p.1.2.1 - n' + 1) * e) * t p)) (Finset.filter_subset _ _) (freeCoordinatesTransform y r)
        (fun t p => clS_rp P q A B (freeCoordinatesTransform y r t p)) (clS_G psi Ψ (y ∘ₗ g.toLinearMap)) ?_ ?_ ?_ ?_ ?_
      ·
        intro t ht h
        refine Finset.mem_filter.2 ⟨ht, ?_⟩
        have hΨ : Ψ (Loc.xx1 (y ∘ₗ g.toLinearMap) (freeCoordinatesTransform y r t)) ≠ 0 := left_ne_zero_of_mul h
        have hT : ∀ p, IntAt P ((q : E) ^ a * freeCoordinatesTransform y r t p) := by
          intro p
          have h1 := hsupp _ hΨ p.1.2 p.1.1
          rwa [free_point_column_formula, dif_pos p.2] at h1
        have key : ∀ N : ℕ, ∀ p : Loc.FC n' (c + 1) n c, p.1.2.1 - n' ≤ N → IntAt P ((q : E) ^ (a + (p.1.2.1 - n' + 1) * e) * t p) := by
          intro N
          induction N with
          | zero =>
            intro p hpN
            have e0 : t p = freeCoordinatesTransform y r t p - clS_phi y r t p := by rw [clS_T_eq hr1]; ring
            rw [e0]
            exact clS_bd_sub (clS_bd_mono (hT p) (Nat.le_add_right _ _)) (clS_phi_bd hy hre p fun p' hp' => absurd hp' (by omega))
          | succ N ih =>
            intro p hpN
            have e0 : t p = freeCoordinatesTransform y r t p - clS_phi y r t p := by rw [clS_T_eq hr1]; ring
            rw [e0]
            exact clS_bd_sub (clS_bd_mono (hT p) (Nat.le_add_right _ _)) (clS_phi_bd hy hre p fun p' hp' => ih p' (by omega))
        exact fun p => key _ p le_rfl
      ·
        intro u hu' h
        refine Finset.mem_filter.2 ⟨hu', fun p => ?_⟩
        have hΨ : Ψ (Loc.xx1 (y ∘ₗ g.toLinearMap) u) ≠ 0 := left_ne_zero_of_mul h
        have h1 := hsupp _ hΨ p.1.2 p.1.1
        rw [free_point_column_formula, dif_pos p.2] at h1
        exact clS_bd_mono h1 (Nat.le_add_right _ _)
      ·
        intro t ht
        have ht2 := (Finset.mem_filter.1 ht).2
        have hsp := fun p => clS_rp_spec hq hu hp hcard (A := A) (B := B) (clS_bd_mono (hTW t ht2 p) (hlev p))
        exact Finset.mem_filter.2 ⟨Fintype.mem_piFinset.2 fun p => (hsp p).1, fun p => clS_bd_of_congr hq0 (hTW t ht2 p) (hsp p).2⟩
      ·
        intro t ht t' ht' hσ
        have ht1 := Fintype.mem_piFinset.1 (Finset.mem_filter.1 (Finset.mem_coe.1 ht)).1
        have ht1' := Fintype.mem_piFinset.1 (Finset.mem_filter.1 (Finset.mem_coe.1 ht')).1
        have ht2 := (Finset.mem_filter.1 (Finset.mem_coe.1 ht)).2
        have ht2' := (Finset.mem_filter.1 (Finset.mem_coe.1 ht')).2
        have hsp := fun p => clS_rp_spec hq hu hp hcard (A := A) (B := B) (clS_bd_mono (hTW t ht2 p) (hlev p))
        have hsp' := fun p => clS_rp_spec hq hu hp hcard (A := A) (B := B) (clS_bd_mono (hTW t' ht2' p) (hlev p))
        have step : ∀ p : Loc.FC n' (c + 1) n c, (∀ p' : Loc.FC n' (c + 1) n c, p'.1.2.1 - n' < p.1.2.1 - n' → t p' = t' p') → t p = t' p := by
          intro p hlow
          refine clS_rep_unique hq hu hp (ht1 p) (ht1' p) ?_
          have e0 : clS_rp P q A B (freeCoordinatesTransform y r t p) = clS_rp P q A B (freeCoordinatesTransform y r t' p) := congrFun hσ p
          have e1 : (t p - t' p) / (q : E) ^ B = (freeCoordinatesTransform y r t p - clS_rp P q A B (freeCoordinatesTransform y r t p)) / (q : E) ^ B -
              (freeCoordinatesTransform y r t' p - clS_rp P q A B (freeCoordinatesTransform y r t' p)) / (q : E) ^ B := by
            rw [e0, clS_T_eq hr1, clS_T_eq hr1, clS_phi_congr y r p hlow]
            ring
          rw [e1]
          exact ciIntAt_sub (hsp p).2 (hsp' p).2
        have key : ∀ N : ℕ, ∀ p : Loc.FC n' (c + 1) n c, p.1.2.1 - n' ≤ N → t p = t' p := by
          intro N
          induction N with
          | zero => exact fun p hpN => step p fun p' hp' => absurd hp' (by omega)
          | succ N ih => exact fun p hpN => step p fun p' hp' => ih p' (by omega)
        exact funext fun p => key _ p le_rfl
      ·
        intro t ht
        have ht2 := (Finset.mem_filter.1 ht).2
        refine clS_G_congr hq0 psi hadd hint Ψ hsupp haD hinv hB _ _ _ fun p => ?_
        have h1 := (clS_rp_spec hq hu hp hcard (A := A) (B := B) (clS_bd_mono (hTW t ht2 p) (hlev p))).2
        have e1 : (clS_rp P q A B (freeCoordinatesTransform y r t p) - freeCoordinatesTransform y r t p) / (q : E) ^ B =
            -((freeCoordinatesTransform y r t p - clS_rp P q A B (freeCoordinatesTransform y r t p)) / (q : E) ^ B) := by ring
        rw [e1]
        exact ciIntAt_neg h1
    ·
      have hG0 : ∀ u, clS_G psi Ψ (y ∘ₗ g.toLinearMap) u = 0 := by
        intro u
        by_contra hne
        have hΨ : Ψ (Loc.xx1 (y ∘ₗ g.toLinearMap) u) ≠ 0 := left_ne_zero_of_mul hne
        refine hyg fun s l => ?_
        have h1 := hsupp _ hΨ (Fin.castAdd (c + 1) s) (Fin.castAdd c l)
        rwa [free_point_block_entry] at h1
      rw [Finset.sum_eq_zero fun t _ => hG0 _, Finset.sum_eq_zero fun u _ => hG0 u]
  show wt ^ _ * ∑ t ∈ _, Ψ (Loc.xx1 y t ∘ₗ r.toLinearMap) * psi (-Loc.chArg (n' := n') (c' := c + 1) (n := n) (c := c) (Loc.xx1 y t)) =
    psi (Loc.n1Arg r) * (wt ^ _ * ∑ u ∈ _, clS_G psi Ψ (y ∘ₗ g.toLinearMap) u)
  rw [Finset.sum_congr rfl fun t _ => hterm t, ← Finset.mul_sum, hsum]
  ring

end Main

end Formalism.L2.Col
