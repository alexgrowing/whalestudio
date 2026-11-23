import Formalism.LocalToGlobal.CharacterGerms.RowTieCartFB

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ MvPowerSeries

variable {C : Type} [Field C]

section Coeff

variable {τ : Type}

theorem Van.sub {T : Set τ} {f g : MvPowerSeries τ C} (hf : Van T f) (hg : Van T g) : Van T (f - g) := by
  intro ν hν
  rw [map_sub, hf ν hν, hg ν hν, sub_zero]

theorem Van.mul_left {T : Set τ} {f : MvPowerSeries τ C} (hf : Van T f) (g : MvPowerSeries τ C) : Van T (g * f) := by
  rw [mul_comm]
  exact hf.mul_right g

theorem van_prod {σ : Type} {T : Set τ} {a : σ → MvPowerSeries τ C} {e : σ →₀ ℕ} {s : σ} (hs : s ∈ e.support)
    (ha : Van T (a s)) : Van T (e.prod fun s m => a s ^ m) := by
  unfold Finsupp.prod
  rw [← Finset.mul_prod_erase _ _ hs]
  apply Van.mul_right
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Finsupp.mem_support_iff.1 hs)
  show Van T (a s ^ e s)
  rw [hm, pow_succ']
  exact ha.mul_right _

theorem coeff_mul_van_van {T : Set τ} {F G : MvPowerSeries τ C} (hF : Van T F) (hG : Van T G) (e : τ →₀ ℕ) (P : τ)
    (he : ∀ s ∈ T, e s ≠ 0 → s = P) (hP : e P ≤ 1) : coeff e (F * G) = 0 := by
  rw [coeff_mul]
  apply Finset.sum_eq_zero
  rintro ⟨a, b⟩ hab
  have hab' : a + b = e := Finset.HasAntidiagonal.mem_antidiagonal.1 hab
  by_cases ha : ∀ w ∈ a.support, w ∉ T
  · rw [hF a ha, zero_mul]
  · by_cases hb : ∀ w ∈ b.support, w ∉ T
    · rw [hG b hb, mul_zero]
    · exfalso
      push Not at ha hb
      obtain ⟨s, hs, hsT⟩ := ha
      obtain ⟨s', hs', hsT'⟩ := hb
      have h1 : a s ≠ 0 := Finsupp.mem_support_iff.1 hs
      have h2 : b s' ≠ 0 := Finsupp.mem_support_iff.1 hs'
      have e1 : e s = a s + b s := by rw [← hab']; rfl
      have e2 : e s' = a s' + b s' := by rw [← hab']; rfl
      have hsP : s = P := he s hsT (by omega)
      have hsP' : s' = P := he s' hsT' (by omega)
      subst hsP
      subst hsP'
      omega

def E2 (P Q : τ) : τ →₀ ℕ := Finsupp.single P 1 + Finsupp.single Q 1

theorem exchangeTwo_self_eq_one {P Q : τ} (h : P ≠ Q) : E2 P Q P = 1 := by
  simp [E2, h.symm]

theorem elementary_pair_apply_second {P Q : τ} (h : P ≠ Q) : E2 P Q Q = 1 := by
  simp [E2, h]

theorem elementary_pair_eq_zero_of_ne {P Q s : τ} (h1 : s ≠ P) (h2 : s ≠ Q) : E2 P Q s = 0 := by
  simp [E2, h1.symm, h2.symm]

theorem elementary_pair_support {P Q s : τ} (h : E2 P Q s ≠ 0) : s = P ∨ s = Q := by
  by_contra hc
  push Not at hc
  exact h (elementary_pair_eq_zero_of_ne hc.1 hc.2)

theorem coeff_mul_van_two {T1 T2 : Set τ} {F G : MvPowerSeries τ C} (hF : Van T1 F) (hG : Van T2 G) {P Q : τ}
    (hPQ : P ≠ Q) (hQ : Q ∉ T1) (hP : P ∉ T2) :
    coeff (E2 P Q) (F * G) = coeff (Finsupp.single P 1) F * coeff (Finsupp.single Q 1) G := by
  rw [coeff_mul]
  rw [Finset.sum_eq_single ((Finsupp.single P 1, Finsupp.single Q 1) : (τ →₀ ℕ) × (τ →₀ ℕ))]
  · rintro ⟨a, b⟩ hab hne
    have hab' : a + b = E2 P Q := Finset.HasAntidiagonal.mem_antidiagonal.1 hab
    have hs : ∀ s, a s + b s = E2 P Q s := fun s => by rw [← hab']; rfl
    by_cases ha : ∀ w ∈ a.support, w ∉ T1
    · rw [hF a ha, zero_mul]
    · by_cases hb : ∀ w ∈ b.support, w ∉ T2
      · rw [hG b hb, mul_zero]
      · exfalso
        push Not at ha hb
        obtain ⟨s, hs1, hsT⟩ := ha
        obtain ⟨s', hs1', hsT'⟩ := hb
        have h1 : a s ≠ 0 := Finsupp.mem_support_iff.1 hs1
        have h2 : b s' ≠ 0 := Finsupp.mem_support_iff.1 hs1'
        have hsP : s = P := by
          rcases elementary_pair_support (P := P) (Q := Q) (s := s) (by have := hs s; omega) with h | h
          · exact h
          · exact absurd (h ▸ hsT) hQ
        have hsQ : s' = Q := by
          rcases elementary_pair_support (P := P) (Q := Q) (s := s') (by have := hs s'; omega) with h | h
          · exact absurd (h ▸ hsT') hP
          · exact h
        subst hsP
        subst hsQ
        have hP1 := hs s
        have hQ1 := hs s'
        rw [exchangeTwo_self_eq_one hPQ] at hP1
        rw [elementary_pair_apply_second hPQ] at hQ1
        apply hne
        have ea : a = Finsupp.single s 1 := by
          ext x
          by_cases hx : x = s
          · subst hx; simp; omega
          · by_cases hx' : x = s'
            · subst hx'; rw [Finsupp.single_apply, if_neg (Ne.symm hx)]; omega
            · have := hs x
              rw [elementary_pair_eq_zero_of_ne hx hx'] at this
              rw [Finsupp.single_apply, if_neg (Ne.symm hx)]; omega
        have eb : b = Finsupp.single s' 1 := by
          ext x
          by_cases hx' : x = s'
          · subst hx'; simp; omega
          · by_cases hx : x = s
            · subst hx; rw [Finsupp.single_apply, if_neg (Ne.symm hx')]; omega
            · have := hs x
              rw [elementary_pair_eq_zero_of_ne hx hx'] at this
              rw [Finsupp.single_apply, if_neg (Ne.symm hx')]; omega
        rw [ea, eb]
  · intro h
    refine absurd ?_ h
    rw [Finset.HasAntidiagonal.mem_antidiagonal]
    unfold E2
    rfl

end Coeff

section Subst

variable {τ κ : Type} [Fintype κ]

theorem elementary_pair_injective {i i' j j' : κ} (h : E2 ((0 : Fin 2), i) ((1 : Fin 2), j) = E2 ((0 : Fin 2), i') ((1 : Fin 2), j')) :
    i = i' ∧ j = j' := by
  have hne : ∀ x y : κ, ((0 : Fin 2), x) ≠ ((1 : Fin 2), y) := fun x y e => by
    have h01 : (0 : Fin 2) = 1 := congrArg Prod.fst e
    exact absurd h01 (by decide)
  constructor
  · have h1 : E2 ((0 : Fin 2), i') ((1 : Fin 2), j') ((0 : Fin 2), i) ≠ 0 := by
      rw [← h, exchangeTwo_self_eq_one (hne i j)]; exact one_ne_zero
    rcases elementary_pair_support h1 with e | e
    · exact (Prod.mk.inj e).2
    · exact absurd e (hne i j')
  · have h1 : E2 ((0 : Fin 2), i') ((1 : Fin 2), j') ((1 : Fin 2), j) ≠ 0 := by
      rw [← h, elementary_pair_apply_second (hne i j)]; exact one_ne_zero
    rcases elementary_pair_support h1 with e | e
    · exact absurd e.symm (hne i' j)
    · exact (Prod.mk.inj e).2

theorem coeff_subst_bil {T1 T2 : Set τ} {a : Fin 2 × κ → MvPowerSeries τ C}
    (ha0 : ∀ s, constantCoeff (a s) = 0) (hax : ∀ i, Van T1 (a (0, i))) (haz : ∀ j, Van T2 (a (1, j)))
    {P Q : τ} (hPQ : P ≠ Q) (hQ : Q ∉ T1) (hP : P ∉ T2) {h : MvPowerSeries (Fin 2 × κ) C}
    (hh : ∀ (g : Fin 2) (e : Fin 2 × κ →₀ ℕ), (∀ s ∈ e.support, s.1 ≠ g) → coeff e h = 0) :
    coeff (E2 P Q) (MvPowerSeries.subst a h) =
      ∑ i, ∑ j, coeff (E2 ((0 : Fin 2), i) ((1 : Fin 2), j)) h *
        (coeff (Finsupp.single P 1) (a (0, i)) * coeff (Finsupp.single Q 1) (a (1, j))) := by
  have hne : ∀ x y : κ, ((0 : Fin 2), x) ≠ ((1 : Fin 2), y) := fun x y e => by
    have h01 : (0 : Fin 2) = 1 := congrArg Prod.fst e
    exact absurd h01 (by decide)
  have he1 : ∀ s ∈ T1, E2 P Q s ≠ 0 → s = P := fun s hs h0 => by
    rcases elementary_pair_support h0 with e | e
    · exact e
    · exact absurd (e ▸ hs) hQ
  have he2 : ∀ s ∈ T2, E2 P Q s ≠ 0 → s = Q := fun s hs h0 => by
    rcases elementary_pair_support h0 with e | e
    · exact absurd (e ▸ hs) hP
    · exact e
  rw [coeff_subst (hasSubst_of_constantCoeff_zero ha0)]
  have hprod : ∀ (i j : κ) (d' : Fin 2 × κ →₀ ℕ),
      ((E2 ((0 : Fin 2), i) ((1 : Fin 2), j) + d').prod fun s m => a s ^ m) =
        a (0, i) * a (1, j) * d'.prod fun s m => a s ^ m := by
    intro i j d'
    unfold E2
    rw [Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _),
      Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _),
      Finsupp.prod_single_index (h := fun s m => a s ^ m) (pow_zero _),
      Finsupp.prod_single_index (h := fun s m => a s ^ m) (pow_zero _), pow_one, pow_one]
  have hsupp : (Function.support fun d : Fin 2 × κ →₀ ℕ =>
      coeff d h • coeff (E2 P Q) (d.prod fun s m => a s ^ m)) ⊆
      ↑((Finset.univ : Finset (κ × κ)).image fun ij => E2 ((0 : Fin 2), ij.1) ((1 : Fin 2), ij.2)) := by
    intro d hd
    by_contra hnot
    apply hd
    show coeff d h • coeff (E2 P Q) (d.prod fun s m => a s ^ m) = 0
    by_cases hx : ∀ s ∈ d.support, s.1 ≠ 0
    · rw [hh 0 d hx, zero_smul]
    by_cases hz : ∀ s ∈ d.support, s.1 ≠ 1
    · rw [hh 1 d hz, zero_smul]
    push Not at hx hz
    obtain ⟨⟨g, i⟩, hs, hg⟩ := hx
    obtain ⟨⟨g', j⟩, hs', hg'⟩ := hz
    have hg0 : g = 0 := hg
    have hg1 : g' = 1 := hg'
    subst hg0
    subst hg1
    have hle : E2 ((0 : Fin 2), i) ((1 : Fin 2), j) ≤ d := by
      intro x
      by_cases h1 : x = ((0 : Fin 2), i)
      · rw [h1, exchangeTwo_self_eq_one (hne i j)]
        exact Nat.one_le_iff_ne_zero.2 (Finsupp.mem_support_iff.1 hs)
      · by_cases h2 : x = ((1 : Fin 2), j)
        · rw [h2, elementary_pair_apply_second (hne i j)]
          exact Nat.one_le_iff_ne_zero.2 (Finsupp.mem_support_iff.1 hs')
        · rw [elementary_pair_eq_zero_of_ne h1 h2]
          exact Nat.zero_le _
    have hd' : d = E2 ((0 : Fin 2), i) ((1 : Fin 2), j) + (d - E2 ((0 : Fin 2), i) ((1 : Fin 2), j)) :=
      (add_tsub_cancel_of_le hle).symm
    set d' := d - E2 ((0 : Fin 2), i) ((1 : Fin 2), j) with hd'def
    have hd'0 : d' ≠ 0 := by
      intro h0
      apply hnot
      rw [Finset.coe_image, Set.mem_image]
      exact ⟨(i, j), by simp, by rw [hd', h0, add_zero]⟩
    obtain ⟨⟨g'', t⟩, hs''⟩ := Finsupp.support_nonempty_iff.2 hd'0
    rw [hd', hprod]
    have hall : ∀ x : Fin 2, x = 0 ∨ x = 1 := by decide
    have hcase : g'' = 0 ∨ g'' = 1 := hall g''
    rcases hcase with rfl | rfl
    · rw [mul_assoc, coeff_mul_van_van (hax i) ((van_prod hs'' (hax t)).mul_left _) (E2 P Q) P he1
        (le_of_eq (exchangeTwo_self_eq_one hPQ)), smul_zero]
    · rw [mul_comm (a (0, i)), mul_assoc, coeff_mul_van_van (haz j) ((van_prod hs'' (haz t)).mul_left _) (E2 P Q) Q he2
        (le_of_eq (elementary_pair_apply_second hPQ)), smul_zero]
  rw [finsum_eq_sum_of_support_subset _ hsupp, Finset.sum_image, Fintype.sum_prod_type]
  · apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    have := hprod i j 0
    rw [add_zero, Finsupp.prod_zero_index, mul_one] at this
    rw [this, coeff_mul_van_two (hax i) (haz j) hPQ hQ hP, smul_eq_mul]
  · intro x _ y _ hxy
    obtain ⟨h1, h2⟩ := elementary_pair_injective hxy
    exact Prod.ext h1 h2

end Subst

section Exp

variable [CharZero C] {n dd : ℕ}

theorem coeff_expS_bil {T : Set (Fin n × Fin dd)} {f : PS C n dd} (hf : Van T f) (e : Fin n × Fin dd →₀ ℕ)
    (P : Fin n × Fin dd) (he : ∀ s ∈ T, e s ≠ 0 → s = P) (hP : e P ≤ 1) (he0 : e ≠ 0) :
    coeff e (FB.expS C f) = coeff e f := by
  unfold FB.expS
  have h0 : PowerSeries.HasSubst f := PowerSeries.HasSubst.of_constantCoeff_zero hf.const
  rw [PowerSeries.coeff_subst h0, finsum_eq_single _ 1]
  · simp [PowerSeries.coeff_exp]
  · intro m hm
    rcases m with _ | _ | k
    · rw [pow_zero, coeff_one, if_neg he0, smul_zero]
    · exact absurd rfl hm
    · have e2 : f ^ (k + 1 + 1) = f * (f * f ^ k) := by ring
      rw [e2, coeff_mul_van_van hf (hf.mul_right _) e P he hP, smul_zero]

end Exp

section Bil

variable {dd : ℕ}

def Tg (dd : ℕ) (g : Fin 2) : Set (Fin 2 × Fin dd) := {s | s.1 = g}

theorem van_X {τ : Type} {T : Set τ} {s : τ} (hs : s ∈ T) : Van T (X s : MvPowerSeries τ C) := by
  intro ν hν
  rw [coeff_X, if_neg]
  intro h
  exact hν s (by rw [h]; simp) hs

def bil (F : PS C 2 dd) (w v : Fin dd → C) : C :=
  ∑ i, ∑ j, coeff (E2 ((0 : Fin 2), i) ((1 : Fin 2), j)) F * (w i * v j)

theorem bil_smul_left (F : PS C 2 dd) (c : C) (w v : Fin dd → C) : bil F (c • w) v = c * bil F w v := by
  unfold bil
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem bil_smul_right (F : PS C 2 dd) (c : C) (w v : Fin dd → C) : bil F w (c • v) = c * bil F w v := by
  unfold bil
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem bil_sub (F G : PS C 2 dd) (w v : Fin dd → C) : bil (F - G) w v = bil F w v - bil G w v := by
  unfold bil
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_sub, sub_mul]

theorem bil_int {V : VF C} {F : PS C 2 dd} (hF : IntS V F) {w v : Fin dd → C} (hw : ∀ i, V.Ge 0 (w i))
    (hv : ∀ i, V.Ge 0 (v i)) : V.Ge 0 (bil F w v) :=
  VF.Ge.sum fun i _ => VF.Ge.sum fun j _ => (hF _).mul_int ((hw i).mul_int (hv j))

theorem comp_coordinate_point (φ : Pt C 1 dd) (g : Fin 2) (i : Fin dd) :
    comp1 φ (pt C (n := 2) dd g) i =
      MvPowerSeries.subst (fun q : Fin 1 × Fin dd => (X (g, q.2) : PS C 2 dd)) (φ i) := by
  show ev ![pt C (n := 2) dd g] (φ i) = _
  rw [eval_single_eq_subst]
  rfl

theorem van_comp1_pt {φ : Pt C 1 dd} (hφ : ∀ i, constantCoeff (φ i) = 0) (g : Fin 2) (i : Fin dd) :
    Van (Tg dd g) (comp1 φ (pt C (n := 2) dd g) i) := by
  rw [comp_coordinate_point]
  exact Van.subst Set.univ (fun _ => constantCoeff_X _) (fun q _ => van_X (show (g, q.2) ∈ Tg dd g from rfl))
    (van_univ (hφ i))

theorem coeff_comp1_pt (φ : Pt C 1 dd) (g : Fin 2) (i k : Fin dd) :
    coeff (Finsupp.single (g, k) 1) (comp1 φ (pt C (n := 2) dd g) i) =
      coeff (Finsupp.single ((0 : Fin 1), k) 1) (φ i) := by
  rw [comp_coordinate_point]
  have hinj : Function.Injective (fun q : Fin 1 × Fin dd => (g, q.2)) := fun x y h =>
    Prod.ext (Subsingleton.elim _ _) (Prod.mk.inj h).2
  have := coeff_subst_rename_inj (C := C) (fun q : Fin 1 × Fin dd => (g, q.2)) hinj (φ i)
    (Finsupp.single ((0 : Fin 1), k) 1)
  rw [Finsupp.mapDomain_single] at this
  exact this

theorem coeff_single_X (g : Fin 2) (j k : Fin dd) :
    coeff (Finsupp.single (g, k) 1) (X (g, j) : PS C 2 dd) = if j = k then 1 else 0 := by
  rw [coeff_X]
  by_cases h : j = k
  · subst h; simp
  · rw [if_neg h, if_neg]
    intro e
    exact h (Prod.mk.inj ((Finsupp.single_left_inj one_ne_zero).1 e)).2.symm

theorem ne01 (x y : Fin dd) : ((0 : Fin 2), x) ≠ ((1 : Fin 2), y) := fun e => by
  have h01 : (0 : Fin 2) = 1 := congrArg Prod.fst e
  exact absurd h01 (by decide)

variable {h : PS C 2 dd}
  (hh : ∀ (g : Fin 2) (e : Fin 2 × Fin dd →₀ ℕ), (∀ s ∈ e.support, s.1 ≠ g) → coeff e h = 0)
  {φ : Pt C 1 dd} (hφ : ∀ i, constantCoeff (φ i) = 0)

include hh hφ

theorem coeff_ev_left (i0 j0 : Fin dd) :
    coeff (E2 ((0 : Fin 2), i0) ((1 : Fin 2), j0)) (ev (n := 2) ![comp1 φ (pt C dd 0), pt C dd 1] h) =
      ∑ i, coeff (E2 ((0 : Fin 2), i) ((1 : Fin 2), j0)) h * coeff (Finsupp.single ((0 : Fin 1), i0) 1) (φ i) := by
  unfold ev
  rw [coeff_subst_bil (T1 := Tg dd 0) (T2 := Tg dd 1) (κ := Fin dd)
    (a := fun p : Fin 2 × Fin dd => ![comp1 φ (pt C (n := 2) dd 0), pt C dd 1] p.1 p.2) ?_ (fun i => van_comp1_pt hφ 0 i)
    (fun j => van_X (show ((1 : Fin 2), j) ∈ Tg dd 1 from rfl)) (ne01 i0 j0)
    (fun e => absurd (show (1 : Fin 2) = 0 from e) (by decide))
    (fun e => absurd (show (0 : Fin 2) = 1 from e) (by decide)) hh]
  · apply Finset.sum_congr rfl
    intro i _
    have h1 : ∀ j, coeff (Finsupp.single ((1 : Fin 2), j0) 1)
        ((![comp1 φ (pt C (n := 2) dd 0), pt C dd 1] ((1 : Fin 2), j).1) ((1 : Fin 2), j).2) = if j = j0 then 1 else 0 :=
      fun j => coeff_single_X 1 j j0
    have h2 : coeff (Finsupp.single ((0 : Fin 2), i0) 1)
        ((![comp1 φ (pt C (n := 2) dd 0), pt C dd 1] ((0 : Fin 2), i).1) ((0 : Fin 2), i).2) =
          coeff (Finsupp.single ((0 : Fin 1), i0) 1) (φ i) := coeff_comp1_pt φ 0 i i0
    simp only [h1, h2]
    simp
  · rintro ⟨g, i⟩
    have hall : ∀ x : Fin 2, x = 0 ∨ x = 1 := by decide
    rcases hall g with rfl | rfl
    · exact (van_comp1_pt hφ 0 i).const
    · exact constantCoeff_X _

theorem coeff_ev_right (i0 j0 : Fin dd) :
    coeff (E2 ((0 : Fin 2), i0) ((1 : Fin 2), j0)) (ev (n := 2) ![pt C dd 0, comp1 φ (pt C dd 1)] h) =
      ∑ j, coeff (E2 ((0 : Fin 2), i0) ((1 : Fin 2), j)) h * coeff (Finsupp.single ((0 : Fin 1), j0) 1) (φ j) := by
  unfold ev
  rw [coeff_subst_bil (T1 := Tg dd 0) (T2 := Tg dd 1) (κ := Fin dd)
    (a := fun p : Fin 2 × Fin dd => ![pt C (n := 2) dd 0, comp1 φ (pt C dd 1)] p.1 p.2) ?_
    (fun i => van_X (show ((0 : Fin 2), i) ∈ Tg dd 0 from rfl)) (fun j => van_comp1_pt hφ 1 j) (ne01 i0 j0)
    (fun e => absurd (show (1 : Fin 2) = 0 from e) (by decide))
    (fun e => absurd (show (0 : Fin 2) = 1 from e) (by decide)) hh]
  · have h1 : ∀ i, coeff (Finsupp.single ((0 : Fin 2), i0) 1)
        ((![pt C (n := 2) dd 0, comp1 φ (pt C dd 1)] ((0 : Fin 2), i).1) ((0 : Fin 2), i).2) = if i = i0 then 1 else 0 :=
      fun i => coeff_single_X 0 i i0
    have h2 : ∀ j, coeff (Finsupp.single ((1 : Fin 2), j0) 1)
        ((![pt C (n := 2) dd 0, comp1 φ (pt C dd 1)] ((1 : Fin 2), j).1) ((1 : Fin 2), j).2) =
          coeff (Finsupp.single ((0 : Fin 1), j0) 1) (φ j) := fun j => coeff_comp1_pt φ 1 j j0
    simp only [h1, h2]
    simp
  · rintro ⟨g, i⟩
    have hall : ∀ x : Fin 2, x = 0 ∨ x = 1 := by decide
    rcases hall g with rfl | rfl
    · exact constantCoeff_X _
    · exact (van_comp1_pt hφ 1 i).const

theorem bil_ev_left (w v : Fin dd → C) :
    bil (ev (n := 2) ![comp1 φ (pt C dd 0), pt C dd 1] h) w v = bil h (linAct φ w) v := by
  unfold bil linAct
  simp only [coeff_ev_left hh hφ, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem bil_ev_right (w v : Fin dd → C) :
    bil (ev (n := 2) ![pt C dd 0, comp1 φ (pt C dd 1)] h) w v = bil h w (linAct φ v) := by
  unfold bil linAct
  simp only [coeff_ev_right hh hφ, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  ring

end Bil

section Final

variable [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}

theorem map_self {σ : Type} (F : MvPowerSeries σ C) : MvPowerSeries.map (algebraMap C C) F = F := by
  ext e
  simp

theorem fin_two_eq_zero_or_eq_one : ∀ x : Fin 2, x = 0 ∨ x = 1 := by decide

theorem FBChart.axisAll (Y : FBChart C V O dd) (g : Fin 2) (e : Fin 2 × Fin dd →₀ ℕ)
    (he : ∀ s ∈ e.support, s.1 ≠ g) : coeff e Y.h = 0 := by
  rcases fin_two_eq_zero_or_eq_one g with rfl | rfl
  · refine coeff_of_ev_zero Y.h 0 ![0, pt C dd 0] rfl ?_ Y.gauge.ax0 e he
    intro g' hg'
    rw [fin_two_eq_one_sub_of_ne' 0 g' hg']
    rfl
  · refine coeff_of_ev_zero Y.h 1 ![pt C dd 0, 0] rfl ?_ Y.gauge.ax1 e he
    intro g' hg'
    rw [fin_two_eq_one_sub_of_ne' 1 g' hg']
    rfl

theorem van_ev_left {h : PS C 2 dd}
    (hh : ∀ (g : Fin 2) (e : Fin 2 × Fin dd →₀ ℕ), (∀ s ∈ e.support, s.1 ≠ g) → coeff e h = 0)
    {φ : Pt C 1 dd} (hφ : ∀ i, constantCoeff (φ i) = 0) :
    Van (Tg dd 0) (ev (n := 2) ![comp1 φ (pt C dd 0), pt C dd 1] h) := by
  unfold ev
  refine Van.subst {s : Fin 2 × Fin dd | s.1 = 0} ?_ ?_ (hh 0)
  · rintro ⟨g, i⟩
    rcases fin_two_eq_zero_or_eq_one g with rfl | rfl
    · exact (van_comp1_pt hφ 0 i).const
    · exact constantCoeff_X _
  · rintro ⟨g, i⟩ hs
    have hg : g = 0 := hs
    subst hg
    exact van_comp1_pt hφ 0 i

theorem van_ev_right {h : PS C 2 dd}
    (hh : ∀ (g : Fin 2) (e : Fin 2 × Fin dd →₀ ℕ), (∀ s ∈ e.support, s.1 ≠ g) → coeff e h = 0)
    {φ : Pt C 1 dd} (hφ : ∀ i, constantCoeff (φ i) = 0) :
    Van (Tg dd 0) (ev (n := 2) ![pt C dd 0, comp1 φ (pt C dd 1)] h) := by
  unfold ev
  refine Van.subst {s : Fin 2 × Fin dd | s.1 = 0} ?_ ?_ (hh 0)
  · rintro ⟨g, i⟩
    rcases fin_two_eq_zero_or_eq_one g with rfl | rfl
    · exact constantCoeff_X _
    · exact (van_comp1_pt hφ 1 i).const
  · rintro ⟨g, i⟩ hs
    have hg : g = 0 := hs
    subst hg
    exact van_X (show ((0 : Fin 2), i) ∈ Tg dd 0 from rfl)

theorem bil_expS {f : PS C 2 dd} (hf : Van (Tg dd 0) f) (w v : Fin dd → C) : bil (FB.expS C f) w v = bil f w v := by
  unfold bil
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [coeff_expS_bil hf (E2 ((0 : Fin 2), i) ((1 : Fin 2), j)) ((0 : Fin 2), i) ?_ (le_of_eq (exchangeTwo_self_eq_one (ne01 i j))) ?_]
  · intro s hs h0
    rcases elementary_pair_support h0 with e | e
    · exact e
    · have h1 : s.1 = 0 := hs
      rw [e] at h1
      have h2 : (1 : Fin 2) = 0 := h1
      exact absurd h2 (by decide)
  · intro h0
    have := exchangeTwo_self_eq_one (ne01 i j)
    rw [h0] at this
    exact absurd this (by simp)

theorem FBChart.bil_ad (Y : FBChart C V O dd) (a : O) (w v : Fin dd → C) :
    bil (Y.B.ad a) w v = bil Y.h (linAct (Y.B.A.act a) w) v - bil Y.h w (linAct (Y.B.A.act (star a)) v) := by
  have hg := Y.gauge.ad a
  have hact : ∀ x, Y.B.actK C x = Y.B.A.act x := fun x => funext fun i => map_self _
  rw [hact, hact] at hg
  have hk : FB.toK C (Y.B.ad a) = Y.B.ad a := map_self _
  rw [hk] at hg
  rw [hg, bil_expS ((van_ev_left Y.axisAll (Y.B.A.const a)).sub (van_ev_right Y.axisAll (Y.B.A.const (star a)))),
    bil_sub, bil_ev_left Y.axisAll (Y.B.A.const a), bil_ev_right Y.axisAll (Y.B.A.const (star a))]

theorem FBChart.raw_first_pairing_eq (Y : FBChart C V O dd) {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] (p : PairData Y d I)
    (w v : Fin dd → C) : (Y.raw p).sg1 w v = -bil Y.h w v := by
  have hs : ∀ x, coeff (Finsupp.single x 1) ((Y.raw p).sg v) =
      -∑ i, v i * coeff (E2 ((0 : Fin 2), x) ((1 : Fin 2), i)) Y.h := by
    intro x
    show -∑ i, v i * coeff ((Finsupp.single x 1).mapDomain (fun x : Fin dd => ((0 : Fin 2), x)) +
      Finsupp.single ((1 : Fin 2), i) 1) Y.h = _
    rw [Finsupp.mapDomain_single]
    rfl
  unfold RawChart.sg1 bil
  simp only [hs, mul_neg, Finset.sum_neg_distrib, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

end Final

theorem hStabFB : HStabFBSt := by
  intro C _ _ V O _ _ dd Y d _ I _ p g c q hty
  have hconj : ∀ (g : Fin 2) t a, p.em (1 - g) t (star a) = p.em g t a := by
    intro g t a
    rcases fin_two_eq_zero_or_eq_one g with rfl | rfl
    · show p.em 1 t (star a) = p.em 0 t a
      rw [p.em_conj, star_star]
    · show p.em 0 t (star a) = p.em 1 t a
      rw [p.em_conj]
  obtain ⟨a, ha⟩ := p.em_sep (g, p.ty g c) (g, p.ty (1 - g) q) (fun h => hty (Prod.mk.inj h).2)
  have ha' : V.v (p.em g (p.ty g c) a - p.em g (p.ty (1 - g) q) a) = 0 := ha
  have hb := Y.bil_ad a (p.u g c) (p.u (1 - g) q)
  rw [p.u_eig g c a, p.u_eig (1 - g) q (star a), hconj, bil_smul_left, bil_smul_right, ← sub_mul] at hb
  have hint : V.Ge 0 (bil (Y.B.ad a) (p.u g c) (p.u (1 - g) q)) :=
    bil_int (Y.intAd a) (p.u_int g c) (p.u_int (1 - g) q)
  rw [hb] at hint
  have hβ : V.Ge 0 (bil Y.h (p.u g c) (p.u (1 - g) q)) := by
    unfold VF.Ge at hint ⊢
    rwa [V.v.map_mul, ha', zero_add] at hint
  show V.Ge 0 ((Y.raw p).sg1 (p.u g c) (p.u (1 - g) q))
  rw [Y.raw_first_pairing_eq]
  exact hβ.neg

end Formalism.L2.FormalSeriesBounds
