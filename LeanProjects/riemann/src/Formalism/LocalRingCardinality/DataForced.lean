import Formalism.LocalRingCardinality.DataParams₂
import Formalism.SharpRestriction.GrowthBounds.IsResidueClassZero

noncomputable section

namespace Formalism.BasicNotions

open Formalism.FrobeniusOrbits Formalism.MainNotions.G
open scoped BigOperators

theorem plGG_mem_Psi (D : D7) (z : Bool × HH D) : plGG D z ∈ D.R.Psi := by
  unfold plGG
  split <;> exact (Formalism.HC.Frame.mem_Psi_iff _).2 rfl

def tauPl (D : D7) (z : Bool × HH D) : D.what₂.Tau := D.eTau.symm ⟨plGG D z, plGG_mem_Psi D z⟩

def wPl (D : D7) (j : ℕ) (z : Bool × HH D) : ℝ := wj D j (tauPl D z)

def posPl (D : D7) (p : ℕ) (z : Bool × HH D) (e : ℕ) : Bool × HH D :=
  (xor z.1 (partner D p z.2 e).1, (partner D p z.2 e).2)

theorem positionPlace_conjugate_partner (D : D7) (p : ℕ) (t : HH D) (e : ℕ) : posPl D p (false, t) e = partner D p t e := by
  simp [posPl]

theorem posPl_zero (D : D7) (p : ℕ) (z : Bool × HH D) : posPl D p z 0 = z := by
  simp [posPl, partner]

theorem posPl_add (D : D7) (p : ℕ) (z : Bool × HH D) (a b : ℕ) :
    posPl D p (posPl D p z a) b = posPl D p z (a + b) := by
  unfold posPl partner
  refine Prod.ext ?_ ?_
  · show xor (xor z.1 (decide (IsSg D p ∧ Odd a))) (decide (IsSg D p ∧ Odd b)) =
      xor z.1 (decide (IsSg D p ∧ Odd (a + b)))
    rw [Bool.xor_assoc]
    congr 1
    by_cases hs : IsSg D p
    · have h : ∀ e : ℕ, decide (IsSg D p ∧ Odd e) = decide (Odd e) :=
        fun e => decide_eq_decide.2 ⟨fun h => h.2, fun h => ⟨hs, h⟩⟩
      simp only [h]
      by_cases ha : Odd a <;> by_cases hb : Odd b <;> simp [ha, hb, Nat.odd_add, ← Nat.not_odd_iff_even]
    · have h : ∀ e : ℕ, decide (IsSg D p ∧ Odd e) = false := fun e => decide_eq_false (fun h => hs h.1)
      simp only [h, Bool.xor_false]
  · show z.2 + a • hP D p + b • hP D p = z.2 + (a + b) • hP D p
    rw [add_smul, add_assoc]

instance nP_neZero (D : D7) (p : ℕ) : NeZero (nP D p) := by
  refine ⟨?_⟩
  unfold nP
  split
  · exact (Nat.mul_pos two_pos (addOrderOf_pos _)).ne'
  · exact (addOrderOf_pos _).ne'

theorem posPl_period (D : D7) (p : ℕ) (z : Bool × HH D) : posPl D p z (nP D p) = z := by
  have key : ¬ (IsSg D p ∧ Odd (nP D p)) ∧ nP D p • hP D p = 0 := by
    by_cases hs : IsSg D p
    · have hn : nP D p = 2 * addOrderOf (2 • hP D p) := if_pos hs
      rw [hn]
      refine ⟨fun h => (Nat.not_odd_iff_even.2 (even_two_mul _)) h.2, ?_⟩
      rw [mul_comm, mul_smul]
      exact addOrderOf_nsmul_eq_zero _
    · have hn : nP D p = addOrderOf (hP D p) := if_neg hs
      rw [hn]
      exact ⟨fun h => hs h.1, addOrderOf_nsmul_eq_zero _⟩
  refine Prod.ext ?_ ?_
  · show xor z.1 (decide (IsSg D p ∧ Odd (nP D p))) = z.1
    rw [decide_eq_false key.1, Bool.xor_false]
  · show z.2 + nP D p • hP D p = z.2
    rw [key.2, add_zero]

theorem posPl_mul_period (D : D7) (p : ℕ) (z : Bool × HH D) (c : ℕ) : posPl D p z (nP D p * c) = z := by
  induction c with
  | zero => simpa using posPl_zero D p z
  | succ c ih => rw [Nat.mul_succ, ← posPl_add, ih, posPl_period]

theorem posPl_mod (D : D7) (p : ℕ) (z : Bool × HH D) (e : ℕ) : posPl D p z (e % nP D p) = posPl D p z e := by
  conv_rhs => rw [← Nat.div_add_mod e (nP D p), ← posPl_add, posPl_mul_period]

theorem lpFeasible_shift_sub (l d : ℕ) [NeZero d] (Ds : ZMod d → ℝ) (c : ZMod d) :
    lpFeasible l d (fun s => Ds (s + c)) ⊆ lpFeasible l d Ds := by
  rintro y ⟨xs, h0, hs, hc, rfl⟩
  refine ⟨fun s i => xs (s - c) i, fun s i => h0 _ _, fun s i h => hs _ _ h, fun s => ?_, ?_⟩
  · have h := hc (s - c)
    have e : ∀ i : ℕ, s - (i : ZMod d) - c = s - c - (i : ZMod d) := fun i => sub_right_comm _ _ _
    simp only [sub_add_cancel] at h
    simp only [e]
    exact h
  · exact (Equiv.sum_comp (Equiv.subRight c) (fun s => ∑ i ∈ Finset.range d, xs s i)).symm

theorem lpF_shift (l d : ℕ) [NeZero d] (Ds : ZMod d → ℝ) (c : ZMod d) :
    lpF l d (fun s => Ds (s + c)) = lpF l d Ds := by
  have hset : lpFeasible l d (fun s => Ds (s + c)) = lpFeasible l d Ds := by
    refine Set.Subset.antisymm (lpFeasible_shift_sub l d Ds c) ?_
    have h := lpFeasible_shift_sub l d (fun s => Ds (s + c)) (-c)
    simpa using h
  have hsum : ∑ s, Ds (s + c) = ∑ s, Ds s := Equiv.sum_comp (Equiv.addRight c) Ds
  unfold lpF
  rw [hset, hsum]

def FOrb (D : D7) (j p : ℕ) (z : Bool × HH D) : ℝ :=
  lpF p (nP D p) (fun s => ((D.R.k : ℝ) - 1) * wPl D j (posPl D p z s.val))

theorem FOrb_step (D : D7) (j p : ℕ) (z : Bool × HH D) (e : ℕ) : FOrb D j p (posPl D p z e) = FOrb D j p z := by
  unfold FOrb
  rw [← lpF_shift p (nP D p) (fun s => ((D.R.k : ℝ) - 1) * wPl D j (posPl D p z s.val)) (e : ZMod (nP D p))]
  congr 1
  funext s
  rw [posPl_add, ZMod.val_add, ZMod.val_natCast, posPl_mod, ← posPl_add D p z s.val, posPl_mod, posPl_add,
    add_comm]

open Classical in

def FInert (D : D7) (j p : ℕ) : ℝ :=
  if IsResidueClassZero D p ∧ hP D p = 0 then ∑ τ : D.what₂.Tau, ((D.R.k : ℝ) - 1) * wj D j τ / ((p : ℝ) ^ 2 - 1)
  else (∑ z : Bool × HH D, FOrb D j p z) / (nP D p : ℝ)

def FRamD (D : D7) (j : ℕ) : ℝ :=
  -(((D.R.k : ℝ) - 1) / 2) * ∑ t : HH D, min (wPl D j (false, t)) (wPl D j (true, t))

def fockDeg (D : D7) (j : ℕ) : ℤ :=
  ∑ τ : D.what₂.Tau, ((∑ a, |D.what₂.kaBig j τ a|) + ∑ a, |D.what₂.kaSmall j τ a|)

def FTypeG (D : D7) (j : ℕ) : ℝ := -((fockDeg D j : ℝ)) / 2

open Classical in

def FvalP {D : D7} (L : SizeData₂ D) (j p : ℕ) : ℝ :=
  if p ∈ L.gTypes then FTypeG D j
  else if D.host.cls p = PrimeClass.ramD then FRamD D j
  else if (IsResidueClassZero D p ∨ IsSg D p) ∧ (p : ℝ) ≤ L.sc.X'' D.R.n then FInert D j p
  else 0

def Fval {D : D7} (L : SizeData₂ D) (j : ℕ) (w : D.what₂.places.Pl) : ℝ := FvalP L j (D.what₂.places.resChar w)

def SizeData₂.FDef {D : D7} (L : SizeData₂ D) : Prop :=
  ∀ j ∈ SizeData₂.lifts D, ∀ w, L.F j w = Fval L j w

theorem posPl_fix (D : D7) (p : ℕ) (y : Bool × HH D) (c : ℕ) (h : posPl D p y c = y) : nP D p ∣ c := by
  have h1 : xor y.1 (decide (IsSg D p ∧ Odd c)) = y.1 := congrArg Prod.fst h
  have h2 : y.2 + c • hP D p = y.2 := congrArg Prod.snd h
  have h2' : c • hP D p = 0 := by simpa using h2
  have h1' : ¬ (IsSg D p ∧ Odd c) := by
    intro hc
    rw [decide_eq_true hc] at h1
    cases hy : y.1 <;> simp [hy] at h1
  by_cases hs : IsSg D p
  · have hn : nP D p = 2 * addOrderOf (2 • hP D p) := if_pos hs
    have hev : Even c := Nat.not_odd_iff_even.1 (fun ho => h1' ⟨hs, ho⟩)
    obtain ⟨a, rfl⟩ := hev
    have h3 : a • (2 • hP D p) = 0 := by
      rw [← mul_smul, mul_two]; exact h2'
    rw [hn, ← two_mul]
    exact Nat.mul_dvd_mul_left 2 (addOrderOf_dvd_of_nsmul_eq_zero h3)
  · have hn : nP D p = addOrderOf (hP D p) := if_neg hs
    rw [hn]
    exact addOrderOf_dvd_of_nsmul_eq_zero h2'

theorem posPl_inj (D : D7) (p : ℕ) (z : Bool × HH D) (a b : ℕ) (ha : a < nP D p) (hb : b < nP D p)
    (h : posPl D p z a = posPl D p z b) : a = b := by
  have key : ∀ a b : ℕ, a ≤ b → b < nP D p → posPl D p z a = posPl D p z b → a = b := by
    intro a b hab hb h
    obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hab
    rw [← posPl_add] at h
    have hd := posPl_fix D p _ c h.symm
    have hc : c = 0 := Nat.eq_zero_of_dvd_of_lt hd (by omega)
    omega
  rcases le_total a b with hab | hab
  · exact key a b hab hb h
  · exact (key b a hab ha h.symm).symm

theorem sum_orbits (D : D7) (j p : ℕ) (T : Finset (Bool × HH D))
    (hT : ∀ z, ∃! r, r ∈ T ∧ ∃ e : ℕ, posPl D p r e = z) :
    (∑ z : Bool × HH D, FOrb D j p z) / (nP D p : ℝ) = ∑ r ∈ T, FOrb D j p r := by
  have hn : (nP D p : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne _)
  have hpos : 0 < nP D p := Nat.pos_of_ne_zero (NeZero.ne _)
  have h1 : ∑ x ∈ T ×ˢ Finset.range (nP D p), FOrb D j p (posPl D p x.1 x.2) =
      ∑ z : Bool × HH D, FOrb D j p z := by
    refine Finset.sum_bij (fun x _ => posPl D p x.1 x.2) (fun _ _ => Finset.mem_univ _) ?_ ?_ (fun _ _ => rfl)
    · rintro ⟨r, a⟩ hx ⟨r', b⟩ hx' h
      rw [Finset.mem_product, Finset.mem_range] at hx hx'
      have hr : r = r' := (hT (posPl D p r a)).unique ⟨hx.1, a, rfl⟩ ⟨hx'.1, b, h.symm⟩
      subst hr
      rw [posPl_inj D p r a b hx.2 hx'.2 h]
    · intro z _
      obtain ⟨r, ⟨hr, e, he⟩, -⟩ := hT z
      exact ⟨(r, e % nP D p), Finset.mem_product.2 ⟨hr, Finset.mem_range.2 (Nat.mod_lt _ hpos)⟩,
        by rw [posPl_mod, he]⟩
  rw [← h1, Finset.sum_product]
  simp only [FOrb_step, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [← Finset.mul_sum, mul_div_cancel_left₀ _ hn]

theorem cls_ramD {D : D7} {p : ℕ} (h : D.host.cls p = PrimeClass.ramD) : p = D.host.d := by
  unfold Host.cls primeClass at h
  split_ifs at h <;> simp_all

section Cases

variable {D : D7} (L : SizeData₂ D) (j : ℕ) {p : ℕ}

theorem FvalP_g (hg : p ∈ L.gTypes) : FvalP L j p = FTypeG D j := if_pos hg

theorem FvalP_d (hg : p ∉ L.gTypes) (hd : D.host.cls p = PrimeClass.ramD) : FvalP L j p = FRamD D j := by
  unfold FvalP
  rw [if_neg hg, if_pos hd]

theorem FvalP_inert (hg : p ∉ L.gTypes) (hc : IsResidueClassZero D p ∨ IsSg D p) (hX : (p : ℝ) ≤ L.sc.X'' D.R.n) :
    FvalP L j p = FInert D j p := by
  have hd : D.host.cls p ≠ PrimeClass.ramD := by
    rcases hc with h | h <;> rw [h] <;> simp
  unfold FvalP
  rw [if_neg hg, if_neg hd, if_pos ⟨hc, hX⟩]

theorem FvalP_split (hg : p ∉ L.gTypes) (hc : D.host.cls p = PrimeClass.splitK ∨ D.host.cls p = PrimeClass.ram2 ∨
    D.host.cls p = PrimeClass.ramQ) : FvalP L j p = 0 := by
  have hd : D.host.cls p ≠ PrimeClass.ramD := by
    rcases hc with h | h | h <;> rw [h] <;> simp
  have hi : ¬ ((IsResidueClassZero D p ∨ IsSg D p) ∧ (p : ℝ) ≤ L.sc.X'' D.R.n) := by
    rintro ⟨h' | h', -⟩ <;> rcases hc with h | h | h <;> exact absurd (h'.symm.trans h) (by decide)
  unfold FvalP
  rw [if_neg hg, if_neg hd, if_neg hi]

theorem FvalP_above (hX : L.sc.X'' D.R.n < (p : ℝ)) (hg : p ∉ L.gTypes) (hd : p ≠ D.host.d) : FvalP L j p = 0 := by
  unfold FvalP
  rw [if_neg hg, if_neg (fun h => hd (cls_ramD h)), if_neg (fun h => absurd h.2 (not_le.2 hX))]

end Cases

theorem addVal_natCast_nonneg {K : Type*} [Field K] (v : AddValuation K (WithTop ℤ)) (n : ℕ) : 0 ≤ v (n : K) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_succ]
    exact le_trans (le_min ih (by rw [v.map_one])) (v.map_add _ _)

theorem resChar_conj (D : D7) (w : D.what₂.places.Pl) :
    D.what₂.places.resChar (D.what₂.places.conj w) = D.what₂.places.resChar w := by
  by_contra hne
  set v := D.what₂.places.val (D.what₂.places.conj w) with hv
  set q := D.what₂.places.resChar (D.what₂.places.conj w) with hq
  set p := D.what₂.places.resChar w with hp
  have hqpr : q.Prime := D.what₂.places.resChar_prime _
  have hppr : p.Prime := D.what₂.places.resChar_prime _
  have hvq : 0 < v (q : D.what₂.LL) := by
    rw [hv, hq, D.what₂.places.val_resChar]
    exact_mod_cast D.what₂.places.ramIdx_pos _
  have hvp : 0 < v (p : D.what₂.LL) := by
    rw [hv, D.conj_val, star_natCast, hp, D.what₂.places.val_resChar]
    exact_mod_cast D.what₂.places.ramIdx_pos _
  obtain ⟨c, -, hc⟩ := Nat.exists_mul_mod_eq_one_of_coprime ((Nat.coprime_primes hppr hqpr).2 (fun h => hne h.symm)) hqpr.one_lt
  have h1 : ((p * c : ℕ) : D.what₂.LL) - ((q * (p * c / q) : ℕ) : D.what₂.LL) = 1 := by
    have := Nat.div_add_mod (p * c) q
    rw [hc] at this
    rw [sub_eq_iff_eq_add, add_comm]
    exact_mod_cast this.symm
  have h2 : 0 < v ((p * c : ℕ) : D.what₂.LL) := by
    rw [Nat.cast_mul, v.map_mul]
    exact add_pos_of_pos_of_nonneg hvp (addVal_natCast_nonneg v c)
  have h3 : 0 < v ((q * (p * c / q) : ℕ) : D.what₂.LL) := by
    rw [Nat.cast_mul, v.map_mul]
    exact add_pos_of_pos_of_nonneg hvq (addVal_natCast_nonneg v _)
  have h4 := v.map_sub ((p * c : ℕ) : D.what₂.LL) ((q * (p * c / q) : ℕ) : D.what₂.LL)
  rw [h1, v.map_one] at h4
  exact absurd (lt_of_lt_of_le (lt_min h2 h3) h4) (lt_irrefl _)

theorem Fval_conj {D : D7} (L : SizeData₂ D) (j : ℕ) (w : D.what₂.places.Pl) :
    Fval L j (D.what₂.places.conj w) = Fval L j w := by
  unfold Fval
  rw [resChar_conj]

def SizeData₂.withFval {D : D7} (L : SizeData₂ D) (hs : ∀ j w, w ∉ L.supp → Fval L j w = 0)
    (hu : ∀ w, D.what₂.muAt w = D.what₂.mu0 → ∀ j, 1 ≤ j → j ≤ D.R.m → Fval L j w = 0) : SizeData₂ D :=
  { L with
    F := fun j w => Fval L j w
    F_supp := hs
    untwisted := fun w h j h1 h2 => ⟨(L.untwisted w h j h1 h2).1, hu w h j h1 h2⟩
    F_conj := fun j w => Fval_conj L j w
    F_above := fun j _ h1 h2 h3 => FvalP_above L j h1 h2 h3 }

theorem SizeData₂.withFval_FDef {D : D7} (L : SizeData₂ D) (hs : ∀ j w, w ∉ L.supp → Fval L j w = 0)
    (hu : ∀ w, D.what₂.muAt w = D.what₂.mu0 → ∀ j, 1 ≤ j → j ≤ D.R.m → Fval L j w = 0) :
    (L.withFval hs hu).FDef := fun _ _ _ => rfl

def SizeData₂.FockDegSize {D : D7} (L : SizeData₂ D) (C : ℝ) : Prop :=
  ∀ j ∈ SizeData₂.lifts D, |(fockDeg D j : ℝ) - ∑ τ : D.what₂.Tau, ((D.R.k : ℝ) - 1) * wj D j τ| ≤
    C * (D.R.f : ℝ) * ((D.R.k : ℝ) * L.Sc + (D.R.m : ℝ) * L.etaSz)

def SizeData₂.FRamDSize {D : D7} (L : SizeData₂ D) : Prop :=
  ∀ j ∈ SizeData₂.lifts D, |FRamD D j| ≤ (D.R.f : ℝ) * D.R.k * L.sc.b'

def FInertGe (D : D7) : Prop :=
  ∀ j ∈ SizeData₂.lifts D, ∀ p : ℕ, p.Prime → (IsResidueClassZero D p ∨ IsSg D p) → (∀ τ : D.what₂.Tau, 0 ≤ wj D j τ) →
    ∑ τ : D.what₂.Tau, ((D.R.k : ℝ) - 1) * wj D j τ / ((p : ℝ) ^ 2 - 1) ≤ FInert D j p

end Formalism.BasicNotions

end
