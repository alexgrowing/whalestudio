import Formalism.SharpRestriction.GrowthBounds.RootWeights.PadicGeMulNat

noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

theorem mah_zero (f : ℕ → ℚ) : mah f 0 = f 0 := rfl

theorem mah_succ (f : ℕ → ℚ) (j : ℕ) : mah f (j + 1) = mah (fwdDiff 1 f) j := by
  simp only [mah, Function.iterate_succ_apply]

theorem mah_add (f g : ℕ → ℚ) (j : ℕ) : mah (f + g) j = mah f j + mah g j := by
  simp only [mah, fwdDiff_iter_add, Pi.add_apply]

theorem mah_zero_fn (j : ℕ) : mah (fun _ => (0 : ℚ)) j = 0 := by
  induction j with
  | zero => rfl
  | succ j ih => rw [mah_succ, fwdDiff_const]; exact ih

theorem mah_const (c : ℚ) (j : ℕ) : mah (fun _ => c) j = if j = 0 then c else 0 := by
  cases j with
  | zero => rfl
  | succ j => rw [mah_succ, fwdDiff_const, mah_zero_fn]; simp

theorem mah_neg (f : ℕ → ℚ) (j : ℕ) : mah (-f) j = - mah f j := by
  have h := mah_add f (-f) j
  rw [add_neg_cancel] at h
  have h0 : mah (0 : ℕ → ℚ) j = 0 := mah_zero_fn j
  rw [h0] at h
  linarith

theorem mah_smul (a : ℚ) (f : ℕ → ℚ) (j : ℕ) : mah (fun n => a * f n) j = a * mah f j := by
  induction j generalizing f with
  | zero => rfl
  | succ j ih =>
    rw [mah_succ, mah_succ, ← ih]
    congr 1
    ext n
    simp only [fwdDiff]
    ring

theorem mah_sum {ι : Type*} (s : Finset ι) (F : ι → ℕ → ℚ) (j : ℕ) :
    mah (fun n => ∑ l ∈ s, F l n) j = ∑ l ∈ s, mah (F l) j := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using mah_zero_fn j
  | insert a s ha ih =>
    have : (fun n => ∑ l ∈ insert a s, F l n) = F a + fun n => ∑ l ∈ s, F l n := by
      ext n; simp [Finset.sum_insert ha]
    rw [this, mah_add, ih, Finset.sum_insert ha]

theorem mah_choose (l j : ℕ) : mah (fun n => (n.choose l : ℚ)) j = if j = l then 1 else 0 := by
  induction j generalizing l with
  | zero =>
    rw [mah_zero]
    cases l with
    | zero => simp
    | succ l => simp
  | succ j ih =>
    rw [mah_succ]
    cases l with
    | zero =>
      have : fwdDiff 1 (fun n : ℕ => (n.choose 0 : ℚ)) = fun _ => 0 := by
        ext n; simp [fwdDiff]
      rw [this, mah_zero_fn]; simp
    | succ l =>
      have : fwdDiff 1 (fun n : ℕ => (n.choose (l + 1) : ℚ)) = fun n => (n.choose l : ℚ) := by
        ext n; simp [fwdDiff, Nat.choose_succ_succ']
      rw [this, ih]; simp

theorem mah_leibniz (f g : ℕ → ℚ) :
    fwdDiff 1 (f * g) = fwdDiff 1 f * g + f * fwdDiff 1 g + fwdDiff 1 f * fwdDiff 1 g := by
  ext n
  simp only [fwdDiff, Pi.mul_apply, Pi.add_apply]
  ring

theorem mah_newton (f : ℕ → ℚ) (m : ℕ) : f m = ∑ j ∈ range (m + 1), mah f j * (m.choose j : ℚ) := by
  have h := shift_eq_sum_fwdDiff_iter (1 : ℕ) f m 0
  simp only [zero_add, smul_eq_mul, mul_one, nsmul_eq_mul] at h
  rw [h]
  exact sum_congr rfl fun j _ => by rw [mah, mul_comm]

theorem mah_decLe_mono {p : ℕ} {θ s : ℝ} {K K' : ℕ} {f : ℕ → ℚ} (h : DecLe p θ s K f) (hK : K' ≤ K) :
    DecLe p θ s K' f := fun j hj => h j (hj.trans hK)

theorem mah_decLe_diff {p : ℕ} {θ s : ℝ} {K : ℕ} {f : ℕ → ℚ} (h : DecLe p θ s (K + 1) f) :
    DecLe p θ (s + θ) K (fwdDiff 1 f) := by
  intro j hj
  rw [← mah_succ]
  refine padicGe_mono (h (j + 1) (by omega)) ?_
  push_cast
  linarith

theorem mah_prodLe {p : ℕ} [Fact p.Prime] {θ : ℝ} (hθ : 0 ≤ θ) (N : ℕ) :
    ∀ (s s' : ℝ) (f g : ℕ → ℚ), DecLe p θ s N f → DecLe p θ s' N g →
      PadicGe p (mah (f * g) N) (θ * N + (s + s')) := by
  induction N with
  | zero =>
    intro s s' f g hf hg
    have h1 := hf 0 le_rfl
    have h2 := hg 0 le_rfl
    have h3 := padicGe_mul h1 h2
    refine padicGe_mono h3 ?_
    simp
  | succ N ih =>
    intro s s' f g hf hg
    rw [mah_succ, mah_leibniz, mah_add, mah_add]
    have hf' := mah_decLe_diff hf
    have hg' := mah_decLe_diff hg
    have hf0 := mah_decLe_mono hf (Nat.le_succ N)
    have hg0 := mah_decLe_mono hg (Nat.le_succ N)
    refine padicGe_add (padicGe_add ?_ ?_) ?_
    · exact padicGe_mono (ih _ _ _ _ hf' hg0) (by push_cast; linarith)
    · exact padicGe_mono (ih _ _ _ _ hf0 hg') (by push_cast; linarith)
    · exact padicGe_mono (ih _ _ _ _ hf' hg') (by push_cast; linarith)

theorem mah_dec_mul {p : ℕ} [Fact p.Prime] {θ s s' : ℝ} {f g : ℕ → ℚ} (hθ : 0 ≤ θ)
    (hf : Dec p θ s f) (hg : Dec p θ s' g) : Dec p θ (s + s') (f * g) :=
  fun N => mah_prodLe hθ N s s' f g (fun j _ => hf j) (fun j _ => hg j)

theorem hMul_proved {p : ℕ} (hp : p.Prime) : HMul p := by
  intro θ s s' f g hθ hf hg
  have := Fact.mk hp
  exact mah_dec_mul hθ hf hg

theorem mah_dec_weaken {p : ℕ} {θ θ' s s' : ℝ} {f : ℕ → ℚ} (h : Dec p θ s f) (h1 : θ' ≤ θ) (h2 : s' ≤ s) :
    Dec p θ' s' f := by
  intro j
  refine padicGe_mono (h j) ?_
  have : θ' * (j : ℝ) ≤ θ * j := mul_le_mul_of_nonneg_right h1 (by positivity)
  linarith

theorem mah_running {p : ℕ} [Fact p.Prime] {θ : ℝ} (hθ : 0 ≤ θ) (g u : ℕ → ℚ) (h0 : g 0 = 1)
    (hs : ∀ n, g (n + 1) = g n * (1 + u n)) (hu : Dec p θ θ u) : Dec p θ 0 g := by
  have hD : fwdDiff 1 g = g * u := by
    ext n
    simp only [fwdDiff, Pi.mul_apply, hs]
    ring
  have key : ∀ N, DecLe p θ 0 N g := by
    intro N
    induction N with
    | zero =>
      intro j hj
      obtain rfl : j = 0 := by omega
      rw [mah_zero, h0]
      right
      simp
    | succ N ih =>
      intro j hj
      rcases Nat.lt_or_ge j (N + 1) with h | h
      · exact ih j (by omega)
      · obtain rfl : j = N + 1 := by omega
        rw [mah_succ, hD]
        exact padicGe_mono (mah_prodLe hθ N 0 θ g u ih (fun j _ => hu j)) (by push_cast; linarith)
  exact fun j => key j j le_rfl

theorem mah_val {p : ℕ} [Fact p.Prime] {θ s : ℝ} {f : ℕ → ℚ} (hθ : 0 ≤ θ) (h : Dec p θ s f) (n : ℕ) :
    PadicGe p (f n) s := by
  rw [mah_newton f n]
  refine padicGe_sum _ _ fun j _ => padicGe_mul_nat (padicGe_mono (h j) ?_) _
  have : 0 ≤ θ * (j : ℝ) := by positivity
  linarith

theorem mah_of_vals {p : ℕ} [Fact p.Prime] {r : ℝ} (N : ℕ) :
    ∀ f : ℕ → ℚ, (∀ n, PadicGe p (f n) r) → PadicGe p (mah f N) r := by
  induction N with
  | zero => intro f h; exact h 0
  | succ N ih =>
    intro f h
    rw [mah_succ]
    refine ih _ fun n => ?_
    simp only [fwdDiff, sub_eq_add_neg]
    exact padicGe_add (h _) (padicGe_neg (h _))

theorem mah_unit {p : ℕ} [Fact p.Prime] {x : ℚ} {θ : ℝ} (hθ : 0 < θ) (hx : PadicGe p x θ) :
    1 + x ≠ 0 ∧ padicValRat p (1 + x) = 0 := by
  by_cases h0 : x = 0
  · simp [h0]
  rcases hx with hx | hx
  · exact absurd hx h0
  have hpos : (0 : ℤ) < padicValRat p x := by
    have : (0 : ℝ) < (padicValRat p x : ℝ) := lt_of_lt_of_le hθ hx
    exact_mod_cast this
  have hne : 1 + x ≠ 0 := by
    intro h
    have hx1 : x = -1 := by linarith
    rw [hx1, padicValRat.neg, padicValRat.one] at hpos
    exact lt_irrefl _ hpos
  refine ⟨hne, ?_⟩
  have := padicValRat.add_eq_of_lt (p := p) hne one_ne_zero h0 (by rw [padicValRat.one]; exact hpos)
  rw [this, padicValRat.one]

theorem mah_padicGe_pow {p : ℕ} [Fact p.Prime] {x : ℚ} {r : ℝ} (hx : PadicGe p x r) (m : ℕ) :
    PadicGe p (x ^ m) (m * r) := by
  induction m with
  | zero => right; simp
  | succ m ih =>
    rw [pow_succ]
    exact padicGe_mono (padicGe_mul ih hx) (by push_cast; linarith)

theorem mah_dec_const {p : ℕ} {θ s : ℝ} {c : ℚ} (hc : PadicGe p c s) : Dec p θ s (fun _ => c) := by
  intro j
  rw [mah_const]
  split_ifs with h
  · subst h; simpa using hc
  · exact Or.inl rfl

theorem mah_dec_add {p : ℕ} [Fact p.Prime] {θ s : ℝ} {f g : ℕ → ℚ} (hf : Dec p θ s f) (hg : Dec p θ s g) :
    Dec p θ s (f + g) := fun j => by rw [mah_add]; exact padicGe_add (hf j) (hg j)

theorem mah_dec_neg {p : ℕ} {θ s : ℝ} {f : ℕ → ℚ} (hf : Dec p θ s f) : Dec p θ s (-f) :=
  fun j => by rw [mah_neg]; exact padicGe_neg (hf j)

theorem mah_dec_pow {p : ℕ} [Fact p.Prime] {θ : ℝ} (hθ : 0 ≤ θ) {w : ℕ → ℚ} (hw : Dec p θ θ w) (i : ℕ) :
    Dec p θ (i * θ) (w ^ i) := by
  induction i with
  | zero =>
    rw [pow_zero]
    refine mah_dec_const (c := 1) ?_
    right; simp
  | succ i ih =>
    rw [pow_succ]
    exact mah_dec_weaken (mah_dec_mul hθ ih hw) le_rfl (by push_cast; linarith)

theorem mah_dec_sum {p : ℕ} [Fact p.Prime] {θ s : ℝ} {ι : Type*} (t : Finset ι) (F : ι → ℕ → ℚ)
    (h : ∀ i ∈ t, Dec p θ s (F i)) : Dec p θ s (fun n => ∑ i ∈ t, F i n) := by
  intro j
  rw [mah_sum]
  exact padicGe_sum _ _ fun i hi => h i hi j

theorem mah_geom (x : ℚ) (hx : 1 + x ≠ 0) (N : ℕ) :
    (1 + x)⁻¹ - 1 = ∑ i ∈ range (N + 1), (-x) ^ (i + 1) + (-x) ^ (N + 2) * (1 + x)⁻¹ := by
  have g := geom_sum_mul (-x) (N + 2)
  rw [sum_range_succ', pow_zero] at g
  have hI : (1 + x)⁻¹ * (1 + x) = 1 := inv_mul_cancel₀ hx
  linear_combination (1 + x)⁻¹ * g + (∑ i ∈ range (N + 1), (-x) ^ (i + 1) + 1) * hI

theorem mah_inv {p : ℕ} [Fact p.Prime] {θ : ℝ} (hθ : 0 < θ) {u : ℕ → ℚ} (hu : Dec p θ θ u) :
    Dec p θ θ (fun n => (1 + u n)⁻¹ - 1) := by
  intro N
  have hval : ∀ n, PadicGe p (u n) θ := mah_val hθ.le hu
  have hdec : (fun n => (1 + u n)⁻¹ - 1) =
      (fun n => ∑ i ∈ range (N + 1), ((-u) ^ (i + 1)) n) + fun n => (-u n) ^ (N + 2) * (1 + u n)⁻¹ := by
    ext n
    simp only [Pi.add_apply, Pi.pow_apply, Pi.neg_apply]
    exact mah_geom (u n) (mah_unit hθ (hval n)).1 N
  rw [hdec, mah_add]
  refine padicGe_add ?_ ?_
  · refine mah_dec_sum (range (N + 1)) (fun i => (-u) ^ (i + 1)) (fun i _ => ?_) N
    refine mah_dec_weaken (mah_dec_pow hθ.le (mah_dec_neg hu) (i + 1)) le_rfl ?_
    push_cast
    have : 0 ≤ (i : ℝ) * θ := by positivity
    linarith
  · refine mah_of_vals N _ fun n => ?_
    have h1 := mah_padicGe_pow (padicGe_neg (hval n)) (N + 2)
    have h2 : PadicGe p ((1 + u n)⁻¹) 0 := by
      right
      rw [padicValRat.inv, (mah_unit hθ (hval n)).2]
      simp
    refine padicGe_mono (padicGe_mul h1 h2) ?_
    push_cast
    linarith

theorem mah_padicGe_of_dvd {p : ℕ} [Fact p.Prime] {a : ℤ} {l : ℕ} (h : (p : ℤ) ^ l ∣ a) :
    PadicGe p (a : ℚ) l := by
  obtain ⟨b, rfl⟩ := h
  have h1 : PadicGe p ((p : ℚ) ^ l) l := by
    right
    rw [padicValRat.pow, padicValRat.self (Fact.out : p.Prime).one_lt]
    simp
  have := padicGe_mul h1 (padicGe_int (p := p) b)
  push_cast
  simpa using this

theorem mah_dU {p : ℕ} [Fact p.Prime] (h : HdU p) (t rho : ℕ) (hr : rho < p ^ (t + 1)) :
    Dec p (1 / 2) (1 / 2) (fun n => dUnit (p ^ (t + 1)) n rho - 1) := by
  obtain ⟨a, ha, hdiv⟩ := h t rho hr
  intro j
  cases j with
  | zero =>
    left
    rw [mah_zero]
    simp [dUnit]
  | succ j =>
    have e1 : fwdDiff 1 (fun n => dUnit (p ^ (t + 1)) n rho - 1) =
        fwdDiff 1 (fun n => ∑ l ∈ range (rho + 1), (a l : ℚ) * (n.choose l : ℚ)) := by
      ext n
      simp only [fwdDiff, ha]
      ring
    rw [mah_succ, e1, ← mah_succ, mah_sum]
    refine padicGe_sum _ _ fun l _ => ?_
    rw [mah_smul, mah_choose]
    split_ifs with hl
    · subst hl
      rw [mul_one]
      refine padicGe_mono (mah_padicGe_of_dvd (hdiv (j + 1))) ?_
      push_cast
      have : (0 : ℝ) ≤ j := by positivity
      linarith
    · left; simp

theorem mah_one_add {p : ℕ} [Fact p.Prime] {θ s : ℝ} {u : ℕ → ℚ} (hs : 0 ≤ s) (hu : Dec p θ s u) :
    Dec p θ 0 (fun n => 1 + u n) := by
  have : (fun n => 1 + u n) = (fun _ => (1 : ℚ)) + u := rfl
  rw [this]
  refine mah_dec_add (mah_dec_const ?_) (mah_dec_weaken hu le_rfl hs)
  right; simp

theorem mah_cUnit_zero (P : ℕ) : cUnit P 0 = 1 := by simp [cUnit]

theorem mah_cUnit_succ (P n : ℕ) (hP : 1 ≤ P) :
    cUnit P (n + 1) = cUnit P n * (1 + (dUnit P n (P - 1) - 1)) := by
  have h1 : cUnit P (n + 1) = _ := Formalism.GrowthSums.blockFactorialQuotientProd P (n + 1) hP
  have h2 : cUnit P n = _ := Formalism.GrowthSums.blockFactorialQuotientProd P n hP
  rw [h1, h2, prod_range_succ]
  congr 1
  have : Icc 1 (P - 1) = Ico 1 P := by
    ext y; simp only [mem_Icc, mem_Ico]; omega
  rw [dUnit, this]
  ring

theorem mah_unitFn_ff (p t rho : ℕ) :
    unitFn p ⟨t, rho, false, false⟩ = fun m => dUnit (p ^ (t + 1)) m rho := by
  funext m; simp [unitFn]

theorem mah_unitFn_ft (p t rho : ℕ) :
    unitFn p ⟨t, rho, false, true⟩ = fun m => (dUnit (p ^ (t + 1)) m rho)⁻¹ := by
  funext m; simp [unitFn]

theorem mah_unitFn_tf (p t rho : ℕ) :
    unitFn p ⟨t, rho, true, false⟩ = fun m => cUnit (p ^ (t + 1)) m := by
  funext m; simp [unitFn]

theorem mah_unitFn_tt (p t rho : ℕ) :
    unitFn p ⟨t, rho, true, true⟩ = fun m => (cUnit (p ^ (t + 1)) m)⁻¹ := by
  funext m; simp [unitFn]

theorem mah_unitFn_half {p : ℕ} (hp : p.Prime) (h : HdU p) (u : UnitFn) (hu : u.rho < p ^ (u.t + 1)) :
    Dec p (1 / 2) 0 (unitFn p u) := by
  have := Fact.mk hp
  obtain ⟨t, rho, isC, inv⟩ := u
  simp only at hu
  have hP : 1 ≤ p ^ (t + 1) := Nat.one_le_pow _ _ hp.pos
  have hd := mah_dU h t rho hu
  have hd' := mah_dU h t (p ^ (t + 1) - 1) (by omega)
  have half : (0 : ℝ) < 1 / 2 := by norm_num
  cases isC <;> cases inv
  · rw [mah_unitFn_ff]
    have e : (fun m => dUnit (p ^ (t + 1)) m rho) = fun n => 1 + (dUnit (p ^ (t + 1)) n rho - 1) := by
      funext n; ring
    rw [e]
    exact mah_one_add half.le hd
  · rw [mah_unitFn_ft]
    have e : (fun m => (dUnit (p ^ (t + 1)) m rho)⁻¹) =
        fun n => 1 + ((1 + (dUnit (p ^ (t + 1)) n rho - 1))⁻¹ - 1) := by
      funext n; ring
    rw [e]
    exact mah_one_add half.le (mah_inv half hd)
  · rw [mah_unitFn_tf]
    exact mah_running half.le (fun m => cUnit (p ^ (t + 1)) m)
      (fun n => dUnit (p ^ (t + 1)) n (p ^ (t + 1) - 1) - 1) (mah_cUnit_zero _)
      (fun n => mah_cUnit_succ _ n hP) hd'
  · rw [mah_unitFn_tt]
    refine mah_running half.le (fun m => (cUnit (p ^ (t + 1)) m)⁻¹)
      (fun n => (1 + (dUnit (p ^ (t + 1)) n (p ^ (t + 1) - 1) - 1))⁻¹ - 1) ?_ (fun n => ?_)
      (mah_inv half hd')
    · simp [mah_cUnit_zero]
    · rw [mah_cUnit_succ _ n hP, mul_inv]
      congr 1
      ring

theorem hDec_of {p : ℕ} (hp : p.Prime) (h : HdU p) : HDec p := fun u hu =>
  mah_dec_weaken (mah_unitFn_half hp h u hu) (by norm_num) le_rfl

theorem hUnit_of {p : ℕ} (hp : p.Prime) (h : HdU p) : HUnit p := by
  have := Fact.mk hp
  intro u hu m
  obtain ⟨t, rho, isC, inv⟩ := u
  simp only at hu
  have hP : 1 ≤ p ^ (t + 1) := Nat.one_le_pow _ _ hp.pos
  have half : (0 : ℝ) < 1 / 2 := by norm_num
  have hdv : ∀ rho', rho' < p ^ (t + 1) → ∀ n, dUnit (p ^ (t + 1)) n rho' ≠ 0 ∧
      padicValRat p (dUnit (p ^ (t + 1)) n rho') = 0 := by
    intro rho' hr n
    have h1 := mah_unit half (mah_val half.le (mah_dU h t rho' hr) n)
    simpa only [add_sub_cancel] using h1
  have hcv : ∀ n, cUnit (p ^ (t + 1)) n ≠ 0 ∧ padicValRat p (cUnit (p ^ (t + 1)) n) = 0 := by
    intro n
    induction n with
    | zero => rw [mah_cUnit_zero]; simp
    | succ n ih =>
      rw [mah_cUnit_succ _ _ hP, add_sub_cancel]
      have hd := hdv (p ^ (t + 1) - 1) (by omega) n
      exact ⟨mul_ne_zero ih.1 hd.1, by rw [padicValRat.mul ih.1 hd.1, ih.2, hd.2]; rfl⟩
  cases isC <;> cases inv
  · rw [mah_unitFn_ff]; exact hdv rho hu m
  · rw [mah_unitFn_ft]
    exact ⟨inv_ne_zero (hdv rho hu m).1, by simp only [padicValRat.inv, (hdv rho hu m).2]; rfl⟩
  · rw [mah_unitFn_tf]; exact hcv m
  · rw [mah_unitFn_tt]
    exact ⟨inv_ne_zero (hcv m).1, by simp only [padicValRat.inv, (hcv m).2]; rfl⟩

end Formalism.MainNotions.G.GLWeightTheory
