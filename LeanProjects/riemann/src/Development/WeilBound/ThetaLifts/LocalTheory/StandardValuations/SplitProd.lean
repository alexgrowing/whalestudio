import Development.WeilBound.ThetaLifts.LocalTheory.StandardValuations.IntIndPow

set_option linter.unusedSectionVars false

noncomputable section

open Matrix MeasureTheory ValuativeRel Topology GlobalTheory.SplitFlip GlobalTheory.SplitWeil

namespace PositivityTheory.ThKG.Std

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n d n₁ d₁ : ℕ} {ν : kˣ →* ℂˣ} {ϖ : kˣ} {c : ℕ}

def mid {b : ℕ} (i : Fin b) : Fin (b + 2) := i.castSucc.succ

theorem detB {b : ℕ} (N : Matrix (Fin (b + 2)) (Fin (b + 2)) k) (h0 : ∀ j, j ≠ Fin.last _ → N 0 j = 0)
    (h1 : ∀ i, N (mid i) 0 = 0) : N.det = -N 0 (Fin.last _) * N (Fin.last _) 0 * (N.submatrix mid mid).det := by
  rw [det_succ_row_zero, Finset.sum_eq_single (Fin.last _) (fun j _ hj => by rw [h0 j hj]; simp) (by simp),
    Fin.succAbove_last, det_succ_column_zero, Finset.sum_eq_single (Fin.last _) (fun i _ hi => by
      obtain ⟨i, rfl⟩ := Fin.exists_castSucc_eq.2 hi
      have := h1 i
      simp only [mid] at this
      simp [this]) (by simp), Fin.succAbove_last]
  have : (N.submatrix Fin.succ Fin.castSucc).submatrix Fin.castSucc Fin.succ = N.submatrix mid mid := by
    ext i j; rfl
  rw [this]
  simp only [Fin.val_last, submatrix_apply, Fin.succ_last, Fin.castSucc_zero, pow_succ]
  have : ((-1 : k) ^ b) * (-1) ^ b = 1 := by rw [← mul_pow]; simp
  linear_combination (-N 0 (Fin.last (b + 1)) * N (Fin.last (b + 1)) 0 * (N.submatrix mid mid).det) * this

theorem detA {b : ℕ} (N : Matrix (Fin (b + 2)) (Fin (b + 2)) k) (h0 : ∀ i, i ≠ 0 → N i (Fin.last _) = 0)
    (h1 : ∀ j, N (Fin.last _) (mid j) = 0) : N.det = -N 0 (Fin.last _) * N (Fin.last _) 0 * (N.submatrix mid mid).det := by
  have hm : ∀ i : Fin b, (mid i).rev = mid i.rev := fun i => Fin.ext (by simp [mid]; omega)
  have := detB ((N.submatrix Fin.revPerm Fin.revPerm)ᵀ) (fun j hj => h0 _ fun h => hj (by simpa using congrArg Fin.rev h))
    (fun i => by simpa [hm] using h1 i.rev)
  rw [det_transpose, det_submatrix_equiv_self] at this
  rw [this, ← det_submatrix_equiv_self Fin.revPerm (N.submatrix mid mid), ← det_transpose ((N.submatrix mid mid).submatrix _ _)]
  congr 2
  · simp
  · simp
  · ext i j; simp [hm]

open Classical in

def rad (ϖ : kˣ) (c : ℕ) (e : Fin n → Fin d) (j : Fin d) : k := if j ∈ Set.range e then 1 else (ϖ : k) ^ c

def std (ν : kˣ →* ℂˣ) (ϖ : kˣ) (c : ℕ) (e : Fin n → Fin d) (Y : Matrix (Fin n) (Fin d) k) : ℂ :=
  (∏ p : Fin n × Fin d, ind (rad ϖ c e p.2) (Y p.1 p.2)) * dl ν (Y.submatrix id e).det

def tm (Z : Fin n × Fin d → k) : Matrix (Fin n) (Fin d) k := Matrix.of fun i j => Z (i, j)

def emb (R : Type) [Zero R] [One R] (j : Fin n₁ → Fin n) : Matrix (Fin n) (Fin n₁) R := Matrix.of fun i i' => if i = j i' then 1 else 0

def ext (jr : Fin n₁ → Fin n) (jc : Fin d₁ → Fin d) (y : Matrix (Fin n₁) (Fin d₁) k) : Matrix (Fin n) (Fin d) k :=
  emb k jr * y * (emb k jc)ᵀ

variable {jr : Fin n₁ → Fin n} {jc : Fin d₁ → Fin d}

theorem ext_mid (hr : Function.Injective jr) (hc : Function.Injective jc) (y : Matrix (Fin n₁) (Fin d₁) k) (i j) :
    ext jr jc y (jr i) (jc j) = y i j := by
  simp [ext, emb, Matrix.mul_apply, hr.eq_iff, hc.eq_iff]

theorem ext_off (y : Matrix (Fin n₁) (Fin d₁) k) {i j} (h : (∀ i', i ≠ jr i') ∨ ∀ j', j ≠ jc j') : ext jr jc y i j = 0 := by
  rcases h with h | h <;> simp [ext, emb, Matrix.mul_apply, h]

theorem rad_ne (e : Fin n → Fin d) (j) : rad ϖ c e j ≠ 0 := by
  unfold rad; split_ifs <;> simp

theorem rad_le (hϖ : IsUnif ϖ) (e : Fin n → Fin d) (j) : valuation k (rad ϖ c e j) ≤ 1 := by
  unfold rad; split_ifs
  · simp
  · exact val_pow_le hϖ c

theorem rad_e (e : Fin n → Fin d) (i) : rad ϖ c e (e i) = 1 := if_pos ⟨i, rfl⟩

theorem ind_zero (c : k) : ind c 0 = 1 := by simp [ind]

theorem val_det {N : Matrix (Fin n) (Fin n) k} (h : ∀ i j, valuation k (N i j) ≤ 1) : valuation k N.det ≤ 1 := by
  have : N = (Matrix.of fun i j => (⟨N i j, h i j⟩ : 𝒪[k])).map (algebraMap 𝒪[k] k) := rfl
  rw [this, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  exact (Matrix.det _ : 𝒪[k]).2

theorem std_mem (hϖ : IsUnif ϖ) (hc : 1 ≤ c) (hν : CondLE ϖ c ν) (e : Fin n → Fin d) :
    std ν ϖ c e ∈ GlobalTheory.WeilM.SB (Matrix (Fin n) (Fin d) k) := by
  refine ⟨(lc_prod _ fun p _ => (lc_ind (rad_ne e p.2)).comp_continuous (continuous_id.matrix_elem _ _)).mul
    ((lc_dl hϖ hc hν).comp_continuous (continuous_id.matrix_submatrix _ _).matrix_det), ?_⟩
  refine HasCompactSupport.intro (isCompact_univ_pi fun _ => isCompact_univ_pi fun j =>
    IsNonarchimedeanLocalField.isCompact_closedBall k (valuation k (rad ϖ c e j))) fun x hx => ?_
  by_contra h
  exact hx fun i _ j _ => ind_ne (Finset.prod_ne_zero_iff.1 (left_ne_zero_of_mul h) (i, j) (Finset.mem_univ _))

theorem prod_mid (hr : Function.Injective jr) (hc : Function.Injective jc) {e : Fin n → Fin d} {e₁ : Fin n₁ → Fin d₁}
    (he : ∀ j, jc j ∈ Set.range e ↔ j ∈ Set.range e₁) {P : Finset (Fin n × Fin d)} (hP : ∀ i j, (jr i, jc j) ∉ P)
    (y : Matrix (Fin n₁) (Fin d₁) k) :
    ∏ p : Fin n × Fin d, (if p ∈ P then 1 else ind (rad ϖ c e p.2) (ext jr jc y p.1 p.2)) =
      ∏ p : Fin n₁ × Fin d₁, ind (rad ϖ c e₁ p.2) (y p.1 p.2) := by
  refine (Fintype.prod_of_injective (Prod.map jr jc) (hr.prodMap hc) _ _ (fun p hp => ?_) fun p => ?_).symm
  · rw [ext_off, ind_zero, ite_self]
    by_contra h
    push Not at h
    obtain ⟨⟨i, hi⟩, j, hj⟩ := h
    exact hp ⟨(i, j), Prod.ext hi.symm hj.symm⟩
  · simp only [Prod.map, if_neg (hP _ _), ext_mid hr hc, rad, he]

variable [SecondCountableTopology k] [MeasurableSpace k] [BorelSpace k] {m : Measure k} {ψ : AddChar k ℂ}

theorem prod_vol (hm : IsVol m) (hϖ : IsUnif ϖ) {e : Fin n → Fin d} {P : Finset (Fin n × Fin d)} {r : ℕ}
    (g : Fin r → Fin n × Fin d) (hg : Function.Injective g) (h : ∀ p, p ∈ Set.range g ↔ p ∈ P ∧ p.2 ∉ Set.range e) :
    ∏ p : Fin n × Fin d, ∫ x, (if p ∈ P then ind (rad ϖ c e p.2) x else ind 1 x) ∂m = (((resCard k : ℂ) ^ c)⁻¹) ^ r := by
  rw [← Fin.prod_const]
  refine (Fintype.prod_of_injective g hg _ _ (fun p hp => ?_) fun p => ?_).symm
  · by_cases h1 : p ∈ P
    · have h2 : p.2 ∈ Set.range e := by by_contra h2; exact hp ((h p).2 ⟨h1, h2⟩)
      simp only [if_pos h1, rad, if_pos h2, int_ind_one hm]
    · simp only [if_neg h1, int_ind_one hm]
  · obtain ⟨h1, h2⟩ := (h _).1 ⟨p, rfl⟩
    simp only [if_pos h1, rad, if_neg h2, int_ind_pow hm hϖ]

theorem split_prod {e : Fin n → Fin d} (P : Finset (Fin n × Fin d)) (Y : Matrix (Fin n) (Fin d) k) (hY : ∀ p ∈ P, Y p.1 p.2 = 0)
    (Z : Fin n × Fin d → k) : (∏ p : Fin n × Fin d, ind (rad ϖ c e p.2) ((tm (cut P Z) + Y) p.1 p.2)) * wt P Z =
      (∏ p : Fin n × Fin d, if p ∈ P then 1 else ind (rad ϖ c e p.2) (Y p.1 p.2)) *
        ∏ p : Fin n × Fin d, (if p ∈ P then ind (rad ϖ c e p.2) (Z p) else ind 1 (Z p)) := by
  rw [wt, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun p _ => ?_
  by_cases hp : p ∈ P
  · simp [tm, cut, hp, hY p hp]
  · simp [tm, cut, hp]

theorem int_ev (hm : IsVol m) (hϖ : IsUnif ϖ) {jc : Fin d₁ → Fin d} (hc : Function.Injective jc) {e : Fin n → Fin d}
    {e₁ : Fin n → Fin d₁} (he : ∀ i, jc (e₁ i) = e i) (j₀ : Fin d) (h0 : j₀ ∉ Set.range e) (h1 : ∀ j, j₀ ≠ jc j)
    (y : Matrix (Fin n) (Fin d₁) k) :
    ∫ Z, std ν ϖ c e (tm (cut (Finset.univ.filter fun p => p.2 = j₀) Z) + ext id jc y) * wt (Finset.univ.filter fun p => p.2 = j₀) Z
      ∂(Measure.pi fun _ => m) = (((resCard k : ℂ) ^ c)⁻¹) ^ n * std ν ϖ c e₁ y := by
  haveI := hm.haar
  set P : Finset (Fin n × Fin d) := Finset.univ.filter fun p => p.2 = j₀ with hP
  have hY : ∀ p ∈ P, ext id jc y p.1 p.2 = 0 := fun p hp => ext_off y (Or.inr fun j => by
    rw [(Finset.mem_filter.1 hp).2]; exact h1 j)
  have hd : ∀ Z, (tm (cut P Z) + ext id jc y).submatrix id e = y.submatrix id e₁ := fun Z => by
    ext i j
    have : e j ≠ j₀ := fun h => h0 ⟨j, h⟩
    have h2 := ext_mid Function.injective_id hc y i (e₁ j)
    rw [he] at h2
    simpa [tm, cut, hP, this] using h2
  simp only [std, hd, mul_right_comm _ (dl ν _), split_prod P _ hY]
  rw [integral_mul_const, integral_const_mul, integral_fintype_prod_eq_prod
    (fun (p : Fin n × Fin d) x => if p ∈ P then ind (rad ϖ c e p.2) x else ind 1 x),
    prod_vol hm hϖ (fun i => (i, j₀)) (fun _ _ h => (Prod.ext_iff.1 h).1) (fun p => ?_),
    prod_mid Function.injective_id hc (e₁ := e₁) (fun j => ?_) (fun i j h => h1 j (Finset.mem_filter.1 h).2.symm)]
  · ring
  · exact ⟨fun ⟨i, hi⟩ => ⟨i, hc ((he i).trans hi)⟩, fun ⟨i, hi⟩ => ⟨i, by rw [← he, hi]⟩⟩
  · simp only [hP, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun ⟨i, hi⟩ => hi ▸ ⟨rfl, h0⟩, fun h => ⟨p.1, Prod.ext rfl h.1.symm⟩⟩

theorem int_cone (hm : IsVol m) (hϖ : IsUnif ϖ) {b : ℕ} {jc : Fin d₁ → Fin d} (hc : Function.Injective jc) {e : Fin (b + 2) → Fin d}
    {e₁ : Fin b → Fin d₁} (hei : Function.Injective e) (he : ∀ i, jc (e₁ i) = e (mid i))
    (h0 : ∀ j, e 0 ≠ jc j) (h1 : ∀ j, e (Fin.last _) ≠ jc j) (P : Finset (Fin (b + 2) × Fin d)) (hP : ∀ i j, (mid i, jc j) ∉ P)
    (ha : (Fin.last _, e 0) ∈ P) (hb : (0, e (Fin.last _)) ∉ P)
    (hAB : ((∀ j, j ≠ Fin.last _ → (0, e j) ∉ P) ∧ ∀ i, (mid i, e 0) ∉ P) ∨
      ((∀ i, i ≠ 0 → (i, e (Fin.last _)) ∉ P) ∧ ∀ j, (Fin.last _, e (mid j)) ∉ P)) {r : ℕ}
    (g : Fin r → Fin (b + 2) × Fin d) (hg : Function.Injective g) (h : ∀ p, p ∈ Set.range g ↔ p ∈ P ∧ p.2 ∉ Set.range e)
    (y : Matrix (Fin b) (Fin d₁) k) (s t : k) :
    ∫ Z, ψ (-(t * Z (Fin.last _, e 0))) * std ν ϖ c e (tm (cut P Z) + (ext mid jc y + single 0 (e (Fin.last _)) s)) * wt P Z
      ∂(Measure.pi fun _ => m) = (((resCard k : ℂ) ^ c)⁻¹) ^ r * (dl ν s * gI m ψ ν t) * std ν ϖ c e₁ y := by
  haveI := hm.haar
  have hmi : Function.Injective (mid : Fin b → _) := fun _ _ h => Fin.ext (by simpa [mid] using congrArg Fin.val h)
  have m0 : ∀ i : Fin b, (0 : Fin (b + 2)) ≠ mid i := fun i h => by simpa [mid] using congrArg Fin.val h
  have ml : ∀ i : Fin b, Fin.last (b + 1) ≠ mid i := fun i h => by
    have := congrArg Fin.val h; simp [mid] at this; omega
  have l0 : Fin.last (b + 1) ≠ 0 := by simp
  set Y := ext mid jc y + single 0 (e (Fin.last _)) s with hYd
  have hE : ∀ p ∈ P, ext mid jc y p.1 p.2 = 0 := fun p hp => ext_off y (by
    by_contra h
    push Not at h
    obtain ⟨⟨i, hi⟩, j, hj⟩ := h
    exact hP i j (by rw [← hi, ← hj]; exact hp))
  have hY : ∀ p ∈ P, Y p.1 p.2 = 0 := fun p hp => by
    rw [hYd, Matrix.add_apply, hE p hp, single_apply_of_ne, add_zero]
    rintro ⟨a, b⟩
    exact hb (by rw [a, b]; exact hp)
  have hd : ∀ Z, ((tm (cut P Z) + Y).submatrix id e).det = s * -Z (Fin.last _, e 0) * (y.submatrix id e₁).det := fun Z => by
    have e1 : ((tm (cut P Z) + Y).submatrix id e).submatrix mid mid = y.submatrix id e₁ := by
      ext i j
      have := hP i (e₁ j)
      simp [tm, cut, hYd, ← he, this, ext_mid hmi hc, single_apply, m0]
    have e2 : (tm (cut P Z) + Y).submatrix id e 0 (Fin.last _) = s := by
      simp [tm, cut, hYd, hb, ext_off y (Or.inl m0)]
    have e3 : (tm (cut P Z) + Y).submatrix id e (Fin.last _) 0 = Z (Fin.last _, e 0) := by
      have := hY _ ha
      simp only [submatrix_apply, id, Matrix.add_apply, this, tm, of_apply, cut, if_pos ha, add_zero]
    rcases hAB with ⟨x1, x2⟩ | ⟨x1, x2⟩
    · rw [detB _ (fun j hj => by simp [tm, cut, hYd, x1 j hj, ext_off y (Or.inl m0), single_apply, hei.eq_iff, hj.symm])
        (fun i => by simp [tm, cut, hYd, x2 i, ext_off y (Or.inr h0), single_apply, m0]), e1, e2, e3]
      ring
    · rw [detA _ (fun i hi => by simp [tm, cut, hYd, x1 i hi, ext_off y (Or.inr h1), single_apply, hi.symm])
        (fun j => by simp [tm, cut, hYd, x2 j, ext_off y (Or.inl ml), single_apply, l0.symm]), e1, e2, e3]
      ring
  have hr : ∀ j, jc j ∈ Set.range e ↔ j ∈ Set.range e₁ := fun j => by
    refine ⟨fun ⟨i, hi⟩ => ?_, fun ⟨i, hi⟩ => ⟨mid i, by rw [← he, hi]⟩⟩
    have a0 : i ≠ 0 := fun h => h0 j (h ▸ hi)
    have a1 : i ≠ Fin.last _ := fun h => h1 j (h ▸ hi)
    have a0' : i.1 ≠ 0 := fun h => a0 (Fin.ext h)
    have a1' : i.1 ≠ b + 1 := fun h => a1 (Fin.ext h)
    have : i = mid ⟨i.1 - 1, by omega⟩ := Fin.ext (by simp [mid]; omega)
    exact ⟨_, hc ((he _).trans (this ▸ hi))⟩
  have hA : (∏ p : Fin (b + 2) × Fin d, if p ∈ P then 1 else ind (rad ϖ c e p.2) (Y p.1 p.2)) =
      (∏ p : Fin b × Fin d₁, ind (rad ϖ c e₁ p.2) (y p.1 p.2)) * ind 1 s := by
    rw [← prod_mid hmi hc hr hP y, ← Finset.prod_ite_eq_of_mem' Finset.univ ((0 : Fin (b + 2)), e (Fin.last _)) (fun _ => ind 1 s)
      (Finset.mem_univ _), ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun p _ => ?_
    by_cases hp : p = (0, e (Fin.last _))
    · subst hp
      simp [hb, hYd, ext_off y (Or.inl m0), rad_e, ind_zero]
    · rw [if_neg hp, mul_one, hYd, Matrix.add_apply, single_apply_of_ne, add_zero]
      rintro ⟨a, b⟩
      exact hp (Prod.ext a.symm b.symm)
  let f : Fin (b + 2) × Fin d → k → ℂ := fun p x => (if p ∈ P then ind (rad ϖ c e p.2) x else ind 1 x) *
    if p = (Fin.last _, e 0) then dl ν (-x) * ψ (-(t * x)) else 1
  have key : ∀ Z, ψ (-(t * Z (Fin.last _, e 0))) * std ν ϖ c e (tm (cut P Z) + Y) * wt P Z =
      dl ν s * std ν ϖ c e₁ y * ∏ p, f p (Z p) := fun Z => by
    have e1 := split_prod (ϖ := ϖ) (c := c) (e := e) P Y hY Z
    rw [hA] at e1
    simp only [f, Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.mem_univ, if_true, std, hd]
    set A := ∏ p : Fin b × Fin d₁, ind (rad ϖ c e₁ p.2) (y p.1 p.2) with hA'
    set Q := ∏ p : Fin (b + 2) × Fin d, (if p ∈ P then ind (rad ϖ c e p.2) (Z p) else ind 1 (Z p)) with hQ
    have e2 : A * ind 1 s * Q * dl ν (s * -Z (Fin.last _, e 0) * (y.submatrix id e₁).det) =
        A * Q * (dl ν s * dl ν (-Z (Fin.last _, e 0)) * dl ν (y.submatrix id e₁).det) := by
      by_cases a1 : A = 0
      · simp [a1]
      by_cases a2 : Q = 0
      · simp [a2]
      have b1 : valuation k (y.submatrix id e₁).det ≤ 1 := val_det fun i j =>
        (ind_ne (Finset.prod_ne_zero_iff.1 a1 (i, e₁ j) (Finset.mem_univ _))).trans (rad_le hϖ _ _)
      have b2 := Finset.prod_ne_zero_iff.1 a2 _ (Finset.mem_univ (Fin.last _, e 0))
      rw [if_pos ha] at b2
      have b3 : valuation k (-Z (Fin.last _, e 0)) ≤ 1 := by simpa using (ind_ne b2).trans (rad_le hϖ _ _)
      by_cases a3 : valuation k s ≤ 1
      · rw [dl_mul (by rw [map_mul]; exact mul_le_one' a3 b3) b1, dl_mul a3 b3, ind, if_pos (by simpa using a3), mul_one]
      · rw [ind, if_neg (by simpa using a3), dl_of_ne (x := s) fun h => a3 h.le]; simp
    linear_combination ψ (-(t * Z (Fin.last _, e 0))) * dl ν (s * -Z (Fin.last _, e 0) * (y.submatrix id e₁).det) * e1 +
      ψ (-(t * Z (Fin.last _, e 0))) * e2
  simp only [key]
  rw [integral_const_mul, integral_fintype_prod_eq_prod f, ← prod_vol hm hϖ g hg h,
    ← Finset.prod_ite_eq_of_mem' Finset.univ (Fin.last (b + 1), e 0) (fun _ => gI m ψ ν t) (Finset.mem_univ _)]
  have : ∏ p, ∫ x, f p x ∂m = (∏ p : Fin (b + 2) × Fin d, ∫ x, (if p ∈ P then ind (rad ϖ c e p.2) x else ind 1 x) ∂m) *
      ∏ p, if p = (Fin.last (b + 1), e 0) then gI m ψ ν t else 1 := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun p _ => ?_
    by_cases hp : p = (Fin.last (b + 1), e 0)
    · subst hp
      simp only [f, if_pos ha, if_true, rad_e, int_ind_one hm, one_mul, ← gI_neg hm]
      congr 1
      funext x
      by_cases hx : valuation k x ≤ 1
      · simp [ind, hx]
      · rw [dl_of_ne (x := -x) fun h => hx (by simpa using h.le)]; simp
    · simp only [f, if_neg hp, mul_one]
  rw [this]; ring

end PositivityTheory.ThKG.Std
