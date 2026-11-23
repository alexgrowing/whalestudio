import Mathlib

noncomputable section

namespace Formalism.MainNotions.N.Ln34.LevelExpansions

open PowerSeries Finset

section Good

variable {LL V : Type*} [Field LL] [AddCommGroup V] [Module LL V] {ι : Type*} [Fintype ι]

def Gd (F : ℤ → Submodule LL V) (h : ℤ) (A : ι → PowerSeries LL) (v : ι → V) : Prop :=
  ∀ i : ℕ, ∑ j, coeff i (A j) • v j ∈ F (h - i)

variable {F : ℤ → Submodule LL V} {h : ℤ} {A : ι → PowerSeries LL} {v : ι → V}

private theorem sum_coeff_mul_smul_eq_antidiagonal (U : PowerSeries LL) (F' : ι → PowerSeries LL) (w' : ι → V) (i : ℕ) :
    ∑ j, coeff i (U * F' j) • w' j = ∑ pq ∈ antidiagonal i, coeff pq.1 U • ∑ j, coeff pq.2 (F' j) • w' j := by
  simp only [coeff_mul, Finset.sum_smul, Finset.smul_sum, mul_smul]
  exact Finset.sum_comm

theorem Gd.mul (hF : Antitone F) (H : Gd F h A v) (u : PowerSeries LL) :
    Gd F h (fun j => u * A j) v := by
  intro i
  show ∑ j, coeff i (u * A j) • v j ∈ F (h - i)
  rw [_root_.Formalism.MainNotions.N.Ln34.LevelExpansions.sum_coeff_mul_smul_eq_antidiagonal u A v i]
  refine Submodule.sum_mem _ fun pq hpq => Submodule.smul_mem _ _ ?_
  have hpq' : pq.1 + pq.2 = i := by
    first
    | exact Finset.HasAntidiagonal.mem_antidiagonal.mp hpq
    | simpa using hpq
  exact hF (show h - (i : ℤ) ≤ h - (pq.2 : ℤ) by omega) (H pq.2)

theorem Gd.unit (hF : Antitone F) {u : PowerSeries LL} (hu : IsUnit u)
    (H : Gd F h (fun j => u * A j) v) : Gd F h A v := by
  intro i
  have := Formalism.MainNotions.N.Ln34.LevelExpansions.Gd.mul hF H (↑hu.unit⁻¹ : PowerSeries LL) i
  simpa only [← mul_assoc, hu.val_inv_mul, one_mul] using this

theorem Gd.step (hF : Antitone F) {y u : PowerSeries LL} (hy : y = X * u) (hu : IsUnit u)
    {o : ι → LL} {A' : ι → PowerSeries LL} (hA : ∀ j, A j = C (o j) + y * A' j) (H : Gd F h A v) :
    ∑ j, o j • v j ∈ F h ∧ Gd F (h - 1) A' v := by
  subst hy
  have hc : ∀ j i, coeff (i + 1) (A j) = coeff i (u * A' j) := by
    intro j i
    rw [hA j, map_add, coeff_C, if_neg (by omega : i + 1 ≠ 0), zero_add, mul_assoc, coeff_succ_X_mul]
  refine ⟨?_, ?_⟩
  · have h0 := H 0
    have e : ∀ j, coeff 0 (A j) = o j := by
      intro j
      rw [hA j, map_add, coeff_C, if_pos rfl, mul_assoc, coeff_zero_X_mul, add_zero]
    simp only [e, Nat.cast_zero, sub_zero] at h0
    exact h0
  · apply Formalism.MainNotions.N.Ln34.LevelExpansions.Gd.unit hF hu
    intro i
    have := H (i + 1)
    simp only [hc] at this
    have hcast : (h - ((i + 1 : ℕ) : ℤ)) = h - 1 - (i : ℤ) := by push_cast; ring
    rw [hcast] at this
    exact this

theorem Gd.peel (hF : Antitone F) {y u : PowerSeries LL} (hy : y = X * u) (hu : IsUnit u) (N : ℕ) :
    ∀ (h : ℤ) (A A' : ι → PowerSeries LL) (p : ι → ℕ → LL),
      (∀ j, A j = ∑ k ∈ range N, C (p j k) * y ^ k + y ^ N * A' j) → Gd F h A v →
      ∀ k < N, ∑ j, p j k • v j ∈ F (h - k) := by
  induction N with
  | zero => intro h A A' p _ _ k hk; exact absurd hk (Nat.not_lt_zero k)
  | succ N ih =>
    intro h A A' p hA H k hk
    have hA' : ∀ j, A j = C (p j 0) + y * (∑ k ∈ range N, C (p j (k + 1)) * y ^ k + y ^ N * A' j) := by
      intro j
      rw [hA j, Finset.sum_range_succ', mul_add, Finset.mul_sum]
      have hs : ∑ k ∈ range N, C (p j (k + 1)) * y ^ (k + 1) = ∑ k ∈ range N, y * (C (p j (k + 1)) * y ^ k) :=
        Finset.sum_congr rfl fun k _ => by ring
      rw [hs]
      ring
    obtain ⟨h0, H'⟩ := Formalism.MainNotions.N.Ln34.LevelExpansions.Gd.step hF hy hu hA' H
    rcases k with _ | k
    · simp only [Nat.cast_zero, sub_zero]
      exact h0
    · have := ih (h - 1) (fun j => ∑ k ∈ range N, C (p j (k + 1)) * y ^ k + y ^ N * A' j) A'
        (fun j k => p j (k + 1)) (fun j => rfl) H' k (by omega)
      have hcast : h - 1 - (k : ℤ) = h - ((k + 1 : ℕ) : ℤ) := by push_cast; ring
      rw [hcast] at this
      exact this

private theorem sum_coeff_smul_eq_sum_coeff_y_pow_mul_smul {y : PowerSeries LL} {N : ℕ} {A' : ι → PowerSeries LL}
    {p : ι → ℕ → LL} (hA : ∀ j, A j = ∑ k ∈ range N, C (p j k) * y ^ k + y ^ N * A' j)
    (h0 : ∀ k < N, ∑ j, p j k • v j = 0) (i : ℕ) :
    ∑ j, coeff i (A j) • v j = ∑ j, coeff i (y ^ N * A' j) • v j := by
  have e : ∀ j, coeff i (A j) = ∑ k ∈ range N, p j k * coeff i (y ^ k) + coeff i (y ^ N * A' j) := by
    intro j
    rw [hA j, map_add, map_sum]
    simp only [coeff_C_mul]
  have hk0 : ∀ k ∈ range N, ∑ j, (p j k * coeff i (y ^ k)) • v j = 0 := by
    intro k hk
    calc ∑ j, (p j k * coeff i (y ^ k)) • v j = coeff i (y ^ k) • ∑ j, p j k • v j := by
          rw [Finset.smul_sum]
          exact Finset.sum_congr rfl fun j _ => by rw [mul_comm, mul_smul]
      _ = 0 := by rw [h0 k (Finset.mem_range.mp hk), smul_zero]
  simp only [e, add_smul, Finset.sum_add_distrib, Finset.sum_smul]
  rw [Finset.sum_comm, Finset.sum_eq_zero hk0, zero_add]

theorem Gd.strip {y : PowerSeries LL} {N : ℕ} {A' : ι → PowerSeries LL} {p : ι → ℕ → LL}
    (hA : ∀ j, A j = ∑ k ∈ range N, C (p j k) * y ^ k + y ^ N * A' j)
    (h0 : ∀ k < N, ∑ j, p j k • v j = 0) (H : Gd F h A v) : Gd F h (fun j => y ^ N * A' j) v := by
  intro i
  have e := _root_.Formalism.MainNotions.N.Ln34.LevelExpansions.sum_coeff_smul_eq_sum_coeff_y_pow_mul_smul hA h0 i
  have := H i
  rw [e] at this
  exact this

def Fv (LL V : Type*) [Field LL] [AddCommGroup V] [Module LL V] (a : ℤ) : Submodule LL V :=
  if 0 < a then ⊥ else ⊤

theorem Fv_anti : Antitone (Fv LL V) := by
  intro a b hab
  unfold Fv
  split_ifs <;> first | exact bot_le | exact le_top | (exfalso; omega)

theorem Gd_Fv {N : ℕ} (H : ∀ i < N, ∑ j, coeff i (A j) • v j = 0) : Gd (Fv LL V) N A v := by
  intro i
  by_cases hi : i < N
  · rw [H i hi]
    exact Submodule.zero_mem _
  · have hn : ¬ (0 : ℤ) < (N : ℤ) - (i : ℤ) := by omega
    unfold Fv
    rw [if_neg hn]
    exact Submodule.mem_top

theorem Fv_zero {N k : ℕ} (hk : k < N) {z : V} (hz : z ∈ Fv LL V ((N : ℤ) - k)) : z = 0 := by
  have hp : (0 : ℤ) < (N : ℤ) - (k : ℤ) := by omega
  unfold Fv at hz
  rw [if_pos hp, Submodule.mem_bot] at hz
  exact hz

theorem peel1 {y u : PowerSeries LL} (hy : y = X * u) (hu : IsUnit u) {N : ℕ} {A G : PowerSeries LL}
    {c : ℕ → LL} (hA : A = ∑ k ∈ range N, C (c k) * y ^ k + y ^ N * G)
    (h0 : ∀ i < N, coeff i A = 0) : ∀ k < N, c k = 0 := by
  intro k hk
  have hFC : Gd (Fv LL LL) (N : ℤ) (fun _ : Unit => A) (fun _ => (1 : LL)) :=
    Gd_Fv (fun i hi => by simpa using h0 i hi)
  have hmem := Formalism.MainNotions.N.Ln34.LevelExpansions.Gd.peel (F := Fv LL LL) (v := fun _ : Unit => (1 : LL))
    Fv_anti hy hu N (N : ℤ) (fun _ => A) (fun _ => G) (fun _ k => c k) (fun _ => hA) hFC k hk
  have h1 := Fv_zero hk hmem
  simpa using h1

private theorem algebraMap_powerSeries_eq_C (c : LL) : algebraMap LL (PowerSeries LL) c = C c := by
  first
  | rfl
  | simp
  | exact PowerSeries.algebraMap_apply' c

theorem poly_expand (y : PowerSeries LL) (N : ℕ) : ∀ Q : Polynomial LL, ∃ G : PowerSeries LL,
    Polynomial.aeval y Q = ∑ k ∈ range N, C (Q.coeff k) * y ^ k + y ^ N * G := by
  induction N with
  | zero => intro Q; exact ⟨Polynomial.aeval y Q, by simp⟩
  | succ N ih =>
    intro Q
    obtain ⟨G, hG⟩ := ih Q.divX
    refine ⟨G, ?_⟩
    have hQ : Polynomial.aeval y Q = Polynomial.aeval y Q.divX * y + C (Q.coeff 0) := by
      have e := congrArg (Polynomial.aeval y) (Polynomial.divX_mul_X_add Q)
      rw [map_add, map_mul, Polynomial.aeval_X, Polynomial.aeval_C, algebraMap_powerSeries_eq_C] at e
      exact e.symm
    rw [hQ, hG, Finset.sum_range_succ', add_mul, Finset.sum_mul]
    have hs : ∑ k ∈ range N, C (Q.divX.coeff k) * y ^ k * y = ∑ k ∈ range N, C (Q.coeff (k + 1)) * y ^ (k + 1) := by
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Polynomial.coeff_divX]
      ring
    rw [hs]
    ring

private theorem coeff_eq_zero_of_isUnit_of_coeff_mul_eq_zero {u E : PowerSeries LL} (hu : IsUnit u) {n : ℕ}
    (h : ∀ i < n, coeff i (u * E) = 0) : ∀ i < n, coeff i E = 0 := by
  intro i hi
  have hE : E = ↑hu.unit⁻¹ * (u * E) := by rw [← mul_assoc, hu.val_inv_mul, one_mul]
  rw [hE, coeff_mul]
  refine Finset.sum_eq_zero fun pq hpq => ?_
  have hpq' : pq.1 + pq.2 = i := by
    first
    | exact Finset.HasAntidiagonal.mem_antidiagonal.mp hpq
    | simpa using hpq
  rw [h pq.2 (by omega), mul_zero]

private theorem sum_coeff_smul_eq_of_isUnit_mul_eq {u : PowerSeries LL} (hu : IsUnit u) {G : PowerSeries LL} {w : V} {n : ℕ}
    (H : ∀ i < n, ∑ j, coeff i (u * A j) • v j = coeff i (u * G) • w) :
    ∀ i < n, ∑ j, coeff i (A j) • v j = coeff i G • w := by
  intro i hi
  have e1 := sum_coeff_mul_smul_eq_antidiagonal (↑hu.unit⁻¹ : PowerSeries LL) (fun j => u * A j) v i
  simp only [← mul_assoc, hu.val_inv_mul, one_mul] at e1
  rw [e1]
  have e2 : coeff i G = ∑ pq ∈ antidiagonal i, coeff pq.1 (↑hu.unit⁻¹ : PowerSeries LL) * coeff pq.2 (u * G) := by
    rw [← coeff_mul, ← mul_assoc, hu.val_inv_mul, one_mul]
  rw [e2, Finset.sum_smul]
  refine Finset.sum_congr rfl fun pq hpq => ?_
  have hpq' : pq.1 + pq.2 = i := by
    first
    | exact Finset.HasAntidiagonal.mem_antidiagonal.mp hpq
    | simpa using hpq
  rw [H pq.2 (by omega), mul_smul]

private theorem sum_smul_eq_smul_of_coeff_expansion {y u : PowerSeries LL} (hy : y = X * u) (hu : IsUnit u) {N : ℕ}
    {A₀ A₀' : ι → PowerSeries LL} {p : ι → ℕ → LL} {v₀ : ι → V} {G G' : PowerSeries LL} {c : ℕ → LL} {w : V}
    (hA : ∀ j, A₀ j = ∑ k ∈ range N, C (p j k) * y ^ k + y ^ N * A₀' j)
    (hG : G = ∑ k ∈ range N, C (c k) * y ^ k + y ^ N * G')
    (H : ∀ i < N, ∑ j, coeff i (A₀ j) • v₀ j = coeff i G • w) :
    ∀ k < N, ∑ j, p j k • v₀ j = c k • w := by
  intro k hk
  have hFC : Gd (Fv LL V) (N : ℤ) (fun x : Option ι => Option.elim x G A₀)
      (fun x => Option.elim x (-w) v₀) := by
    apply Gd_Fv
    intro i hi
    rw [Fintype.sum_option]
    simp only [Option.elim]
    first
    | rw [H i hi, smul_neg, neg_add_cancel]
    | simp [H i hi]
  have hm := Formalism.MainNotions.N.Ln34.LevelExpansions.Gd.peel (F := Fv LL V) (v := fun x : Option ι => Option.elim x (-w) v₀)
    Fv_anti hy hu N (N : ℤ) (fun x => Option.elim x G A₀) (fun x => Option.elim x G' A₀')
    (fun x k => Option.elim x (c k) (fun j => p j k))
    (fun x => by cases x with | none => exact hG | some j => exact hA j) hFC k hk
  have h0 := Fv_zero hk hm
  rw [Fintype.sum_option] at h0
  simp only [Option.elim, smul_neg] at h0
  exact (neg_add_eq_zero.mp h0).symm

theorem van_of_dvd {y u G : PowerSeries LL} (hy : y = X * u) (N : ℕ) :
    ∀ i < N, coeff i (y ^ N * G) = 0 := by
  have hd : (X : PowerSeries LL) ^ N ∣ y ^ N * G := by
    rw [hy, mul_pow, mul_assoc]
    exact Dvd.intro _ rfl
  first
  | exact PowerSeries.X_pow_dvd_iff.mp hd
  | (intro i hi; rw [hy, mul_pow, mul_assoc, PowerSeries.coeff_X_pow_mul', if_neg (by omega)])

end Good

section Div

variable {O LL : Type*} [CommRing O] [Field LL] [Algebra O LL] {A Z : Type*}
  (ev : Z → A → PowerSeries LL)

def Dv (O : Type*) [CommRing O] [Algebra O LL] (y : Z → PowerSeries LL) : Prop :=
  ∀ a : A, ∃ (o : O) (a' : A), ∀ z, ev z a = C (algebraMap O LL o) + y z * ev z a'

variable {ev}

theorem Dv.expand {y : Z → PowerSeries LL} (H : Dv ev O y) (N : ℕ) : ∀ a : A, ∃ (p : ℕ → O) (a' : A),
    ∀ z, ev z a = ∑ k ∈ range N, C (algebraMap O LL (p k)) * y z ^ k + y z ^ N * ev z a' := by
  induction N with
  | zero => intro a; exact ⟨fun _ => 0, a, fun z => by simp⟩
  | succ N ih =>
    intro a
    obtain ⟨o, a₁, ha⟩ := H a
    obtain ⟨p, a', hp⟩ := ih a₁
    refine ⟨fun k => if k = 0 then o else p (k - 1), a', fun z => ?_⟩
    have key : ∑ k ∈ range (N + 1), C (algebraMap O LL (if k = 0 then o else p (k - 1))) * y z ^ k
        = C (algebraMap O LL o) + y z * ∑ k ∈ range N, C (algebraMap O LL (p k)) * y z ^ k := by
      rw [Finset.sum_range_succ', Finset.mul_sum, add_comm]
      congr 1
      · first
        | rw [if_pos rfl, pow_zero, mul_one]
        | simp
      · refine Finset.sum_congr rfl fun k _ => ?_
        rw [if_neg (show k + 1 ≠ 0 by omega), Nat.add_sub_cancel]
        ring
    rw [key, ha z, hp z]
    ring

theorem Dv.transfer {y : Z → PowerSeries LL} (H : Dv ev O y) {z z' : Z} {u u' : PowerSeries LL}
    (hy : y z = X * u) (hu : IsUnit u) (hy' : y z' = X * u') (N : ℕ) (a b : A) (x : LL)
    (h : ∀ i < N, coeff i (ev z a) = x * coeff i (ev z b)) :
    ∀ i < N, coeff i (ev z' a) = x * coeff i (ev z' b) := by
  obtain ⟨pa, a', ha⟩ := H.expand N a
  obtain ⟨pb, b', hb⟩ := H.expand N b
  have hexp : ∀ w, ev w a - C x * ev w b = ∑ k ∈ range N, C (algebraMap O LL (pa k) - x * algebraMap O LL (pb k)) * y w ^ k
      + y w ^ N * (ev w a' - C x * ev w b') := by
    intro w
    have hs : ∑ k ∈ range N, C (algebraMap O LL (pa k) - x * algebraMap O LL (pb k)) * y w ^ k
        = ∑ k ∈ range N, C (algebraMap O LL (pa k)) * y w ^ k - C x * ∑ k ∈ range N, C (algebraMap O LL (pb k)) * y w ^ k := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_sub, map_mul]
      ring
    rw [hs, ha w, hb w]
    ring
  have hc : ∀ k < N, algebraMap O LL (pa k) - x * algebraMap O LL (pb k) = 0 :=
    Formalism.MainNotions.N.Ln34.LevelExpansions.peel1 hy hu (hexp z) (fun i hi => by
      rw [map_sub, coeff_C_mul, h i hi, sub_self])
  intro i hi
  have hz' : ev z' a - C x * ev z' b = y z' ^ N * (ev z' a' - C x * ev z' b') := by
    rw [hexp z', Finset.sum_eq_zero (fun k hk => by rw [hc k (Finset.mem_range.mp hk), map_zero, zero_mul]), zero_add]
  have h1 := Formalism.MainNotions.N.Ln34.LevelExpansions.van_of_dvd (G := ev z' a' - C x * ev z' b') hy' N i hi
  rw [← hz', map_sub, coeff_C_mul] at h1
  exact sub_eq_zero.mp h1

theorem unit_add_C {y u : PowerSeries LL} (hy : y = X * u) {δ : LL} (hδ : δ ≠ 0) : IsUnit (y + C δ) := by
  subst hy
  first
  | (rw [PowerSeries.isUnit_iff_constantCoeff]; simpa using hδ)
  | exact isUnit_of_mul_eq_one _ _ (PowerSeries.mul_inv_cancel _ (by simpa using hδ))

theorem integ {yU yD : Z → PowerSeries LL} (HU : Dv ev O yU) (HD : Dv ev O yD) {zU zD : Z}
    {u u' : PowerSeries LL} (hyU : yU zU = X * u) (hu : IsUnit u) (hyD : yD zD = X * u')
    (hu' : IsUnit u') {δ : LL} (hδ : δ ≠ 0) (hUD : yU zD = yD zD + C δ) (a : A) (x a₂ : LL)
    (h b B : ℕ) (hb : b ≤ h) (hU : ∀ i, i + b < h → coeff i (ev zU a) = 0)
    (hD : ∀ i < h + B, coeff i (ev zD a) = x * coeff i ((C a₂ * yU zD * yD zD) ^ h)) :
    ∀ k < B, ∃ o : O, algebraMap O LL o = x * a₂ ^ h * (b.choose k : LL) * δ ^ (b - k) := by
  intro k hk
  obtain ⟨p, a₁, hp⟩ := HU.expand (h - b) a
  have hp0 : ∀ m < h - b, algebraMap O LL (p m) = 0 :=
    peel1 hyU hu (hp zU) (fun i hi => hU i (by omega))
  have hA : ∀ z, ev z a = yU z ^ (h - b) * ev z a₁ := by
    intro z
    rw [hp z, Finset.sum_eq_zero (fun m hm => by rw [hp0 m (Finset.mem_range.mp hm), map_zero, zero_mul]), zero_add]
  obtain ⟨q, a₃, hq⟩ := HD.expand (h + B) a₁
  obtain ⟨P, hP⟩ : ∃ P : Polynomial LL,
      P = Polynomial.C (x * a₂ ^ h) * (Polynomial.X + Polynomial.C δ) ^ b * Polynomial.X ^ h := ⟨_, rfl⟩
  obtain ⟨GT, hGT⟩ := poly_expand (yD zD) (h + B) P
  have hPt : Polynomial.aeval (yD zD) P = C (x * a₂ ^ h) * yU zD ^ b * yD zD ^ h := by
    rw [hP, hUD]
    first
    | (simp only [map_mul, map_pow, map_add, Polynomial.aeval_X, Polynomial.aeval_C, algebraMap_powerSeries_eq_C]; done)
    | (simp only [map_mul, map_pow, map_add, Polynomial.aeval_X, Polynomial.aeval_C, algebraMap_powerSeries_eq_C]; ring)
  have hsU : IsUnit (yU zD) := by rw [hUD]; exact unit_add_C hyD hδ
  have key : yU zD ^ (h - b) * Polynomial.aeval (yD zD) P = C x * (C a₂ * yU zD * yD zD) ^ h := by
    rw [hPt]
    have hsp : yU zD ^ (h - b) * yU zD ^ b = yU zD ^ h := by rw [← pow_add, Nat.sub_add_cancel hb]
    calc yU zD ^ (h - b) * (C (x * a₂ ^ h) * yU zD ^ b * yD zD ^ h)
        = C (x * a₂ ^ h) * (yU zD ^ (h - b) * yU zD ^ b) * yD zD ^ h := by ring
      _ = C x * (C a₂ * yU zD * yD zD) ^ h := by rw [hsp, map_mul, map_pow]; ring
  have hE0 : ∀ i < h + B, coeff i (ev zD a₁ - Polynomial.aeval (yD zD) P) = 0 :=
    coeff_eq_zero_of_isUnit_of_coeff_mul_eq_zero (hsU.pow (h - b)) (fun i hi => by
      rw [mul_sub, ← hA zD, key, map_sub, coeff_C_mul, hD i hi, sub_self])
  have hEexp : ev zD a₁ - Polynomial.aeval (yD zD) P
      = ∑ m ∈ range (h + B), C (algebraMap O LL (q m) - P.coeff m) * yD zD ^ m + yD zD ^ (h + B) * (ev zD a₃ - GT) := by
    have hs2 : ∑ m ∈ range (h + B), C (algebraMap O LL (q m) - P.coeff m) * yD zD ^ m
        = ∑ m ∈ range (h + B), C (algebraMap O LL (q m)) * yD zD ^ m - ∑ m ∈ range (h + B), C (P.coeff m) * yD zD ^ m := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun m _ => by rw [map_sub, sub_mul]
    rw [hs2, hq zD, hGT]
    ring
  have hc : algebraMap O LL (q (h + k)) - P.coeff (h + k) = 0 :=
    peel1 hyD hu' hEexp hE0 (h + k) (by omega)
  refine ⟨q (h + k), ?_⟩
  rw [sub_eq_zero] at hc
  rw [hc, hP, add_comm h k, Polynomial.coeff_mul_X_pow, Polynomial.coeff_C_mul, Polynomial.coeff_X_add_C_pow]
  ring

theorem caseB {V₁ V₂ : Type*} [AddCommGroup V₁] [Module LL V₁] [AddCommGroup V₂] [Module LL V₂]
    {ι : Type*} [Fintype ι] {yU yD : Z → PowerSeries LL} (HU : Dv ev O yU) (HD : Dv ev O yD)
    {zU zD : Z} {u u' : PowerSeries LL} (hyU : yU zU = X * u) (hu : IsUnit u) (hyD : yD zD = X * u')
    (hu' : IsUnit u') {δ : LL} (hδ : δ ≠ 0) (hDU : yD zU = yU zU + C δ)
    (a : ι → A) (v₁ : ι → V₁) (v₂ : ι → V₂) (w : V₂) {FU FD : ℤ → Submodule LL V₁}
    (hFU : Antitone FU) (hFD : Antitone FD) (h b B η : ℕ) (hb : b ≤ h) (hBb : B + 2 * η < b) (κ : LL)
    (hZ : ∀ o : ι → O, ∑ j, algebraMap O LL (o j) • v₁ j ∈ FD (η + 1) →
      ∑ j, algebraMap O LL (o j) • v₁ j = 0 ∧ ∑ j, algebraMap O LL (o j) • v₂ j = 0)
    (hD : Gd FD h (fun j => ev zD (a j)) v₁) (hU : Gd FU h (fun j => ev zU (a j)) v₁)
    (h2 : ∀ i ≤ h, ∑ j, coeff i (ev zU (a j)) • v₂ j =
      coeff i (C κ * yU zU ^ (h - b) * yD zU ^ (h + B)) • w) :
    ∃ o : ι → O, ∑ j, algebraMap O LL (o j) • v₁ j ∈ FU (η + 1) ∧
      ∑ j, algebraMap O LL (o j) • v₂ j = κ • w := by
  choose p a₁ hp using fun j => HD.expand (h - η) (a j)
  have hnull : ∀ k < h - η, ∑ j, algebraMap O LL (p j k) • v₁ j = 0 ∧ ∑ j, algebraMap O LL (p j k) • v₂ j = 0 := by
    intro k hk
    apply hZ (fun j => p j k)
    have hm := Formalism.MainNotions.N.Ln34.LevelExpansions.Gd.peel hFD hyD hu' (h - η) (h : ℤ) (fun j => ev zD (a j)) (fun j => ev zD (a₁ j))
      (fun j k => algebraMap O LL (p j k)) (fun j => hp j zD) hD k hk
    exact hFD (by omega) hm
  have hsU : IsUnit (yD zU) := by rw [hDU]; exact unit_add_C hyU hδ
  have hFC1 : Gd FU h (fun j => ev zU (a₁ j)) v₁ := by
    have hs : Gd FU h (fun j => yD zU ^ (h - η) * ev zU (a₁ j)) v₁ :=
      Formalism.MainNotions.N.Ln34.LevelExpansions.Gd.strip (F := FU) (h := (h : ℤ)) (A := fun j => ev zU (a j)) (v := v₁) (y := yD zU)
        (N := h - η) (A' := fun j => ev zU (a₁ j)) (p := fun j k => algebraMap O LL (p j k))
        (fun j => hp j zU) (fun k hk => (hnull k hk).1) hU
    exact Formalism.MainNotions.N.Ln34.LevelExpansions.Gd.unit hFU (hsU.pow (h - η)) hs
  have hv2 : ∀ i < h + 1, ∑ j, coeff i (yD zU ^ (h - η) * ev zU (a₁ j)) • v₂ j
      = coeff i (yD zU ^ (h - η) * (C κ * yU zU ^ (h - b) * yD zU ^ (B + η))) • w := by
    intro i hi
    have e : ∑ j, coeff i (ev zU (a j)) • v₂ j = ∑ j, coeff i (yD zU ^ (h - η) * ev zU (a₁ j)) • v₂ j :=
      sum_coeff_smul_eq_sum_coeff_y_pow_mul_smul (v := v₂) (A := fun j => ev zU (a j)) (A' := fun j => ev zU (a₁ j))
        (p := fun j k => algebraMap O LL (p j k)) (y := yD zU) (N := h - η)
        (fun j => hp j zU) (fun k hk => (hnull k hk).2) i
    have hpow : yD zU ^ (h - η) * (C κ * yU zU ^ (h - b) * yD zU ^ (B + η))
        = C κ * yU zU ^ (h - b) * yD zU ^ (h + B) := by
      rw [show h + B = (h - η) + (B + η) by omega]
      ring
    rw [← e, hpow, h2 i (by omega)]
  have hv2' : ∀ i < h + 1, ∑ j, coeff i (ev zU (a₁ j)) • v₂ j = coeff i (C κ * yU zU ^ (h - b) * yD zU ^ (B + η)) • w :=
    sum_coeff_smul_eq_of_isUnit_mul_eq (A := fun j => ev zU (a₁ j)) (v := v₂) (hsU.pow (h - η)) hv2
  choose q a₂ hq using fun j => HU.expand (B + η + (h - b) + 1) (a₁ j)
  obtain ⟨P, hP⟩ : ∃ P : Polynomial LL,
      P = Polynomial.C κ * (Polynomial.X + Polynomial.C δ) ^ (B + η) * Polynomial.X ^ (h - b) := ⟨_, rfl⟩
  obtain ⟨G', hG'⟩ := poly_expand (yU zU) (B + η + (h - b) + 1) P
  have hPt : Polynomial.aeval (yU zU) P = C κ * yU zU ^ (h - b) * yD zU ^ (B + η) := by
    rw [hP, hDU]
    simp only [map_mul, map_pow, map_add, Polynomial.aeval_X, Polynomial.aeval_C, algebraMap_powerSeries_eq_C]
    ring
  rw [hPt] at hG'
  have huniq : ∑ j, algebraMap O LL (q j (B + η + (h - b))) • v₂ j = P.coeff (B + η + (h - b)) • w :=
    sum_smul_eq_smul_of_coeff_expansion (v₀ := v₂) (w := w) (A₀ := fun j => ev zU (a₁ j)) (A₀' := fun j => ev zU (a₂ j))
      (p := fun j k => algebraMap O LL (q j k)) (c := fun k => P.coeff k) hyU hu (fun j => hq j zU) hG'
      (fun i hi => hv2' i (by omega)) (B + η + (h - b)) (by omega)
  have hm1 := Formalism.MainNotions.N.Ln34.LevelExpansions.Gd.peel hFU hyU hu (B + η + (h - b) + 1) (h : ℤ) (fun j => ev zU (a₁ j))
    (fun j => ev zU (a₂ j)) (fun j k => algebraMap O LL (q j k)) (fun j => hq j zU) hFC1 (B + η + (h - b)) (by omega)
  refine ⟨fun j => q j (B + η + (h - b)), hFU (by omega) hm1, ?_⟩
  show ∑ j, algebraMap O LL (q j (B + η + (h - b))) • v₂ j = κ • w
  rw [huniq, hP, Polynomial.coeff_mul_X_pow, Polynomial.coeff_C_mul, Polynomial.coeff_X_add_C_pow]
  simp

end Div

section Num

theorem caseC {O K : Type*} [CommRing O] [Field K] [Algebra O K] (l : ℕ) [Fact l.Prime] (δ : O)
    (hδ : δ ^ 2 ∣ (l : O)) (hun : ∀ m : ℕ, ¬ l ∣ m → IsUnit (m : O)) (x : K) (b B : ℕ) (hB : 1 ≤ B)
    (hBb : B ≤ b) (o : O)
    (ho : algebraMap O K o = x * (b.choose (B - 1) : K) * (algebraMap O K δ) ^ (b - (B - 1)))
    (y : ℕ) (hy : b - B + 1 + 2 * padicValNat l (b.choose (B - 1)) ≤ 2 * y) :
    ∃ o : O, algebraMap O K o = (l : K) ^ y * x := by
  obtain ⟨c, hc⟩ : ∃ c, c = b.choose (B - 1) := ⟨_, rfl⟩
  rw [← hc] at ho hy
  have hc0 : c ≠ 0 := by rw [hc]; exact (Nat.choose_pos (by omega)).ne'
  obtain ⟨c', hc'⟩ := (pow_padicValNat_dvd : l ^ padicValNat l c ∣ c)
  have hnd : ¬ l ∣ c' := by
    rintro ⟨d, rfl⟩
    have hd : l ^ (padicValNat l c + 1) ∣ l ^ padicValNat l c * (l * d) := ⟨d, by ring⟩
    rw [← hc'] at hd
    exact pow_succ_padicValNat_not_dvd (p := l) hc0 hd
  generalize hv : padicValNat l c = v at hc' hy
  obtain ⟨r, hr⟩ := hδ
  have hu := hun c' hnd
  refine ⟨o * ↑hu.unit⁻¹ * δ ^ (2 * (y - v) - (b - (B - 1))) * r ^ (y - v), ?_⟩
  have hlK : (l : K) = algebraMap O K δ ^ 2 * algebraMap O K r := by
    rw [← map_natCast (algebraMap O K) l, hr, map_mul, map_pow]
  have hcK : (c : K) = (l : K) ^ v * (c' : K) := by rw [hc']; push_cast; ring
  have hinv : algebraMap O K (↑hu.unit⁻¹ : O) * (c' : K) = 1 := by
    rw [← map_natCast (algebraMap O K) c', ← map_mul, hu.val_inv_mul, map_one]
  have h2 : 2 * (y - v) = (b - (B - 1)) + (2 * (y - v) - (b - (B - 1))) := by omega
  have hy2 : y = v + (y - v) := by omega
  rw [map_mul, map_mul, map_mul, ho, map_pow, map_pow, hcK]
  calc _ = x * (l : K) ^ v * (algebraMap O K (↑hu.unit⁻¹ : O) * (c' : K))
        * (algebraMap O K δ ^ (b - (B - 1)) * algebraMap O K δ ^ (2 * (y - v) - (b - (B - 1))))
        * algebraMap O K r ^ (y - v) := by ring
    _ = x * (l : K) ^ v * (algebraMap O K δ ^ 2 * algebraMap O K r) ^ (y - v) := by
        rw [hinv, ← pow_add, ← h2, pow_mul, mul_pow]
        ring
    _ = (l : K) ^ y * x := by
        rw [← hlK, mul_assoc, ← pow_add, ← hy2, mul_comm]

theorem yc_bound (l : ℕ) [hl : Fact l.Prime] (b B η h : ℕ) (hb : b ≤ h)
    (hbB : b ≤ B + 2 * η) (hBb : B ≤ b) :
    b - B + 1 + 2 * padicValNat l (b.choose (B - 1)) ≤ 2 * ⌈(η : ℝ) + 1 / 2 + Real.logb l h⌉₊ := by
  obtain ⟨v, hv⟩ : ∃ v, v = padicValNat l (b.choose (B - 1)) := ⟨_, rfl⟩
  rw [← hv]
  have hvlog : v ≤ Nat.log l b := by
    rw [hv, ← Nat.factorization_def _ hl.out]
    exact Nat.factorization_choose_le_log
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hl.out.one_lt
  have hvle : (v : ℝ) ≤ Real.logb l h := by
    rcases Nat.eq_zero_or_pos v with hv0 | hv0
    · rw [hv0, Nat.cast_zero]
      rcases Nat.eq_zero_or_pos h with h0 | h0
      · rw [h0, Nat.cast_zero, Real.logb_zero]
      · exact Real.logb_nonneg hl1 (by exact_mod_cast h0)
    · have hb0 : b ≠ 0 := by
        rintro rfl
        rw [Nat.log_zero_right] at hvlog
        omega
      have hpow : l ^ v ≤ h :=
        (Nat.pow_le_pow_right hl.out.pos hvlog).trans ((Nat.pow_log_le_self l hb0).trans hb)
      have hh : (0 : ℝ) < h := by exact_mod_cast (Nat.pos_of_ne_zero hb0).trans_le hb
      rw [Real.le_logb_iff_rpow_le hl1 hh, Real.rpow_natCast]
      exact_mod_cast hpow
  have hcl := Nat.le_ceil ((η : ℝ) + 1 / 2 + Real.logb l h)
  have h1 : ((b - B : ℕ) : ℝ) ≤ 2 * η := by exact_mod_cast (by omega : b - B ≤ 2 * η)
  have key : ((b - B + 1 + 2 * v : ℕ) : ℝ) ≤ ((2 * ⌈(η : ℝ) + 1 / 2 + Real.logb l h⌉₊ : ℕ) : ℝ) := by
    push_cast
    linarith
  exact_mod_cast key

end Num

end Formalism.MainNotions.N.Ln34.LevelExpansions

end
