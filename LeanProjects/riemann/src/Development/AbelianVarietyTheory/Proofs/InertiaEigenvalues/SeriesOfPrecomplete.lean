import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ConvZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemRangeOfFrobeniusEquationCyclotomicFixed

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL GlobalTheory.Decompl GlobalTheory.FrobDescent

noncomputable section

namespace GlobalTheory.HWL.MatDecompl

section Abstract

variable {E A R : Type} [CommRing E] [CommRing A] [CommRing R] {n : Type} [Fintype n]
  [DecidableEq n] {ι : A →+* R} {p : ℕ} {t : R}

def NearM (ι : A →+* R) (p : ℕ) (t : R) (m : ℕ) (X : Matrix n n R) : Prop :=
  ∀ i j, Near ι p t m (X i j)

def matS (S : Subring R) : Subring (Matrix n n R) where
  carrier := {X | ∀ i j, X i j ∈ S}
  mul_mem' := fun {X Y} hX hY i j => by
    rw [Matrix.mul_apply]; exact sum_mem fun k _ => mul_mem (hX i k) (hY k j)
  one_mem' := fun i j => by
    rw [Matrix.one_apply]; split_ifs; exacts [one_mem _, zero_mem _]
  add_mem' := fun hX hY i j => add_mem (hX i j) (hY i j)
  zero_mem' := fun _ _ => zero_mem _
  neg_mem' := fun hX i j => neg_mem (hX i j)

omit [Fintype n] [DecidableEq n] in
theorem NearM.sub {m : ℕ} {X Y : Matrix n n R} (hX : NearM ι p t m X) (hY : NearM ι p t m Y) :
    NearM ι p t m (X - Y) := fun i j => (hX i j).sub (hY i j)

omit [Fintype n] [DecidableEq n] in
theorem NearM.add {m : ℕ} {X Y : Matrix n n R} (hX : NearM ι p t m X) (hY : NearM ι p t m Y) :
    NearM ι p t m (X + Y) := fun i j => (hX i j).add (hY i j)

omit [Fintype n] [DecidableEq n] in
theorem NearM.neg {m : ℕ} {X : Matrix n n R} (hX : NearM ι p t m X) :
    NearM ι p t m (-X) := fun i j => (hX i j).neg

omit [Fintype n] [DecidableEq n] in
theorem NearM.of_smul (m : ℕ) (X : Matrix n n R) : NearM ι p t m ((p : R) • X) :=
  fun i j => Near.of_mul m (X i j)

omit [Fintype n] [DecidableEq n] in
theorem NearM.mono {τ : A} (hτ : ι τ = t) {m k : ℕ} (h : m ≤ k) {X : Matrix n n R}
    (hX : NearM ι p t k X) : NearM ι p t m X := fun i j => (hX i j).mono hτ h

omit [Fintype n] [DecidableEq n] in
theorem NearM.cancel (ht : IsUnit t) {m k : ℕ} {X : Matrix n n R}
    (hX : NearM ι p t (k + m) (t ^ k • X)) : NearM ι p t m X := fun i j => (hX i j).cancel ht

omit [DecidableEq n] in
theorem NearM.mul {m k : ℕ} {X Y : Matrix n n R} (hX : NearM ι p t m X) (hY : NearM ι p t k Y) :
    NearM ι p t (m + k) (X * Y) := fun i j => by
  rw [Matrix.mul_apply]; exact Near.sum _ fun k _ => (hX i k).mul (hY k j)

omit [Fintype n] [DecidableEq n] in
theorem NearM.smul {τ : A} (hτ : ι τ = t) {m : ℕ} (k : ℕ) {X : Matrix n n R}
    (hX : NearM ι p t m X) : NearM ι p t m (t ^ k • X) := fun i j => by
  have := (hX i j).mul_ι (τ ^ k)
  rwa [map_pow, hτ] at this

omit [Fintype n] in
theorem NearM.one : NearM ι p t 0 (1 : Matrix n n R) := fun i j => by
  rw [Matrix.one_apply]
  split_ifs
  · exact ⟨1, 0, by simp⟩
  · exact Near.zero 0

omit [DecidableEq n] in
theorem exists_pole {τ : A} (hτ : ι τ = t) (X : Matrix n n R)
    (h : ∀ i j, ∃ k, Near ι p t 0 (t ^ k * X i j)) :
    ∃ K, ∀ K' ≥ K, NearM ι p t 0 (t ^ K' • X) := by
  choose k hk using h
  refine ⟨Finset.univ.sup fun q : n × n => k q.1 q.2, fun K' hK i j => ?_⟩
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le
    ((Finset.le_sup (f := fun q : n × n => k q.1 q.2) (Finset.mem_univ (i, j))).trans hK)
  have := (hk i j).mul_ι (τ ^ d)
  rw [map_pow, hτ, ← mul_assoc, ← pow_add, add_comm] at this
  exact this

theorem contract {τ : A} (hτ : ι τ = t) {S : Subring R}
    (meet : ∀ x, (∀ m, Near ι p t m x) → ∃ r, x = (p : R) * r)
    (comp : ∀ (k : ℕ) (f : ℕ → R), (∀ i, f i ∈ S) → (∀ i, Near ι p t (i + k) (f i)) →
      ∃ x ∈ S, ∀ m, Near ι p t (m + k) (x - ∑ i ∈ Finset.range m, f i))
    (T : Matrix n n R →+ Matrix n n R) (m : ℕ)
    (hT : ∀ k X, NearM ι p t (k + m) X → NearM ι p t (k + 1 + m) (T X))
    (hTS : ∀ X ∈ matS S, T X ∈ matS S) (y : Matrix n n R) (hy : y ∈ matS S)
    (hy' : NearM ι p t m y) :
    ∃ z ∈ matS S, NearM ι p t m z ∧ ∃ r, z = y + T z + (p : R) • r := by
  have h1 : ∀ k, T^[k] y ∈ matS S ∧ NearM ι p t (k + m) (T^[k] y) := by
    intro k
    induction k with
    | zero => exact ⟨hy, by rw [zero_add]; exact hy'⟩
    | succ k ih => rw [Function.iterate_succ_apply']; exact ⟨hTS _ ih.1, hT _ _ ih.2⟩
  choose z hz hz' using fun i j =>
    comp m (fun k => T^[k] y i j) (fun k => (h1 k).1 i j) (fun k => (h1 k).2 i j)
  have h2 : ∀ k, NearM ι p t (k + m) (Matrix.of z - ∑ i ∈ Finset.range k, T^[i] y) :=
    fun k i j => by
      rw [Matrix.sub_apply, Matrix.sum_apply]; exact hz' i j k
  have h3 : ∀ k, ∑ i ∈ Finset.range (k + 1), T^[i] y =
      y + T (∑ i ∈ Finset.range k, T^[i] y) := by
    intro k
    rw [Finset.sum_range_succ', map_sum, add_comm]
    simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
  choose r hr using fun i j => meet ((Matrix.of z - y - T (Matrix.of z)) i j) fun k => by
    have := ((h2 (k + 1)).sub (hT k _ (h2 k))).mono hτ (show k ≤ k + 1 + m by omega)
    rw [h3, map_sub] at this
    convert this i j using 1
    refine congrFun (congrFun ?_ i) j
    abel
  refine ⟨Matrix.of z, hz, by simpa using h2 0, Matrix.of r, ?_⟩
  have : Matrix.of z - y - T (Matrix.of z) = (p : R) • Matrix.of r := Matrix.ext hr
  rw [← this]
  abel

def opT (φ : R →+* R) (X Y : Matrix n n R) : Matrix n n R →+ Matrix n n R :=
  AddMonoidHom.mk' (fun Z => X * φ.mapMatrix Z * Y) fun _ _ => by rw [map_add, mul_add, add_mul]

theorem opT_apply (φ : R →+* R) (X Y Z : Matrix n n R) :
    opT φ X Y Z = X * φ.mapMatrix Z * Y := rfl

theorem near_opT {τ : A} (hτ : ι τ = t) (ht : IsUnit t) (hp : 2 ≤ p) {φ : R →+* R}
    (h3 : ∀ m x, Near ι p t m x → Near ι p t (p * m) (φ x)) {K : ℕ} {X Y : Matrix n n R}
    (hX : NearM ι p t 0 (t ^ K • X)) (hY : NearM ι p t 0 (t ^ K • Y)) (k : ℕ) (Z : Matrix n n R)
    (hZ : NearM ι p t (k + (2 * K + 1)) Z) :
    NearM ι p t (k + 1 + (2 * K + 1)) (opT φ X Y Z) := by
  have h : NearM ι p t (p * (k + (2 * K + 1))) (φ.mapMatrix Z) := fun i j => h3 _ _ (hZ i j)
  have := (hX.mul h).mul hY
  rw [smul_mul_assoc, smul_mul_assoc, mul_smul_comm, smul_smul, ← pow_add] at this
  exact NearM.cancel ht (k := K + K) (this.mono hτ (by nlinarith))

theorem opT_mem {φ : R →+* R} {S : Subring R} (hφS : ∀ x ∈ S, φ x ∈ S) {X Y : Matrix n n R}
    (hX : X ∈ matS S) (hY : Y ∈ matS S) : ∀ Z ∈ matS S, opT φ X Y Z ∈ matS S :=
  fun Z hZ => mul_mem (mul_mem hX (show φ.mapMatrix Z ∈ matS S from fun i j => hφS _ (hZ i j))) hY

theorem isUnit_of_mul_eq (hJ : ∀ x : R, IsUnit (1 + (p : R) * x)) {X Y r : Matrix n n R}
    (h : X * Y = 1 + (p : R) • r) : IsUnit X := by
  rw [Matrix.isUnit_iff_isUnit_det]
  refine isUnit_of_mul_isUnit_left (y := Y.det) ?_
  rw [← Matrix.det_mul, h, Matrix.det_one_add_smul, add_assoc, pow_two, ← mul_assoc, ← add_mul,
    mul_comm]
  exact hJ _

theorem exists_of_mem_modSub {io : E →+* R} {X : Matrix n n R} (h : X ∈ matS (modSub io p)) :
    ∃ (e : Matrix n n E) (r : Matrix n n R), X = io.mapMatrix e + (p : R) • r := by
  choose e r h using h
  exact ⟨Matrix.of e, Matrix.of r, Matrix.ext h⟩

omit [DecidableEq n] in
theorem exists_approx {φ : R →+* R} {D : Subring R} {hD : ∀ x ∈ D, φ x ∈ D} {m : ℕ}
    {X : Matrix n n R} (h : ∀ i j, ∃ u ∈ perfSub φ D hD, Near ι p t m (X i j - u)) :
    ∃ (N : ℕ) (u : Matrix n n R), (∀ i j, (φ ^ N) (u i j) ∈ D) ∧ NearM ι p t m (X - u) := by
  choose u hu hu' using h
  choose N hN using hu
  exact ⟨Finset.univ.sup fun q : n × n => N q.1 q.2, Matrix.of u, fun i j => pow_mem_of_le hD
    (Finset.le_sup (f := fun q : n × n => N q.1 q.2) (Finset.mem_univ (i, j))) (hN i j), hu'⟩

def Conj (φ : R →+* R) (S : Subring R) (F F' : Matrix n n R) : Prop :=
  ∃ V ∈ matS S, IsUnit V ∧ F * φ.mapMatrix V = V * F'

theorem Conj.trans {φ : R →+* R} {S : Subring R} {F F' F'' : Matrix n n R}
    (h : Conj φ S F F') (h' : Conj φ S F' F'') : Conj φ S F F'' := by
  obtain ⟨V, h1, h2, h3⟩ := h
  obtain ⟨V', h1', h2', h3'⟩ := h'
  exact ⟨V * V', mul_mem h1 h1', h2.mul h2', by
    rw [map_mul, ← mul_assoc, h3, mul_assoc, h3', mul_assoc]⟩

theorem conj_pow {φ : R →+* R} {S : Subring R} (hφS : ∀ x ∈ S, φ x ∈ S) {F : Matrix n n R}
    (hF : F ∈ matS S) (hu : IsUnit F) (N : ℕ) : Conj φ S F ((φ ^ N).mapMatrix F) := by
  induction N with
  | zero => exact ⟨1, one_mem _, isUnit_one, by rw [map_one, mul_one, one_mul]; rfl⟩
  | succ N ih =>
    refine ih.trans ⟨(φ ^ N).mapMatrix F, fun i j => pow_mem_of_le hφS (Nat.zero_le N) (hF i j),
      hu.map _, ?_⟩
    rw [pow_succ']
    rfl

theorem near_pow {φ : R →+* R} (h3 : ∀ m x, Near ι p t m x → Near ι p t (p * m) (φ x))
    (N m : ℕ) (x : R) (h : Near ι p t m x) : Near ι p t (p ^ N * m) ((φ ^ N) x) := by
  induction N with
  | zero => rw [pow_zero, one_mul]; exact h
  | succ N ih => rw [pow_succ', pow_succ', mul_assoc]; exact h3 _ _ ih

theorem pole_pow {φ : R →+* R} (h3 : ∀ m x, Near ι p t m x → Near ι p t (p * m) (φ x))
    (hφt : (p : R) ∣ t ^ p - φ t) (N K : ℕ) (x : R) (h : Near ι p t 0 (t ^ K * x)) :
    Near ι p t 0 (t ^ (p ^ N * K) * (φ ^ N) x) := by
  induction N with
  | zero => rw [pow_zero, one_mul]; exact h
  | succ N ih =>
    have h1 := h3 _ _ ih
    obtain ⟨r, hr⟩ := hφt.trans (sub_dvd_pow_sub_pow _ _ (p ^ N * K))
    have h2 := h1.add (Near.of_mul (p * 0) (r * φ ((φ ^ N) x)))
    rw [map_mul, map_pow, ← mul_assoc, ← hr, ← add_mul, add_sub_cancel, ← pow_mul,
      ← mul_assoc] at h2
    rw [pow_succ', pow_succ']
    exact h2

theorem map_pow_smul (f : E →+* R) (k : ℕ) (z : Matrix n n E) :
    f.mapMatrix ((p : E) ^ k • z) = (p : R) ^ k • f.mapMatrix z := by
  ext i j
  simp

theorem map_natCast_smul (f : E →+* R) (z : Matrix n n E) :
    f.mapMatrix ((p : E) • z) = (p : R) • f.mapMatrix z := by
  ext i j
  simp

theorem mem_of_pow_smul {S : Subring R} (hsat : ∀ x, (p : R) * x ∈ S → x ∈ S) (k : ℕ)
    (X : Matrix n n R) (h : (p : R) ^ k • X ∈ matS S) : X ∈ matS S := by
  induction k with
  | zero => simpa using h
  | succ k ih =>
    refine ih fun i j => hsat _ ?_
    have := h i j
    rw [pow_succ', mul_smul] at this
    exact this

theorem padic_conj {φ : R →+* R} {io : E →+* R} {S : Subring R} (hφS : ∀ x ∈ S, φ x ∈ S)
    (hioS : ∀ e, io e ∈ S) (hsat : ∀ x, (p : R) * x ∈ S → x ∈ S)
    (hJ : ∀ x : R, IsUnit (1 + (p : R) * x))
    (sep : ∀ x : R, (∀ k : ℕ, (p : R) ^ k ∣ x) → x = 0)
    (compS : ∀ x : ℕ → R, (∀ i, x i ∈ S) → ∃ y ∈ S, ∀ k : ℕ, ∃ r,
      y - ∑ i ∈ Finset.range k, (p : R) ^ i * x i = (p : R) ^ k * r)
    (compE : ∀ x : ℕ → E, ∃ y, ∀ k : ℕ, ∃ r,
      y - ∑ i ∈ Finset.range k, (p : E) ^ i * x i = (p : E) ^ k * r)
    (F : Matrix n n R) (hF : F ∈ matS S) (e : Matrix n n E) (r₀ : Matrix n n R)
    (he : F = io.mapMatrix e + (p : R) • r₀)
    (hL : ∀ y ∈ matS S, ∃ z ∈ matS S, ∃ (d : Matrix n n E) (r : Matrix n n R),
      y + io.mapMatrix e * φ.mapMatrix z - z * io.mapMatrix e = io.mapMatrix d + (p : R) • r) :
    ∃ e', Conj φ S F (io.mapMatrix e') := by
  have hpS : ∀ (k : ℕ), ∀ z ∈ matS S, (p : R) ^ k • z ∈ matS (n := n) S :=
    fun k z hz i j => mul_mem (pow_mem (natCast_mem S p) k) (hz i j)
  let Inv : ℕ → Matrix n n R → Matrix n n E → Prop := fun k V D =>
    V ∈ matS S ∧ ∃ v d ρ, V = 1 + (p : R) • v ∧ D = e + (p : E) • d ∧
      F * φ.mapMatrix V - V * io.mapMatrix D = (p : R) ^ (k + 1) • ρ
  have step : ∀ k V D, ∃ z d', Inv k V D →
      z ∈ matS S ∧ Inv (k + 1) (V + (p : R) ^ (k + 1) • z) (D + (p : E) ^ (k + 1) • d') := by
    intro k V D
    by_cases h : Inv k V D
    swap
    · exact ⟨0, 0, fun h' => absurd h' h⟩
    obtain ⟨hV, v, d, ρ, hv, hd, hρ⟩ := h
    have hρS : ρ ∈ matS S := mem_of_pow_smul hsat (k + 1) _ (hρ ▸ sub_mem
      (mul_mem hF (show φ.mapMatrix V ∈ matS S from fun i j => hφS _ (hV i j)))
      (mul_mem hV (show io.mapMatrix D ∈ matS S from fun i j => hioS _)))
    obtain ⟨z, hz, d', r, hr⟩ := hL ρ hρS
    refine ⟨z, d', fun _ => ⟨hz, add_mem hV (hpS _ _ hz), v + (p : R) ^ k • z,
      d + (p : E) ^ k • d', r + r₀ * φ.mapMatrix z - v * io.mapMatrix d' - z * io.mapMatrix d -
        (p : R) ^ k • (z * io.mapMatrix d'), ?_, ?_, ?_⟩⟩
    · rw [hv]; module
    · rw [hd]; module
    · have h2 : F * φ.mapMatrix z =
          io.mapMatrix e * φ.mapMatrix z + (p : R) • (r₀ * φ.mapMatrix z) := by
        rw [he, add_mul, smul_mul_assoc]
      have h3 : V * io.mapMatrix d' = io.mapMatrix d' + (p : R) • (v * io.mapMatrix d') := by
        rw [hv, add_mul, smul_mul_assoc, one_mul]
      have h4 : z * io.mapMatrix D = z * io.mapMatrix e + (p : R) • (z * io.mapMatrix d) := by
        rw [hd, map_add, map_natCast_smul, mul_add, mul_smul_comm]
      simp only [map_add, map_pow_smul, mul_add, add_mul, mul_smul_comm, smul_mul_assoc]
      linear_combination (norm := module) hρ + (p : R) ^ (k + 1) • hr + (p : R) ^ (k + 1) • h2 -
        (p : R) ^ (k + 1) • h3 - (p : R) ^ (k + 1) • h4
  choose z d hstep using step
  let q : ℕ → Matrix n n R × Matrix n n E := fun k => Nat.rec (1, e) (fun k x =>
    (x.1 + (p : R) ^ (k + 1) • z k x.1 x.2, x.2 + (p : E) ^ (k + 1) • d k x.1 x.2)) k
  have hq : ∀ k, Inv k (q k).1 (q k).2 := by
    intro k
    induction k with
    | zero =>
      refine ⟨one_mem _, 0, 0, r₀, by simp [q], by simp [q], ?_⟩
      change F * φ.mapMatrix 1 - 1 * io.mapMatrix e = _
      rw [map_one, mul_one, one_mul, he, zero_add, pow_one, add_sub_cancel_left]
    | succ k ih => exact (hstep k _ _ ih).2
  have hs : ∀ k, (q k).1 = 1 + (p : R) • ∑ i ∈ Finset.range k, (p : R) ^ i • z i (q i).1 (q i).2 ∧
      (q k).2 = e + (p : E) • ∑ i ∈ Finset.range k, (p : E) ^ i • d i (q i).1 (q i).2 := by
    intro k
    induction k with
    | zero => simp [q]
    | succ k ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ, smul_add, smul_add, ← add_assoc,
        ← add_assoc, ← ih.1, ← ih.2, smul_smul, smul_smul, ← pow_succ', ← pow_succ']
      exact ⟨rfl, rfl⟩
  choose s hsS a ha using fun i j =>
    compS (fun k => z k (q k).1 (q k).2 i j) fun k => (hstep k _ _ (hq k)).1 i j
  choose σ b hb using fun i j => compE fun k => d k (q k).1 (q k).2 i j
  have ha' : ∀ k, 1 + (p : R) • Matrix.of s =
      (q k).1 + (p : R) ^ (k + 1) • Matrix.of fun i j => a i j k := fun k => by
    have : Matrix.of s - ∑ i ∈ Finset.range k, (p : R) ^ i • z i (q i).1 (q i).2 =
        (p : R) ^ k • Matrix.of fun i j => a i j k := Matrix.ext fun i j => by
      rw [Matrix.sub_apply, Matrix.sum_apply]; exact ha i j k
    linear_combination (norm := module) (p : R) • this - (hs k).1
  have hb' : ∀ k, e + (p : E) • Matrix.of σ =
      (q k).2 + (p : E) ^ (k + 1) • Matrix.of fun i j => b i j k := fun k => by
    have : Matrix.of σ - ∑ i ∈ Finset.range k, (p : E) ^ i • d i (q i).1 (q i).2 =
        (p : E) ^ k • Matrix.of fun i j => b i j k := Matrix.ext fun i j => by
      rw [Matrix.sub_apply, Matrix.sum_apply]; exact hb i j k
    linear_combination (norm := module) (p : E) • this - (hs k).2
  refine ⟨e + (p : E) • Matrix.of σ, 1 + (p : R) • Matrix.of s,
    add_mem (one_mem _) (by simpa using hpS 1 (Matrix.of s) hsS),
    isUnit_of_mul_eq hJ (mul_one _), ?_⟩
  rw [← sub_eq_zero]
  refine Matrix.ext fun i j => sep _ fun k => ?_
  obtain ⟨-, -, -, ρ, -, -, hρ⟩ := hq k
  rw [ha' k, hb' k]
  generalize (Matrix.of fun i j => a i j k) = a'
  generalize (Matrix.of fun i j => b i j k) = b'
  have : F * φ.mapMatrix ((q k).1 + (p : R) ^ (k + 1) • a') - ((q k).1 + (p : R) ^ (k + 1) • a') *
      io.mapMatrix ((q k).2 + (p : E) ^ (k + 1) • b') = (p : R) ^ k • (p : R) •
        (ρ + F * φ.mapMatrix a' - (q k).1 * io.mapMatrix b' - a' * io.mapMatrix (q k).2 -
          (p : R) ^ (k + 1) • (a' * io.mapMatrix b')) := by
    simp only [map_add, map_pow_smul, mul_add, add_mul, mul_smul_comm, smul_mul_assoc]
    linear_combination (norm := module) hρ
  rw [this]
  exact ⟨_, rfl⟩

variable {τ : A} (hτ : ι τ = t) (ht : IsUnit t) (hp : 2 ≤ p) {φ : R →+* R}
  (h3 : ∀ m x, Near ι p t m x → Near ι p t (p * m) (φ x)) {S : Subring R}
  (meet : ∀ x, (∀ m, Near ι p t m x) → ∃ r, x = (p : R) * r)
  (comp : ∀ (k : ℕ) (f : ℕ → R), (∀ i, f i ∈ S) → (∀ i, Near ι p t (i + k) (f i)) →
    ∃ x ∈ S, ∀ m, Near ι p t (m + k) (x - ∑ i ∈ Finset.range m, f i))
  (hφS : ∀ x ∈ S, φ x ∈ S) {io : E →+* R} (hioS : ∀ e, io e ∈ S)
  (hD : ∀ x ∈ modSub io p, φ x ∈ modSub io p)
  (hpole : ∀ x, ∃ k, Near ι p t 0 (t ^ k * x))
  (h2 : ∀ x ∈ S, ∀ m, ∃ u ∈ perfSub φ (modSub io p) hD, Near ι p t m (x - u))

include hτ hpole in
omit [DecidableEq n] in
theorem exists_pole₂ (F G : Matrix n n R) :
    ∃ K, NearM ι p t 0 (t ^ K • F) ∧ NearM ι p t 0 (t ^ K • G) := by
  obtain ⟨K₁, h₁⟩ := exists_pole hτ F fun i j => hpole _
  obtain ⟨K₂, h₂⟩ := exists_pole hτ G fun i j => hpole _
  exact ⟨max K₁ K₂, h₁ _ (le_max_left _ _), h₂ _ (le_max_right _ _)⟩

include hτ ht hp h3 meet comp hφS hioS hpole h2 in

theorem onto_mod (a b : Matrix n n E) (y : Matrix n n R) (hy : y ∈ matS S) :
    ∃ z ∈ matS S, y - (z - opT φ (io.mapMatrix a) (io.mapMatrix b) z) ∈ matS (modSub io p) := by
  obtain ⟨K, ha, hb⟩ := exists_pole₂ hτ hpole (io.mapMatrix a) (io.mapMatrix b)
  have hT := near_opT hτ ht hp h3 ha hb
  have hTS := opT_mem hφS (show io.mapMatrix a ∈ matS S from fun i j => hioS _)
    (show io.mapMatrix b ∈ matS S from fun i j => hioS _)
  obtain ⟨N, u, hN, hu⟩ := exists_approx (X := y) fun i j => h2 _ (hy i j) (2 * K + 1)
  induction N generalizing y u with
  | zero =>
    obtain ⟨e, r, her⟩ := exists_of_mem_modSub (X := u) hN
    have h : NearM ι p t (2 * K + 1) (y - io.mapMatrix e) := by
      have := hu.add (NearM.of_smul _ r)
      rw [her] at this
      convert this using 1
      abel
    obtain ⟨z, hzS, -, r', hr'⟩ := contract hτ meet comp _ _ hT hTS _
      (sub_mem hy (show io.mapMatrix e ∈ matS S from fun i j => hioS _)) h
    refine ⟨z, hzS, ?_⟩
    have : y - (z - opT φ (io.mapMatrix a) (io.mapMatrix b) z) =
        io.mapMatrix e + (p : R) • (-r') := by
      linear_combination (norm := module) -hr'
    rw [this]
    exact fun i j => ⟨e i j, -r' i j, rfl⟩
  | succ N ih =>
    have h : (φ ^ N).mapMatrix (opT φ (io.mapMatrix a) (io.mapMatrix b) u) ∈
        matS (modSub io p) := by
      rw [opT_apply, map_mul, map_mul]
      exact mul_mem (mul_mem (fun i j => pow_mem_of_le hD (Nat.zero_le N) (io_mem io p _)) hN)
        fun i j => pow_mem_of_le hD (Nat.zero_le N) (io_mem io p _)
    obtain ⟨z, hz, h'⟩ := ih _ (hTS y hy) _ h (by
      rw [← map_sub]
      exact (hT 0 _ (by rw [zero_add]; exact hu)).mono hτ (by omega))
    refine ⟨y + z, add_mem hy hz, ?_⟩
    rw [map_add]
    convert h' using 1
    abel

include hτ ht hp h3 meet comp hφS hioS hpole h2 in

theorem conj_mod (hφt : (p : R) ∣ t ^ p - φ t) (hJ : ∀ x : R, IsUnit (1 + (p : R) * x))
    (hinv : ∀ X Y : Matrix n n R, X ∈ matS S → X * Y = 1 → Y ∈ matS S)
    (F : Matrix n n R) (hF : F ∈ matS S) (hu : IsUnit F) :
    ∃ F' ∈ matS S, IsUnit F' ∧ Conj φ S F F' ∧
      ∃ (e : Matrix n n E) (r : Matrix n n R), F' = io.mapMatrix e + (p : R) • r := by
  obtain ⟨G, hG⟩ := hu.exists_right_inv
  have hGS := hinv F G hF hG
  obtain ⟨K, hKF, hKG⟩ := exists_pole₂ hτ hpole F G
  obtain ⟨N, u, hN, hu'⟩ := exists_approx (X := F) fun i j => h2 _ (hF i j) (3 * K + 1)
  obtain ⟨e, r, her⟩ := exists_of_mem_modSub (X := (φ ^ N).mapMatrix u) hN
  have hδ : NearM ι p t (p ^ N * (3 * K + 1)) ((φ ^ N).mapMatrix F - io.mapMatrix e) := by
    have h : NearM ι p t (p ^ N * (3 * K + 1)) ((φ ^ N).mapMatrix (F - u)) :=
      fun i j => near_pow h3 N _ _ (hu' i j)
    have := h.add (NearM.of_smul _ r)
    rw [map_sub, her] at this
    convert this using 1
    abel
  have hF1 : NearM ι p t 0 (t ^ (p ^ N * K) • (φ ^ N).mapMatrix F) :=
    fun i j => pole_pow h3 hφt N K _ (hKF i j)
  have hG1 : NearM ι p t 0 (t ^ (p ^ N * K) • (φ ^ N).mapMatrix G) :=
    fun i j => pole_pow h3 hφt N K _ (hKG i j)
  have hF1S : (φ ^ N).mapMatrix F ∈ matS S :=
    fun i j => pow_mem_of_le hφS (Nat.zero_le N) (hF i j)
  have hG1S : (φ ^ N).mapMatrix G ∈ matS S :=
    fun i j => pow_mem_of_le hφS (Nat.zero_le N) (hGS i j)
  have hGF : (φ ^ N).mapMatrix G * (φ ^ N).mapMatrix F = 1 := by
    rw [← map_mul, mul_eq_one_comm.1 hG, map_one]
  have hc := conj_pow hφS hF hu N
  have hu1 := hu.map (φ ^ N).mapMatrix
  have hBS : io.mapMatrix e ∈ matS S := fun i j => hioS _
  generalize (φ ^ N).mapMatrix F = F₁ at *
  generalize (φ ^ N).mapMatrix G = G₁ at *
  have hB : NearM ι p t 0 (t ^ (p ^ N * K) • io.mapMatrix e) := by
    have := hF1.sub ((hδ.mono hτ (Nat.zero_le _)).smul hτ (p ^ N * K))
    rwa [← smul_sub, sub_sub_cancel] at this
  have hy : NearM ι p t (2 * (p ^ N * K) + 1) (-((F₁ - io.mapMatrix e) * G₁)) := by
    refine NearM.neg (NearM.cancel ht (k := p ^ N * K) ?_)
    rw [← mul_smul_comm]
    have : 0 < p ^ N := pow_pos (by omega) N
    exact (hδ.mul hG1).mono hτ (by nlinarith)
  obtain ⟨z, hzS, hz, r₁, hr₁⟩ := contract hτ meet comp _ _ (near_opT hτ ht hp h3 hB hG1)
    (opT_mem hφS hBS hG1S) _ (neg_mem (mul_mem (sub_mem hF1S hBS) hG1S)) hy
  obtain ⟨W, -, -, r₂, hr₂⟩ := contract hτ meet comp (AddMonoidHom.mulLeft (-z)) 0
    (fun k X hX => (hz.neg.mul hX).mono hτ (by omega))
    (fun X hX => mul_mem (neg_mem hzS) hX) 1 (one_mem _) NearM.one
  have hU : IsUnit (1 + z) := isUnit_of_mul_eq hJ (Y := W) (r := r₂) (by
    rw [AddMonoidHom.coe_mulLeft, neg_mul] at hr₂
    rw [add_mul, one_mul]
    linear_combination (norm := abel) hr₂)
  obtain ⟨V, hV⟩ := hU.exists_right_inv
  have hVU := mul_eq_one_comm.1 hV
  have hUS : 1 + z ∈ matS S := add_mem (one_mem _) hzS
  have hVS := hinv _ _ hUS hV
  have hVu : IsUnit V := isUnit_iff_exists.2 ⟨_, hVU, hV⟩
  have key : (1 + z) * F₁ = io.mapMatrix e * φ.mapMatrix (1 + z) + (p : R) • (r₁ * F₁) := by
    have := congrArg (· * F₁) hr₁
    simp only [add_mul, neg_mul, opT_apply, mul_assoc, hGF, mul_one, smul_mul_assoc] at this
    rw [map_add, map_one, mul_add, mul_one, add_mul, one_mul, this]
    abel
  refine ⟨(1 + z) * F₁ * φ.mapMatrix V, mul_mem (mul_mem hUS hF1S)
    (show φ.mapMatrix V ∈ matS S from fun i j => hφS _ (hVS i j)),
    (hU.mul hu1).mul (hVu.map _), hc.trans ⟨V, hVS, hVu, ?_⟩, e, r₁ * F₁ * φ.mapMatrix V, ?_⟩
  · rw [← mul_assoc, ← mul_assoc, hVU, one_mul]
  · rw [key, add_mul, mul_assoc (io.mapMatrix e), ← map_mul, hV, map_one, mul_one, smul_mul_assoc]

include hτ ht hp h3 meet comp hφS hioS hpole h2 in

theorem conj_io (hφt : (p : R) ∣ t ^ p - φ t) (hJ : ∀ x : R, IsUnit (1 + (p : R) * x))
    (hinv : ∀ X Y : Matrix n n R, X ∈ matS S → X * Y = 1 → Y ∈ matS S)
    (hsat : ∀ x, (p : R) * x ∈ S → x ∈ S)
    (sep : ∀ x : R, (∀ k : ℕ, (p : R) ^ k ∣ x) → x = 0)
    (compS : ∀ x : ℕ → R, (∀ i, x i ∈ S) → ∃ y ∈ S, ∀ k : ℕ, ∃ r,
      y - ∑ i ∈ Finset.range k, (p : R) ^ i * x i = (p : R) ^ k * r)
    (compE : ∀ x : ℕ → E, ∃ y, ∀ k : ℕ, ∃ r,
      y - ∑ i ∈ Finset.range k, (p : E) ^ i * x i = (p : E) ^ k * r)
    (hrefl : ∀ e, IsUnit (io e) → IsUnit e)
    (F : Matrix n n R) (hF : F ∈ matS S) (hu : IsUnit F) :
    ∃ e, Conj φ S F (io.mapMatrix e) := by
  obtain ⟨F', hF', hu', hc, e, r, he⟩ :=
    conj_mod hτ ht hp h3 meet comp hφS hioS hD hpole h2 hφt hJ hinv F hF hu
  obtain ⟨G, hG⟩ := hu'.exists_right_inv
  have hB : IsUnit (io.mapMatrix e) := isUnit_of_mul_eq hJ (Y := G) (r := -(r * G)) (by
    rw [← hG, he, add_mul, smul_mul_assoc, smul_neg, add_neg_cancel_right])
  have hue : IsUnit e := by
    rw [Matrix.isUnit_iff_isUnit_det] at hB ⊢
    exact hrefl _ (by rwa [RingHom.map_det])
  obtain ⟨e', he'⟩ := hue.exists_left_inv
  have hBB : io.mapMatrix e' * io.mapMatrix e = 1 := by rw [← map_mul, he', map_one]
  obtain ⟨e'', h⟩ := padic_conj hφS hioS hsat hJ sep compS compE F' hF' e r he fun y hy => by
    obtain ⟨z, hz, h⟩ := onto_mod hτ ht hp h3 meet comp hφS hioS hD hpole h2 e e' _
      (mul_mem hy (show io.mapMatrix e' ∈ matS S from fun i j => hioS _))
    obtain ⟨d, r', hd⟩ := exists_of_mem_modSub h
    refine ⟨z, hz, d * e, r' * io.mapMatrix e, ?_⟩
    have := congrArg (· * io.mapMatrix e) hd
    simp only [add_mul, sub_mul, opT_apply, mul_assoc, hBB, mul_one, smul_mul_assoc] at this
    rw [map_mul, ← this]
    abel
  exact ⟨e'', hc.trans h⟩

theorem series_of_precomplete [IsPrecomplete (Ideal.span {(p : E)}) E] (x : ℕ → E) :
    ∃ y, ∀ k : ℕ, ∃ r, y - ∑ i ∈ Finset.range k, (p : E) ^ i * x i = (p : E) ^ k * r := by
  have hI : ∀ (k : ℕ) (a b : E), a ≡ b [SMOD (Ideal.span {(p : E)} ^ k • ⊤ : Submodule E E)] ↔
      (p : E) ^ k ∣ a - b := by
    intro k a b
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton]
  obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := Ideal.span {(p : E)})
    (fun k => ∑ i ∈ Finset.range k, (p : E) ^ i * x i) (fun {m k} hmk => by
      rw [hI, ← dvd_neg, neg_sub, ← Finset.sum_Ico_eq_sub _ hmk]
      exact Finset.dvd_sum fun i hi => (pow_dvd_pow _ (Finset.mem_Ico.1 hi).1).mul_right _)
  exact ⟨L, fun k => by
    have := (hI k _ _).1 (hL k)
    rwa [← dvd_neg, neg_sub] at this⟩

theorem isUnit_one_add [IsAdicComplete (Ideal.span {(p : R)}) R] (x : R) :
    IsUnit (1 + (p : R) * x) := by
  rw [add_comm]
  exact Ideal.mem_jacobson_bot.1
    (IsAdicComplete.le_jacobson_bot _ (Ideal.mem_span_singleton_self (p : R))) x

theorem map_eq_of_mul_eq_one (g : R →+* R) {X Y : Matrix n n R} (hX : ∀ i j, g (X i j) = X i j)
    (h : X * Y = 1) (i j : n) : g (Y i j) = Y i j := by
  have h1 : g.mapMatrix X = X := Matrix.ext hX
  have h2 : X * g.mapMatrix Y = 1 := by rw [← h1, ← map_mul, h, map_one]
  have h3 : g.mapMatrix Y = Y := (left_inv_eq_right_inv (mul_eq_one_comm.1 h) h2).symm
  exact congrFun (congrFun h3 i) j

theorem dvd_pow_sub (hp : p.Prime) {t y : R} (h : y = (t + 1) ^ p - 1) : (p : R) ∣ t ^ p - y := by
  obtain ⟨r, hr⟩ := exists_add_pow_prime_eq hp t 1
  exact ⟨-(t * r), by rw [h, hr]; ring⟩

end Abstract

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n s : ℕ}
    {Γ : WGam PD LL O v n s} {R : WSer Γ} {RA RW : Type} [CommRing RA] [CommRing RW] [Algebra O RA]
    [Algebra O RW] {inclR : RA →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : RA}
    (I : WIo R RA RW inclR φR gR πA)

theorem io_fixed (g : G) (hg : Γ.resΓ g = 1) (e : R.EE) : gR g (I.ioE e) = I.ioE e := by
  rw [← I.ioE_γ, hg, map_one, AlgHom.one_apply]

theorem io_pi : I.ioE (algebraMap (LetA O n) R.EE letπ) = inclR πA := by
  rw [I.ioE_ext, I.io_π]

include I in
theorem isUnit_pi : IsUnit (inclR πA) := io_pi I ▸ R.EE_π.map I.ioE

include I in
theorem frob_pi {p : ℕ} (hp : PD.p = p) : φR (inclR πA) = (inclR πA + 1) ^ p - 1 := by
  have h : letφ (n := n) R.φ₀ letπ = (letπ + 1) ^ PD.p - 1 := by
    funext i
    change R.φ₀ PowerSeries.X = (PowerSeries.X + 1) ^ PD.p - 1
    rw [R.φ₀_X, R.q₀_def, add_comm]
  rw [← io_pi I, ← I.ioE_φ, R.φE_ext, h, hp]
  simp only [map_sub, map_pow, map_add, map_one]

theorem series_EE (R : WSer Γ) {p : ℕ} (hp : PD.p = p) (x : ℕ → R.EE) :
    ∃ y, ∀ k : ℕ, ∃ r, y - ∑ i ∈ Finset.range k, (p : R.EE) ^ i * x i = (p : R.EE) ^ k * r := by
  subst hp
  haveI := R.EE_complete
  exact series_of_precomplete x

theorem stable_io (p : ℕ) : ∀ x ∈ modSub (I.ioE : R.EE →+* RW) p,
    (φR : RW →+* RW) x ∈ modSub (I.ioE : R.EE →+* RW) p := modSub_stable p I.ioE_φ

def perfI (p : ℕ) : Subring RW :=
  perfSub (φR : RW →+* RW) (modSub (I.ioE : R.EE →+* RW) p) (stable_io I p)

theorem ioE_mem_perfI (p : ℕ) (e : R.EE) : I.ioE e ∈ perfI I p :=
  ⟨0, io_mem (I.ioE : R.EE →+* RW) p e⟩

theorem algebraMap_mem_perfI (p : ℕ) (o : O) : algebraMap O RW o ∈ perfI I p :=
  I.ioE.commutes o ▸ ioE_mem_perfI I p _

theorem mem_perfI_of_io (p : ℕ) {a : LetA O n} {b : RA} (h : I.io a = b) :
    inclR b ∈ perfI I p := h ▸ I.ioE_ext a ▸ ioE_mem_perfI I p _

theorem exists_inv_perfI (p : ℕ) : ∃ u ∈ perfI I p, inclR πA * u = 1 := by
  obtain ⟨u, hu⟩ := R.EE_π.exists_right_inv
  exact ⟨I.ioE u, ioE_mem_perfI I p u, by rw [← io_pi I, ← map_mul, hu, map_one]⟩

theorem mem_perfI_of_iterate (p N k : ℕ) (x : RW) (hx : φR^[N] x = (inclR πA + 1) ^ k) :
    x ∈ perfI I p := by
  refine ⟨N, ?_⟩
  rw [RingHom.coe_pow]
  change φR^[N] x ∈ _
  rw [hx, ← io_pi I]
  exact pow_mem (add_mem (io_mem (I.ioE : R.EE →+* RW) p _) (one_mem _)) k

end Generic

end GlobalTheory.HWL.MatDecompl
